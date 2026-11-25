//! A fast reader for the `<sheetData>` of a worksheet part.
//!
//! The general reader ([`craft_xml::Options::parse_streaming_partial`]) builds a tree for every
//! `<row>` with namespace resolution, owned names and owned attribute values, which is most of the
//! time a large sheet takes to read. This reader scans the rows of `<sheetData>` directly into
//! [`Row`]s, borrowing names and values from the part, and hands the rest of the part (everything
//! but the rows) to the general reader.
//!
//! It reads only a plain subset of XML: no comments, processing instructions or CDATA inside the
//! sheet data, no namespace declarations below the root, prefixes only where the canonical name
//! is the name as written, references only to predefined and numeric entities. Whatever is
//! outside that subset, malformed, or past a size limit makes it stop and say how many rows it
//! has handed out; the caller then reads the part with the general reader, skipping that many
//! rows. The rows both readers hand out are the same, since both convert with
//! [`RowReader::row_from`].

use std::borrow::Cow;

use craft_xml::{El, Node, Options};

use crate::ns::{CANONICAL, MAIN, MAIN_STRICT};
use crate::sheet::{AttrList, CellIn, Row, RowReader};

/// Tokens in one row past which the general reader takes over, whatever the limits allow.
const MAX_ROW_NODES: usize = 100_000;
/// Attributes on one start tag past which the general reader takes over.
const MAX_TAG_ATTRS: usize = 256;
/// Nesting below a `<c>` past which the general reader takes over.
const MAX_DEPTH: usize = 32;
/// Levels above the content of a `<c>`: the root, `<sheetData>`, `<row>` and `<c>`.
const CELL_DEPTH: usize = 4;

/// What one row may hold before the general reader takes over: well inside the limits the general
/// reader holds a row to, so a row near them gets the general reader's own answer. Every token
/// counts as a node (more than the tree keeps), and so does every token before the sheet data,
/// which may still be in the tree when a row is read.
#[derive(Clone, Copy)]
struct Budget {
    nodes: usize,
    elements: usize,
    attrs: usize,
    tag_attrs: usize,
    /// Deepest element allowed, counted from the root as 1, one level short of the limit.
    depth: usize,
}

impl Budget {
    fn new(limits: &craft_xml::Limits, before: &Budget) -> Budget {
        // `before` holds what the part had used before the sheet data; two more for `<sheetData>`
        // and the blank text between rows.
        let left = |limit: usize, used: usize| limit.saturating_sub(used.saturating_add(2)).min(MAX_ROW_NODES);
        Budget {
            nodes: left(limits.max_nodes, before.nodes),
            elements: left(limits.max_elements, before.elements),
            attrs: left(limits.max_attrs_total, before.attrs),
            tag_attrs: limits.max_attrs.min(MAX_TAG_ATTRS),
            depth: limits.max_depth.saturating_sub(1).min(MAX_DEPTH + CELL_DEPTH),
        }
    }
    fn unlimited() -> Budget {
        Budget { nodes: usize::MAX, elements: usize::MAX, attrs: usize::MAX, tag_attrs: MAX_TAG_ATTRS, depth: usize::MAX }
    }
}

/// Why the fast read stopped.
pub(crate) enum Stop<E> {
    /// `each` failed: the read ends with its error.
    Caller(E),
    /// The part needs the general reader, which skips the rows already handed out.
    Fallback { emitted: u64 },
}

/// What the fast read produced: the part without its rows, read by the general reader, and the
/// row counts.
pub(crate) struct Read {
    pub(crate) root: El,
    pub(crate) rows: RowReader,
}

/// Bails out of the fast read.
struct Bail;

type R<T> = Result<T, Bail>;

/// Borrowed attributes: names as written, values with references resolved.
type Attrs<'x> = Vec<(&'x str, Cow<'x, str>)>;

impl AttrList for Attrs<'_> {
    fn get(&self, name: &str) -> Option<&str> {
        self.iter().find(|(k, _)| *k == name).map(|(_, v)| v.as_ref())
    }
    fn owned_except(&self, skip: &[&str]) -> Vec<(String, String)> {
        self.iter().filter(|(k, _)| !skip.contains(k)).map(|(k, v)| ((*k).to_string(), v.to_string())).collect()
    }
}

/// Reads the rows of `bytes` (a worksheet part) with `each`; see the module documentation.
/// Bytes read from the part at a time.
pub(crate) const CHUNK: usize = 1 << 20;
/// The most of the part kept before `<sheetData>` while looking for it.
const MAX_HEAD_BYTES: usize = 64 << 20;
/// The longest stretch one row (or the blank text between two) may take in the window.
const MAX_ROW_BYTES: usize = 16 << 20;
/// How close to the end of the window a failure must be to count as the window being too short
/// rather than the markup being unreadable: no token but text (read up to the next `<`) is longer.
const TOKEN_SLACK: usize = 64 << 10;

/// The part as read so far: a window over it that holds the rows being read and nothing before.
struct Window<'s> {
    src: &'s mut dyn std::io::Read,
    buf: Vec<u8>,
    /// Where the unread part of `buf` starts.
    pos: usize,
    eof: bool,
    /// Bytes read from `src`.
    read: u64,
    chunk: usize,
}

impl Window<'_> {
    /// Appends up to one chunk. A read error ends the fast read (the general reader reports it).
    fn fill(&mut self) -> R<()> {
        if self.eof {
            return Ok(());
        }
        let len = self.buf.len();
        self.buf.resize(len + self.chunk, 0);
        let mut got = 0;
        // A short read is not the end: only a read of nothing is.
        while got < self.chunk {
            let Some(dst) = self.buf.get_mut(len + got..) else { break };
            match self.src.read(dst) {
                Ok(0) => {
                    self.eof = true;
                    break;
                }
                Ok(n) => got += n,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(_) => {
                    self.buf.truncate(len + got);
                    return Err(Bail);
                }
            }
        }
        self.buf.truncate(len + got);
        self.read = self.read.saturating_add(got as u64);
        Ok(())
    }

    /// Drops what lies before `pos`.
    fn compact(&mut self) {
        self.buf.drain(..self.pos);
        self.pos = 0;
    }

    /// The unread bytes as text, up to the last whole character. Bytes that are not UTF-8 end
    /// the fast read (the general reader decodes them leniently).
    fn text(&self) -> R<&str> {
        let bytes = self.buf.get(self.pos..).ok_or(Bail)?;
        match std::str::from_utf8(bytes) {
            Ok(t) => Ok(t),
            Err(e) if e.error_len().is_none() && !self.eof => bytes.get(..e.valid_up_to()).and_then(|b| std::str::from_utf8(b).ok()).ok_or(Bail),
            Err(_) => Err(Bail),
        }
    }
}

/// What the fast read of a whole part produced, and the bytes it read.
pub(crate) struct Streamed {
    pub(crate) read: Read,
    pub(crate) bytes: u64,
}

/// Reads the rows of the worksheet part that `src` streams (`declared` bytes at most) with
/// `each`, holding only a window of the part at a time; see the module documentation.
pub(crate) fn read_stream<E>(
    src: &mut dyn std::io::Read,
    declared: u64,
    opts: &Options<'_>,
    each: &mut dyn FnMut(Row) -> Result<(), E>,
    chunk: usize,
) -> Result<Streamed, Stop<E>> {
    let fallback = |emitted| Stop::Fallback { emitted };
    // The general reader refuses a part over the input limit before it reads a row.
    if usize::try_from(declared).map_or(true, |d| d > opts.limits.max_input) {
        return Err(fallback(0));
    }
    let mut w = Window { src, buf: Vec::new(), pos: 0, eof: false, read: 0, chunk: chunk.max(1) };
    // The head: up to the `<sheetData>` start tag, read whole.
    let (before, prefixes, root, used) = loop {
        if w.fill().is_err() {
            return Err(fallback(0));
        }
        if w.buf.len() >= 4 || w.eof {
            // A byte-order mark is skipped; UTF-16 is the general reader's.
            match craft_xml::to_utf8(&w.buf) {
                Cow::Borrowed(b) => w.pos = w.buf.len() - b.len(),
                Cow::Owned(_) => return Err(fallback(0)),
            }
            let found = w.text().ok().and_then(|t| head(t).ok().map(|h| (t, h)));
            if let Some((t, h)) = found {
                let before = t.get(..h.data_start).ok_or(Bail).map(str::to_string);
                let Ok(before) = before else { return Err(fallback(0)) };
                let prefixes: Vec<String> = h.prefixes.iter().map(|p| (*p).to_string()).collect();
                let root = h.root.to_string();
                let used = h.used;
                w.pos += h.data_start;
                break (before, prefixes, root, used);
            }
            w.pos = 0;
        }
        if w.eof || w.buf.len() > MAX_HEAD_BYTES {
            return Err(fallback(0));
        }
    };
    let prefixes: Vec<&str> = prefixes.iter().map(String::as_str).collect();
    // What comes before the rows must read without error before any row is handed out: the
    // general reader would stop there and hand out none.
    let probe = format!("{before}</sheetData></{root}>");
    let mut stray = false;
    let (probed, err) = opts.parse_streaming_partial(probe.as_bytes(), &["row"], |_| {
        stray = true;
        Ok::<(), craft_xml::Error>(())
    });
    if probed.is_none() || err.is_some() || stray {
        return Err(fallback(0));
    }
    w.compact();
    let budget = Budget::new(&opts.limits, &used);
    let mut rows = RowReader::default();
    let mut emitted = 0u64;
    let mut blank = String::new();
    // The rows, up to `</sheetData>`, a window at a time.
    loop {
        let Ok(text) = w.text() else { return Err(fallback(emitted)) };
        // The root and `<sheetData>` are open.
        let mut lx = Lexer { s: text, at: 0, left: budget, open: 2 };
        let mut scratch = Scratch::default();
        // `Ok(at)`: `</sheetData>` starts at `at`. `Err(at)`: the token or row at `at` needs more.
        let stop: Result<usize, usize> = loop {
            let start = lx.at;
            match lx.next(&prefixes) {
                Ok(Tok::Text(t)) => {
                    if lx.at == text.len() && !w.eof {
                        break Err(start);
                    }
                    // Only blank text between rows: it stays in the tree as one text node.
                    if !t.bytes().all(|b| matches!(b, b' ' | b'\t' | b'\n')) {
                        return Err(fallback(emitted));
                    }
                    blank.push_str(t);
                }
                Ok(Tok::End { name: "sheetData", start }) => break Ok(start),
                Ok(Tok::Start { name: "row", attrs, empty }) => {
                    lx.left = budget;
                    match read_row(&mut lx, &prefixes, attrs, empty, &mut scratch, &mut rows) {
                        Ok(row) => {
                            if let Some(row) = row {
                                each(row).map_err(Stop::Caller)?;
                                emitted += 1;
                            }
                        }
                        Err(Bail) => break Err(start),
                    }
                }
                Ok(_) => return Err(fallback(emitted)),
                Err(Bail) => break Err(start),
            }
        };
        let consumed = match stop {
            Ok(at) => {
                w.pos += at;
                break;
            }
            Err(at) => {
                // A failure well inside the window is the markup, not the window's end.
                let near_end = lx.at.saturating_add(TOKEN_SLACK) >= text.len();
                if w.eof || !near_end || text.len() - at > MAX_ROW_BYTES {
                    return Err(fallback(emitted));
                }
                at
            }
        };
        w.pos += consumed;
        w.compact();
        if w.fill().is_err() {
            return Err(fallback(emitted));
        }
    }
    // The rest of the part, from `</sheetData>`, read whole.
    w.compact();
    while !w.eof {
        if w.fill().is_err() {
            return Err(fallback(emitted));
        }
    }
    let Ok(after) = std::str::from_utf8(&w.buf) else { return Err(fallback(emitted)) };
    // Everything but the rows, for the general reader: the part with an empty `<sheetData>`
    // holding the blank text that stood between the rows.
    let rest = [before.as_str(), &blank, after].concat();
    let mut stray = false;
    let (root, err) = opts.parse_streaming_partial(rest.as_bytes(), &["row"], |_| {
        stray = true;
        Ok::<(), craft_xml::Error>(())
    });
    match (root, err) {
        (Some(root), None) if !stray => Ok(Streamed { read: Read { root, rows }, bytes: w.read }),
        _ => Err(fallback(emitted)),
    }
}

/// Where the sheet data starts, and the prefixes it may use.
struct Head<'x> {
    /// Just after the `<sheetData …>` start tag.
    data_start: usize,
    /// Prefixes the root declares whose canonical prefix is the prefix itself.
    prefixes: Vec<&'x str>,
    /// Tokens, start tags and attributes before the sheet data.
    used: Budget,
    /// The root element's name.
    root: &'x str,
}

/// Finds `<sheetData>` as a child of the root, checking that what comes before it is plain
/// markup with no `<row>` and that the root's namespaces read as written.
fn head(s: &str) -> R<Head<'_>> {
    let mut lx = Lexer { s, at: 0, left: Budget::unlimited(), open: 0 };
    // An XML declaration, then the root.
    let mut prefixes = Vec::new();
    let rest = s.trim_start_matches([' ', '\t', '\r', '\n']);
    lx.at = s.len() - rest.len();
    if rest.starts_with("<?xml") {
        let end = rest.find("?>").ok_or(Bail)?;
        lx.at += end + 2;
    }
    let mut depth = 0usize;
    let mut first = true;
    let mut root = "";
    loop {
        // Any name is allowed before the sheet data: only its nesting matters here.
        let tok = lx.next_any()?;
        lx.count(&tok)?;
        match tok {
            Tok::Text(t) => {
                if first && !t.trim().is_empty() {
                    return Err(Bail);
                }
            }
            Tok::Start { name, attrs, empty } => {
                if first {
                    first = false;
                    root = name;
                    for (k, v) in &attrs {
                        if *k == "xmlns" {
                            if v != MAIN && v != MAIN_STRICT {
                                return Err(Bail);
                            }
                        } else if let Some(p) = k.strip_prefix("xmlns:")
                            && CANONICAL.prefix(v) == p
                            && p != "mc"
                        {
                            prefixes.push(p);
                        }
                    }
                } else if attrs.iter().any(|(k, _)| is_ns_decl(k)) || name == "row" {
                    return Err(Bail);
                }
                if name == "sheetData" && depth == 1 {
                    let used = Budget::unlimited();
                    let used = Budget {
                        nodes: used.nodes - lx.left.nodes,
                        elements: used.elements - lx.left.elements,
                        attrs: used.attrs - lx.left.attrs,
                        ..used
                    };
                    return if empty { Err(Bail) } else { Ok(Head { data_start: lx.at, prefixes, used, root }) };
                }
                if !empty {
                    depth += 1;
                }
            }
            Tok::End { .. } => {
                depth = depth.checked_sub(1).ok_or(Bail)?;
                if depth == 0 {
                    return Err(Bail);
                }
            }
        }
    }
}

fn is_ns_decl(k: &str) -> bool {
    k == "xmlns" || k.starts_with("xmlns:")
}

/// Per-row buffers, kept between rows.
#[derive(Default)]
struct Scratch<'x> {
    cells: Vec<CellParts<'x>>,
    inline: Vec<El>,
}

struct CellParts<'x> {
    attrs: Attrs<'x>,
    v: Option<Cow<'x, str>>,
    f: Option<(Attrs<'x>, Cow<'x, str>)>,
    /// Index into [`Scratch::inline`].
    is: Option<usize>,
}

fn read_row<'x>(
    lx: &mut Lexer<'x>,
    prefixes: &[&str],
    attrs: Attrs<'x>,
    empty: bool,
    scratch: &mut Scratch<'x>,
    rows: &mut RowReader,
) -> R<Option<Row>> {
    scratch.cells.clear();
    scratch.inline.clear();
    if !empty {
        loop {
            match lx.next(prefixes)? {
                Tok::Text(_) => {}
                Tok::End { name: "row", .. } => break,
                Tok::End { .. } => return Err(Bail),
                Tok::Start { name: "c", attrs, empty } => {
                    let cell = read_cell(lx, prefixes, attrs, empty, &mut scratch.inline)?;
                    scratch.cells.push(cell);
                }
                Tok::Start { name, empty, .. } => {
                    if !empty {
                        lx.skip(prefixes, name, 1)?;
                    }
                }
            }
        }
    }
    let inline = &scratch.inline;
    let cells: Vec<CellIn<'_>> = scratch
        .cells
        .iter()
        .map(|c| CellIn {
            attrs: &c.attrs,
            v: c.v.as_ref().map(|v| Cow::Borrowed(v.as_ref())),
            f: c.f.as_ref().map(|(a, t)| (a as &dyn AttrList, Cow::Borrowed(t.as_ref()))),
            is: c.is.and_then(|i| inline.get(i)),
        })
        .collect();
    Ok(rows.row_from(&attrs, cells))
}

fn read_cell<'x>(lx: &mut Lexer<'x>, prefixes: &[&str], attrs: Attrs<'x>, empty: bool, inline: &mut Vec<El>) -> R<CellParts<'x>> {
    let mut cell = CellParts { attrs, v: None, f: None, is: None };
    if empty {
        return Ok(cell);
    }
    loop {
        match lx.next(prefixes)? {
            Tok::Text(_) => {}
            Tok::End { name: "c", .. } => return Ok(cell),
            Tok::End { .. } => return Err(Bail),
            Tok::Start { name: "v", empty, .. } if cell.v.is_none() => {
                cell.v = Some(if empty { Cow::Borrowed("") } else { lx.text_of(prefixes, "v")? });
            }
            Tok::Start { name: "f", attrs, empty } if cell.f.is_none() => {
                let text = if empty { Cow::Borrowed("") } else { lx.text_of(prefixes, "f")? };
                cell.f = Some((attrs, text));
            }
            Tok::Start { name: "is", attrs, empty } if cell.is.is_none() => {
                let el = lx.element(prefixes, "is", attrs, empty, 1)?;
                cell.is = Some(inline.len());
                inline.push(el);
            }
            Tok::Start { name, empty, .. } => {
                if !empty {
                    lx.skip(prefixes, name, 1)?;
                }
            }
        }
    }
}

enum Tok<'x> {
    Start {
        name: &'x str,
        attrs: Attrs<'x>,
        empty: bool,
    },
    /// `start` is where the end tag begins.
    End {
        name: &'x str,
        start: usize,
    },
    /// Raw text, references not yet resolved.
    Text(&'x str),
}

struct Lexer<'x> {
    s: &'x str,
    at: usize,
    /// What the current row may still use.
    left: Budget,
    /// Elements open, the root included.
    open: usize,
}

impl<'x> Lexer<'x> {
    fn bytes(&self) -> &'x [u8] {
        self.s.as_bytes()
    }

    /// Charges a token to the row's budget.
    fn count(&mut self, tok: &Tok<'_>) -> R<()> {
        let take = |left: &mut usize, n: usize| left.checked_sub(n).map(|l| *left = l).ok_or(Bail);
        take(&mut self.left.nodes, 1)?;
        match tok {
            Tok::Start { attrs, empty, .. } => {
                take(&mut self.left.elements, 1)?;
                take(&mut self.left.attrs, attrs.len())?;
                // An empty element is as deep as any other.
                if self.open + 1 > self.left.depth {
                    return Err(Bail);
                }
                if !empty {
                    self.open += 1;
                }
            }
            Tok::End { .. } => self.open = self.open.saturating_sub(1),
            Tok::Text(_) => {}
        }
        Ok(())
    }

    /// The next token, its names checked against `prefixes`.
    fn next(&mut self, prefixes: &[&str]) -> R<Tok<'x>> {
        let tok = self.next_any()?;
        let ok = match &tok {
            Tok::Start { name, attrs, .. } => name_ok(name, prefixes) && attrs.iter().all(|(k, _)| !is_ns_decl(k) && name_ok(k, prefixes)),
            Tok::End { name, .. } => name_ok(name, prefixes),
            Tok::Text(_) => true,
        };
        if !ok {
            return Err(Bail);
        }
        self.count(&tok)?;
        Ok(tok)
    }

    fn next_any(&mut self) -> R<Tok<'x>> {
        let b = self.bytes();
        let rest = b.get(self.at..).ok_or(Bail)?;
        match rest.first() {
            None => Err(Bail),
            Some(b'<') => self.tag(),
            Some(_) => {
                let len = rest.iter().position(|&c| c == b'<').unwrap_or(rest.len());
                let t = self.s.get(self.at..self.at + len).ok_or(Bail)?;
                self.at += len;
                Ok(Tok::Text(t))
            }
        }
    }

    fn name(&mut self) -> R<&'x str> {
        let b = self.bytes();
        let start = self.at;
        match b.get(start) {
            Some(c) if c.is_ascii_alphabetic() || *c == b'_' => {}
            _ => return Err(Bail),
        }
        let len = b.get(start..).ok_or(Bail)?.iter().take_while(|c| c.is_ascii_alphanumeric() || matches!(c, b'_' | b'-' | b'.' | b':')).count();
        self.at += len;
        self.s.get(start..start + len).ok_or(Bail)
    }

    fn skip_ws(&mut self) -> usize {
        let b = self.bytes();
        let n = b.get(self.at..).map_or(0, |r| r.iter().take_while(|c| matches!(c, b' ' | b'\t' | b'\r' | b'\n')).count());
        self.at += n;
        n
    }

    fn byte(&self) -> Option<u8> {
        self.bytes().get(self.at).copied()
    }

    fn tag(&mut self) -> R<Tok<'x>> {
        let start = self.at;
        self.at += 1;
        if self.byte() == Some(b'/') {
            self.at += 1;
            let name = self.name()?;
            self.skip_ws();
            if self.byte() != Some(b'>') {
                return Err(Bail);
            }
            self.at += 1;
            return Ok(Tok::End { name, start });
        }
        // `<!` (comments, CDATA, DOCTYPE) and `<?` fail here.
        let name = self.name()?;
        let mut attrs = Attrs::new();
        loop {
            let ws = self.skip_ws();
            match self.byte() {
                Some(b'>') => {
                    self.at += 1;
                    return Ok(Tok::Start { name, attrs, empty: false });
                }
                Some(b'/') => {
                    self.at += 1;
                    if self.byte() != Some(b'>') {
                        return Err(Bail);
                    }
                    self.at += 1;
                    return Ok(Tok::Start { name, attrs, empty: true });
                }
                Some(_) if ws > 0 => {
                    if attrs.len() >= self.left.tag_attrs {
                        return Err(Bail);
                    }
                    let key = self.name()?;
                    self.skip_ws();
                    if self.byte() != Some(b'=') {
                        return Err(Bail);
                    }
                    self.at += 1;
                    self.skip_ws();
                    let quote = self.byte().filter(|q| matches!(*q, b'"' | b'\'')).ok_or(Bail)?;
                    self.at += 1;
                    let vstart = self.at;
                    let len = self.bytes().get(vstart..).ok_or(Bail)?.iter().position(|&c| c == quote).ok_or(Bail)?;
                    let raw = self.s.get(vstart..vstart + len).ok_or(Bail)?;
                    self.at = vstart + len + 1;
                    if raw.contains('<') {
                        return Err(Bail);
                    }
                    attrs.push((key, attr_value(raw)?));
                }
                _ => return Err(Bail),
            }
        }
    }

    /// The text of an element whose start tag was just read: its text with references resolved,
    /// up to its end tag. Child elements are left to the general reader.
    fn text_of(&mut self, prefixes: &[&str], name: &str) -> R<Cow<'x, str>> {
        let mut out: Option<String> = None;
        let mut first: Cow<'x, str> = Cow::Borrowed("");
        loop {
            match self.next(prefixes)? {
                Tok::Text(t) => {
                    let t = text(t)?;
                    match &mut out {
                        Some(o) => o.push_str(&t),
                        None if first.is_empty() => first = t,
                        None => {
                            let mut o = first.clone().into_owned();
                            o.push_str(&t);
                            out = Some(o);
                        }
                    }
                }
                Tok::End { name: n, .. } if n == name => return Ok(out.map_or(first, Cow::Owned)),
                _ => return Err(Bail),
            }
        }
    }

    /// Skips the content of element `name`, whose start tag was just read, and its end tag.
    fn skip(&mut self, prefixes: &[&str], name: &str, depth: usize) -> R<()> {
        if depth > MAX_DEPTH {
            return Err(Bail);
        }
        loop {
            match self.next(prefixes)? {
                Tok::Text(_) => {}
                Tok::End { name: n, .. } => return if n == name { Ok(()) } else { Err(Bail) },
                Tok::Start { name: child, empty, .. } => {
                    if !empty {
                        self.skip(prefixes, child, depth + 1)?;
                    }
                }
            }
        }
    }

    /// Element `name`, whose start tag was just read, as the general reader builds it.
    fn element(&mut self, prefixes: &[&str], name: &str, attrs: Attrs<'x>, empty: bool, depth: usize) -> R<El> {
        if depth > MAX_DEPTH {
            return Err(Bail);
        }
        let mut el = El { name: name.to_string(), attrs: attrs.owned_except(&[]), children: Vec::new() };
        if empty {
            return Ok(el);
        }
        loop {
            match self.next(prefixes)? {
                Tok::Text(t) => {
                    let t = text(t)?;
                    // Adjacent text is one node, as the general reader merges it.
                    if let Some(Node::Text(prev)) = el.children.last_mut() {
                        prev.push_str(&t);
                    } else {
                        el.children.push(Node::Text(t.into_owned()));
                    }
                }
                Tok::End { name: n, .. } => return if n == name { Ok(el) } else { Err(Bail) },
                Tok::Start { name: child, attrs, empty } => {
                    let c = self.element(prefixes, child, attrs, empty, depth + 1)?;
                    el.children.push(Node::El(c));
                }
            }
        }
    }
}

/// Is `name` read as written? Unprefixed names are; a prefixed one when the root declares the
/// prefix for a namespace whose canonical prefix is that prefix.
fn name_ok(name: &str, prefixes: &[&str]) -> bool {
    match name.split_once(':') {
        None => true,
        Some((p, local)) => !local.is_empty() && !local.contains(':') && prefixes.contains(&p),
    }
}

/// Text content as the general reader reads it: literal line ends become `\n`, references are
/// resolved (and not line-end normalised). An unknown or unterminated reference bails.
fn text(raw: &str) -> R<Cow<'_, str>> {
    if !raw.contains(['&', '\r']) {
        return Ok(Cow::Borrowed(raw));
    }
    let mut out = String::with_capacity(raw.len());
    let mut rest = raw;
    loop {
        let (lit, after) = match rest.find('&') {
            Some(i) => (rest.get(..i).ok_or(Bail)?, Some(rest.get(i + 1..).ok_or(Bail)?)),
            None => (rest, None),
        };
        if lit.contains('\r') {
            out.push_str(&lit.replace("\r\n", "\n").replace('\r', "\n"));
        } else {
            out.push_str(lit);
        }
        let Some(after) = after else { return Ok(Cow::Owned(out)) };
        let (c, tail) = reference(after)?;
        out.push(c);
        rest = tail;
    }
}

/// An attribute value as the general reader reads it: references resolved, literal tabs and
/// line ends turned into spaces (a CR LF into one).
fn attr_value(raw: &str) -> R<Cow<'_, str>> {
    if !raw.contains(['&', '\t', '\n', '\r']) {
        return Ok(Cow::Borrowed(raw));
    }
    let mut out = String::with_capacity(raw.len());
    let mut rest = raw;
    while let Some(i) = rest.find(['&', '\t', '\n', '\r']) {
        out.push_str(rest.get(..i).ok_or(Bail)?);
        let tail = rest.get(i..).ok_or(Bail)?;
        match tail.strip_prefix('&') {
            Some(after) => {
                let (c, t) = reference(after)?;
                out.push(c);
                rest = t;
            }
            None => {
                out.push(' ');
                rest = tail.strip_prefix("\r\n").or_else(|| tail.get(1..)).ok_or(Bail)?;
            }
        }
    }
    out.push_str(rest);
    Ok(Cow::Owned(out))
}

/// The character of the reference that `after` (the text after an `&`) starts with, and what
/// follows it. Only predefined and numeric references are read here.
fn reference(after: &str) -> R<(char, &str)> {
    let len = after.bytes().take_while(|b| b.is_ascii_alphanumeric() || *b == b'#').count();
    if after.as_bytes().get(len) != Some(&b';') {
        return Err(Bail);
    }
    let c = craft_xml::entity(after.get(..len).ok_or(Bail)?).ok_or(Bail)?;
    Ok((c, after.get(len + 1..).ok_or(Bail)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    type Out = (Option<El>, Vec<Row>, (u64, u64, u64), bool);

    fn opts() -> Options<'static> {
        Options { unknown_entity: craft_xml::UnknownEntity::Literal, ..Options::canonical(&CANONICAL) }
    }

    thread_local! {
        static LIMITS: std::cell::Cell<craft_xml::Limits> = const { std::cell::Cell::new(craft_xml::Limits::DEFAULT) };
    }

    /// [`opts`] with the limits of the case being checked.
    fn limited() -> Options<'static> {
        opts().with_limits(LIMITS.with(std::cell::Cell::get))
    }

    /// The general reader alone, skipping the first `skip` rows.
    fn general(bytes: &[u8], mut skip: u64, out: &mut Vec<Row>) -> (Option<El>, (u64, u64, u64), bool) {
        let mut rows = RowReader::default();
        let (root, err) = limited().parse_streaming_partial(bytes, &["row"], |e| {
            if let Some(row) = rows.row(&e) {
                if skip > 0 {
                    skip -= 1;
                } else {
                    out.push(row);
                }
            }
            Ok::<(), craft_xml::Error>(())
        });
        (root, (rows.rows, rows.dropped, rows.dropped_cells), err.is_some())
    }

    /// Reads `bytes` a few bytes at a time, as a stream that is not one slice.
    struct Trickle<'b>(&'b [u8]);

    impl std::io::Read for Trickle<'_> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            let n = buf.len().min(self.0.len()).min(5);
            let (head, rest) = self.0.split_at(n);
            buf[..n].copy_from_slice(head);
            self.0 = rest;
            Ok(n)
        }
    }

    thread_local! {
        static CHUNK_SIZE: std::cell::Cell<usize> = const { std::cell::Cell::new(super::CHUNK) };
    }

    /// As `Package::sheet` reads: fast, then the general reader for what is left. Also says
    /// whether the fast reader read the whole part.
    fn combined(bytes: &[u8]) -> (Out, bool) {
        let mut out = Vec::new();
        let r = read_stream(
            &mut Trickle(bytes),
            bytes.len() as u64,
            &limited(),
            &mut |row| {
                out.push(row);
                Ok::<(), ()>(())
            },
            CHUNK_SIZE.with(std::cell::Cell::get),
        );
        match r {
            Ok(s) => {
                assert_eq!(s.bytes, bytes.len() as u64, "a whole read counts every byte");
                let read = s.read;
                ((Some(read.root), out, (read.rows.rows, read.rows.dropped, read.rows.dropped_cells), false), true)
            }
            Err(Stop::Caller(())) => (Default::default(), false),
            Err(Stop::Fallback { emitted }) => {
                let (root, counts, err) = general(bytes, emitted, &mut out);
                ((root, out, counts, err), false)
            }
        }
    }

    const NS: &str = r#"xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships" xmlns:mc="http://schemas.openxmlformats.org/markup-compatibility/2006" mc:Ignorable="x14ac xr" xmlns:x14ac="http://schemas.microsoft.com/office/spreadsheetml/2009/9/ac" xmlns:xr="http://schemas.microsoft.com/office/spreadsheetml/2014/revision""#;

    fn sheet(ns: &str, data: &str) -> String {
        format!(
            "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\r\n<worksheet {ns} xr:uid=\"{{1}}\"><dimension ref=\"A1:C3\"/><sheetViews><sheetView workbookViewId=\"0\"/></sheetViews><sheetFormatPr defaultRowHeight=\"15\" x14ac:dyDescent=\"0.25\"/><cols><col min=\"1\" max=\"1\" width=\"9\"/></cols>{data}<mergeCells count=\"1\"><mergeCell ref=\"A1:B1\"/></mergeCells><pageMargins left=\"0.7\" right=\"0.7\" top=\"0.75\" bottom=\"0.75\" header=\"0.3\" footer=\"0.3\"/></worksheet>"
        )
    }

    /// Every case reads the same both ways; the plain ones also read wholly by the fast reader.
    #[test]
    fn reads_as_the_general_reader() {
        let row1 = r#"<row r="1" spans="1:3" ht="20" customHeight="1" x14ac:dyDescent="0.25"><c r="A1" s="1" t="s"><v>0</v></c><c r="B1"><v>1.5</v></c><c r="C1"><f>A1*2</f><v>3</v></c></row>"#;
        let fast = [
            format!("<sheetData>{row1}</sheetData>"),
            format!("<sheetData>\n  {row1}\n  <row r=\"2\"><c r=\"A2\" t=\"str\"><f t=\"shared\" ref=\"A2:A9\" si=\"0\">B1&amp;\"x\"</f><v>a_x0009_b &lt;&#65;&#x42;&gt;</v></c></row>\n</sheetData>"),
            "<sheetData><row><c><v>1</v></c><c t=\"b\"><v>1</v></c><c t=\"e\"><v>#N/A</v></c><c t=\"d\"><v>2024-01-01</v></c><c t='n'><v> 7 </v></c><c t=\"n\"><v>abc</v></c><c/><c r=\"Q1\" vm=\"1\" cm=\"2\" ph=\"1\"><v/></c></row><row/><row r=\"9\" s=\"3\" customFormat=\"1\" hidden=\"true\" outlineLevel=\"12\" collapsed=\"1\"/></sheetData>".into(),
            "<sheetData><row r=\"0\"><c><v>1</v></c><c><v>2</v></c></row><row r=\"1048577\"><c r=\"A1048577\"><v>3</v></c></row><row r=\"3\"><c r=\"XFE3\"><v>4</v></c><c r=\"B3\"><v>5</v></c><c r=\"junk\"><v>6</v></c></row></sheetData>".into(),
            "<sheetData><row r=\"1\" a=\"1\" a=\"2\" note=\"tab\there\r\nand line\"><c r=\"A1\" s=\"1\" s=\"2\"><v>line\r\none\rtwo</v><v>second v ignored</v><f t=\"array\" ref=\"A1:A2\" aca=\"1\">SUM(B1:B2)</f><extLst><ext uri=\"x\"><foo/></ext></extLst></c></row></sheetData>".into(),
            "<sheetData><row r=\"1\"><c r=\"A1\" t=\"inlineStr\"><is><t>in_x000A_line</t></is></c><c r=\"B1\" t=\"inlineStr\"><is><r><rPr><b/><sz val=\"11\"/></rPr><t>bold</t></r><r><t>plain &amp; more</t></r></is></c><c r=\"C1\" t=\"inlineStr\"><v>fallback</v></c></row></sheetData>".into(),
            "<sheetData><row r=\"2\">text in a row<c r=\"A2\"><v>1</v></c><x14ac:foo/></row></sheetData>".into(),
            "<sheetData><row r=\"5\"><c r=\"A5\"><v>1</v></c><row r=\"6\"><c r=\"A6\"><v>2</v></c></row></row></sheetData>".into(),
            "<sheetData><row r=\"1\"><c r=\"A1\" t=\"s\"><v>&#9;</v></c><c r=\"B1\"><f>\"&#13;\"</f><v>&#10;</v></c></row></sheetData>".into(),
        ];
        let fallback = [
            // Markup the fast reader leaves to the general one, at the start, middle and end.
            format!("<sheetData>{row1}<!-- note -->{row1}</sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\"><v><![CDATA[1<2]]></v></c></row>{row1}</sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\" t=\"inlineStr\"><is><t xml:space=\"preserve\"> x </t></is></c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\"><v>&nbsp;</v></c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\"><v>a & b</v></c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><x:c r=\"A2\"><v>1</v></x:c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\" xmlns:q=\"urn:q\"><c r=\"A2\" q:z=\"1\"><v>1</v></c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\" mc:Ignorable=\"x14ac\"><c r=\"A2\"><v>1</v></c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\"><v>1</c></row>{row1}</sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\"><v>1</v></c>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\" s=1><v>1</v></c></row></sheetData>"),
            format!("<sheetData>{row1}<row r=\"2\"><c r=\"A2\"><v>1<b/>2</v></c></row></sheetData>"),
            format!("<sheetData>{row1}<other/>{row1}</sheetData>"),
            format!("<sheetData>{row1} x {row1}</sheetData>"),
            format!("<sheetData>{row1}\r\n{row1}</sheetData>"),
            format!("<sheetData>{row1}</sheetData><row r=\"7\"><c r=\"A7\"><v>7</v></c></row>"),
            format!("<row r=\"7\"><c r=\"A7\"><v>7</v></c></row><sheetData>{row1}</sheetData>"),
            "<sheetData/>".into(),
            format!("<!-- c --><sheetData>{row1}</sheetData>"),
        ];
        let tight = [
            craft_xml::Limits::DEFAULT,
            craft_xml::Limits { max_nodes: 40, ..craft_xml::Limits::DEFAULT },
            craft_xml::Limits { max_elements: 25, ..craft_xml::Limits::DEFAULT },
            craft_xml::Limits { max_attrs: 3, max_attrs_total: 30, ..craft_xml::Limits::DEFAULT },
            craft_xml::Limits { max_depth: 6, ..craft_xml::Limits::DEFAULT },
        ];
        let chunks = [1, 3, 17, 4096].map(|c| (craft_xml::Limits::DEFAULT, c));
        for (limits, chunk) in tight.into_iter().map(|l| (l, super::CHUNK)).chain(chunks) {
            LIMITS.with(|l| l.set(limits));
            CHUNK_SIZE.with(|c| c.set(chunk));
            for data in fast.iter().chain(&fallback) {
                for ns in [
                    NS,
                    "xmlns=\"http://purl.oclc.org/ooxml/spreadsheetml/main\" xmlns:x14ac=\"http://schemas.microsoft.com/office/spreadsheetml/2009/9/ac\" xmlns:xr=\"urn:other\"",
                    "xmlns=\"urn:not-spreadsheetml\"",
                ] {
                    let xml = sheet(ns, data);
                    let mut rows = Vec::new();
                    let (root, counts, err) = general(xml.as_bytes(), 0, &mut rows);
                    let (got, whole) = combined(xml.as_bytes());
                    assert_eq!(got, (root, rows, counts, err), "{limits:?} {xml}");
                    if ns == NS && fast.contains(data) && limits == craft_xml::Limits::DEFAULT {
                        assert!(whole, "the fast reader should read {data}");
                    }
                }
            }
        }
        LIMITS.with(|l| l.set(craft_xml::Limits::DEFAULT));
        CHUNK_SIZE.with(|c| c.set(super::CHUNK));
        // A byte-order mark, and a part the reader cannot decode as UTF-8.
        for bytes in
            [[&[0xEF, 0xBB, 0xBF][..], sheet(NS, &fast[0]).as_bytes()].concat(), [sheet(NS, &fast[0]).as_bytes(), &[0xFF, b'<'][..]].concat()]
        {
            let mut rows = Vec::new();
            let (root, counts, err) = general(&bytes, 0, &mut rows);
            assert_eq!(combined(&bytes).0, (root, rows, counts, err));
        }
    }

    /// The caller's error stops the read with that error.
    #[test]
    fn a_caller_error_stops_the_read() {
        let xml = sheet(NS, "<sheetData><row r=\"1\"><c><v>1</v></c></row><row r=\"2\"><c><v>2</v></c></row></sheetData>");
        let mut seen = 0;
        let r = read_stream(
            &mut xml.as_bytes(),
            xml.len() as u64,
            &opts(),
            &mut |_| {
                seen += 1;
                Err("stop")
            },
            super::CHUNK,
        );
        assert!(matches!(r, Err(Stop::Caller("stop"))));
        assert_eq!(seen, 1);
    }
}
