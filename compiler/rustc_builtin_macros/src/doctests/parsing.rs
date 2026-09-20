#![allow(unused)]

use std::borrow::Cow;
use std::iter::Peekable;
use std::ops::Range;
use std::str::CharIndices;

use pulldown_cmark::{
    self, BrokenLink, CodeBlockKind, CowStr, Event, LinkType, Options, Parser, Tag, TagEnd, html,
};
use rustc_ast::rustdoc::{DocFragment, source_span_for_markdown_range};
use rustc_errors::{Diag, DiagMessage};
//use rustc_hir::def_id::LocalDefId;
//use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::edition::Edition;
use rustc_span::source_map::SourceMap;

/// Options for rendering Markdown in the main body of documentation.
fn main_body_opts() -> Options {
    Options::ENABLE_TABLES
        | Options::ENABLE_FOOTNOTES
        | Options::ENABLE_STRIKETHROUGH
        | Options::ENABLE_TASKLISTS
        | Options::ENABLE_SMART_PUNCTUATION
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub(crate) enum ErrorCodes {
    Yes,
    No,
}

impl ErrorCodes {
    pub(crate) fn from(b: bool) -> Self {
        match b {
            true => ErrorCodes::Yes,
            false => ErrorCodes::No,
        }
    }

    pub(crate) fn as_bool(self) -> bool {
        match self {
            ErrorCodes::Yes => true,
            ErrorCodes::No => false,
        }
    }
}

/// A newtype that represents a relative line number in Markdown.
///
/// In other words, this represents an offset from the first line of Markdown
/// in a doc comment or other source. If the first Markdown line appears on line 32,
/// and the `MdRelLine` is 3, then the absolute line for this one is 35. I.e., it's
/// a zero-based offset.
#[derive(Debug)]
pub(crate) struct MdRelLine {
    offset: usize,
}

impl MdRelLine {
    /// See struct docs.
    pub(crate) const fn new(offset: usize) -> Self {
        Self { offset }
    }

    /// See struct docs.
    pub(crate) const fn offset(&self) -> usize {
        self.offset
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CodeLineMapping {
    pub(crate) generated: Range<usize>,
    pub(crate) original: Span,
}

pub(crate) trait DocTestVisitor {
    fn visit_test(
        &mut self,
        test: String,
        config: LangString,
        rel_line: MdRelLine,
        code_mappings: Vec<CodeLineMapping>,
    );
    fn visit_header(&mut self, _name: &str, _level: u32) {}
}

pub(crate) fn find_testable_code<T: DocTestVisitor>(
    doc: &str,
    tests: &mut T,
    error_codes: ErrorCodes,
    extra_info: Option<&ExtraInfo<'_ /*, '_*/>>,
) {
    find_codes(doc, tests, error_codes, extra_info, false)
}

pub(crate) fn find_codes<T: DocTestVisitor>(
    doc: &str,
    tests: &mut T,
    error_codes: ErrorCodes,
    extra_info: Option<&ExtraInfo<'_ /*, '_*/>>,
    include_non_rust: bool,
) {
    let mut parser = Parser::new_ext(doc, main_body_opts()).into_offset_iter();
    let mut prev_offset = 0;
    let mut nb_lines = 0;
    let mut register_header = None;
    while let Some((event, offset)) = parser.next() {
        match event {
            Event::Start(Tag::CodeBlock(kind)) => {
                let block_info = match kind {
                    CodeBlockKind::Fenced(ref lang) => {
                        if lang.is_empty() {
                            Default::default()
                        } else {
                            LangString::parse(lang, error_codes /*, extra_info*/)
                        }
                    }
                    CodeBlockKind::Indented => Default::default(),
                };
                if !include_non_rust && !block_info.rust {
                    continue;
                }

                let mut test_s = String::new();
                let mut text_events = Vec::new();

                while let Some((Event::Text(s), offset)) = parser.next() {
                    let start = test_s.len();
                    test_s.push_str(&s);
                    text_events.push((start..test_s.len(), offset));
                }
                let (text, code_mappings) = map_code_block(doc, &test_s, &text_events, extra_info);

                nb_lines += doc[prev_offset..offset.start].lines().count();
                // If there are characters between the preceding line ending and
                // this code block, `str::lines` will return an additional line,
                // which we subtract here.
                if nb_lines != 0 && !&doc[prev_offset..offset.start].ends_with('\n') {
                    nb_lines -= 1;
                }
                let line = MdRelLine::new(nb_lines);
                tests.visit_test(text, block_info, line, code_mappings);
                prev_offset = offset.start;
            }
            Event::Start(Tag::Heading { level, .. }) => {
                register_header = Some(level as u32);
            }
            Event::Text(ref s) if register_header.is_some() => {
                let level = register_header.unwrap();
                tests.visit_header(s, level);
                register_header = None;
            }
            _ => {}
        }
    }
}

fn map_code_block(
    doc: &str,
    code: &str,
    text_events: &[(Range<usize>, Range<usize>)],
    extra_info: Option<&ExtraInfo<'_ /*, '_*/>>,
) -> (String, Vec<CodeLineMapping>) {
    let mut text = String::new();
    let mut code_mappings = Vec::new();
    let mut code_line_start = 0;

    for (line_index, line) in code.lines().enumerate() {
        if line_index != 0 {
            text.push('\n');
        }

        let generated_start = text.len();
        let mapped_line = map_line(line).for_code();
        text.push_str(&mapped_line);
        let generated = generated_start..text.len();

        let offset = line.len().saturating_sub(mapped_line.len());

        if let Some(extra_info) = extra_info
            && let Some(fragments) = extra_info.fragments
        {
            let code_line = (code_line_start + offset)..(code_line_start + mapped_line.len());
            if let Some(md_range) = markdown_range_for_code_range(text_events, code_line)
                && let Some((original, _)) =
                    source_span_for_markdown_range(extra_info.source_map, doc, &md_range, fragments)
            {
                code_mappings.push(CodeLineMapping { generated, original });
            }
        }

        code_line_start += line.len() + 1;
    }

    (text, code_mappings)
}

fn markdown_range_for_code_range(
    text_events: &[(Range<usize>, Range<usize>)],
    code_range: Range<usize>,
) -> Option<Range<usize>> {
    text_events.iter().find_map(|(event_code_range, event_md_range)| {
        if event_code_range.start <= code_range.start && code_range.end <= event_code_range.end {
            let start = event_md_range.start + code_range.start - event_code_range.start;
            let end = event_md_range.start + code_range.end - event_code_range.start;
            Some(start..end)
        } else {
            None
        }
    })
}

pub(crate) struct ExtraInfo<'doc /*, 'tcx*/> {
    /*def_id: LocalDefId,
    sp: Span,
    tcx: TyCtxt<'tcx>,*/
    source_map: &'doc SourceMap,
    fragments: Option<&'doc [DocFragment]>,
}

impl<'doc /*, 'tcx*/> ExtraInfo<'doc /*, 'tcx*/> {
    pub(crate) fn new(
        /*tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        sp: Span,*/
        source_map: &'doc SourceMap,
        fragments: Option<&'doc [DocFragment]>,
    ) -> ExtraInfo<'doc /*, 'tcx*/> {
        ExtraInfo { /*def_id, sp, tcx,*/ source_map, fragments }
    }

    /*fn error_invalid_codeblock_attr(&self, msg: impl Into<DiagMessage>) {
        self.error_invalid_codeblock_attr_with_help(msg, |_| {});
    }

    fn error_invalid_codeblock_attr_with_help(
        &self,
        msg: impl Into<DiagMessage>,
        f: impl for<'a, 'b> FnOnce(&'b mut Diag<'a, ()>),
    ) {
        self.tcx.emit_node_span_lint(
            crate::lint::INVALID_CODEBLOCK_ATTRIBUTES,
            self.tcx.local_def_id_to_hir_id(self.def_id),
            self.sp,
            rustc_errors::DiagDecorator(|lint| {
                lint.primary_message(msg);
                f(lint);
            }),
        );
    }*/
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub(crate) struct LangString {
    pub(crate) original: String,
    pub(crate) should_panic: bool,
    pub(crate) no_run: bool,
    pub(crate) ignore: Ignore,
    pub(crate) rust: bool,
    pub(crate) test_harness: bool,
    pub(crate) compile_fail: bool,
    pub(crate) standalone_crate: bool,
    pub(crate) error_codes: Vec<String>,
    pub(crate) edition: Option<Edition>,
    pub(crate) added_classes: Vec<String>,
    pub(crate) unknown: Vec<String>,
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub(crate) enum Ignore {
    All,
    None,
    Some(Vec<String>),
}

/// This is the parser for fenced codeblocks attributes.
///
/// It implements the following grammar as expressed in ABNF:
///
/// ```ABNF
/// lang-string = *(token-list / delimited-attribute-list / comment)
/// bareword = LEADINGCHAR *(CHAR)
/// bareword-without-leading-char = CHAR *(CHAR)
/// quoted-string = QUOTE *(NONQUOTE) QUOTE
/// token = bareword / quoted-string
/// token-without-leading-char = bareword-without-leading-char / quoted-string
/// sep = COMMA/WS *(COMMA/WS)
/// attribute = (DOT token)/(token EQUAL token-without-leading-char)
/// attribute-list = [sep] attribute *(sep attribute) [sep]
/// delimited-attribute-list = OPEN-CURLY-BRACKET attribute-list CLOSE-CURLY-BRACKET
/// token-list = [sep] token *(sep token) [sep]
/// comment = OPEN_PAREN *<all characters except closing parentheses> CLOSE_PAREN
///
/// OPEN_PAREN = "("
/// CLOSE_PARENT = ")"
/// OPEN-CURLY-BRACKET = "{"
/// CLOSE-CURLY-BRACKET = "}"
/// LEADINGCHAR = ALPHA | DIGIT | "_" | "-" | ":"
/// ; All ASCII punctuation except comma, quote, equals, backslash, grave (backquote) and braces.
/// ; Comma is used to separate language tokens, so it can't be used in one.
/// ; Quote is used to allow otherwise-disallowed characters in language tokens.
/// ; Equals is used to make key=value pairs in attribute blocks.
/// ; Backslash and grave are special Markdown characters.
/// ; Braces are used to start an attribute block.
/// CHAR = ALPHA | DIGIT | "_" | "-" | ":" | "." | "!" | "#" | "$" | "%" | "&" | "*" | "+" | "/" |
///        ";" | "<" | ">" | "?" | "@" | "^" | "|" | "~"
/// NONQUOTE = %x09 / %x20 / %x21 / %x23-7E ; TAB / SPACE / all printable characters except `"`
/// COMMA = ","
/// DOT = "."
/// EQUAL = "="
///
/// ALPHA = %x41-5A / %x61-7A ; A-Z / a-z
/// DIGIT = %x30-39
/// WS = %x09 / " "
/// ```
pub(crate) struct TagIterator<'a /*, 'tcx*/> {
    inner: Peekable<CharIndices<'a>>,
    data: &'a str,
    is_in_attribute_block: bool,
    //extra: Option<&'a ExtraInfo<'a, 'tcx>>,
    is_error: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LangStringToken<'a> {
    LangToken(&'a str),
    ClassAttribute(&'a str),
    KeyValueAttribute(&'a str, &'a str),
}

fn is_leading_char(c: char) -> bool {
    c == '_' || c == '-' || c == ':' || c.is_ascii_alphabetic() || c.is_ascii_digit()
}
fn is_bareword_char(c: char) -> bool {
    is_leading_char(c) || ".!#$%&*+/;<>?@^|~".contains(c)
}
fn is_separator(c: char) -> bool {
    c == ' ' || c == ',' || c == '\t'
}

struct Indices {
    start: usize,
    end: usize,
}

impl<'a /*, 'tcx*/> TagIterator<'a /*, 'tcx*/> {
    pub(crate) fn new(data: &'a str /*, extra: Option<&'a ExtraInfo<'a, 'tcx>>*/) -> Self {
        Self {
            inner: data.char_indices().peekable(),
            data,
            is_in_attribute_block: false,
            //extra,
            is_error: false,
        }
    }

    fn emit_error(&mut self, err: impl Into<DiagMessage>) {
        /*if let Some(extra) = self.extra {
            extra.error_invalid_codeblock_attr(err);
        }*/
        self.is_error = true;
    }

    fn skip_separators(&mut self) -> Option<usize> {
        while let Some((pos, c)) = self.inner.peek() {
            if !is_separator(*c) {
                return Some(*pos);
            }
            self.inner.next();
        }
        None
    }

    fn parse_string(&mut self, start: usize) -> Option<Indices> {
        for (pos, c) in self.inner.by_ref() {
            if c == '"' {
                return Some(Indices { start: start + 1, end: pos });
            }
        }
        self.emit_error("unclosed quote string `\"`");
        None
    }

    fn parse_class(&mut self, start: usize) -> Option<LangStringToken<'a>> {
        while let Some((pos, c)) = self.inner.peek().copied() {
            if is_bareword_char(c) {
                self.inner.next();
            } else {
                let class = &self.data[start + 1..pos];
                if class.is_empty() {
                    self.emit_error(format!("unexpected `{c}` character after `.`"));
                    return None;
                } else if self.check_after_token() {
                    return Some(LangStringToken::ClassAttribute(class));
                } else {
                    return None;
                }
            }
        }
        let class = &self.data[start + 1..];
        if class.is_empty() {
            self.emit_error("missing character after `.`");
            None
        } else if self.check_after_token() {
            Some(LangStringToken::ClassAttribute(class))
        } else {
            None
        }
    }

    fn parse_token(&mut self, start: usize) -> Option<Indices> {
        while let Some((pos, c)) = self.inner.peek() {
            if !is_bareword_char(*c) {
                return Some(Indices { start, end: *pos });
            }
            self.inner.next();
        }
        self.emit_error("unexpected end");
        None
    }

    fn parse_key_value(&mut self, c: char, start: usize) -> Option<LangStringToken<'a>> {
        let key_indices =
            if c == '"' { self.parse_string(start)? } else { self.parse_token(start)? };
        if key_indices.start == key_indices.end {
            self.emit_error("unexpected empty string as key");
            return None;
        }

        if let Some((_, c)) = self.inner.next() {
            if c != '=' {
                self.emit_error(format!("expected `=`, found `{c}`"));
                return None;
            }
        } else {
            self.emit_error("unexpected end");
            return None;
        }
        let value_indices = match self.inner.next() {
            Some((pos, '"')) => self.parse_string(pos)?,
            Some((pos, c)) if is_bareword_char(c) => self.parse_token(pos)?,
            Some((_, c)) => {
                self.emit_error(format!("unexpected `{c}` character after `=`"));
                return None;
            }
            None => {
                self.emit_error("expected value after `=`");
                return None;
            }
        };
        if value_indices.start == value_indices.end {
            self.emit_error("unexpected empty string as value");
            None
        } else if self.check_after_token() {
            Some(LangStringToken::KeyValueAttribute(
                &self.data[key_indices.start..key_indices.end],
                &self.data[value_indices.start..value_indices.end],
            ))
        } else {
            None
        }
    }

    /// Returns `false` if an error was emitted.
    fn check_after_token(&mut self) -> bool {
        if let Some((_, c)) = self.inner.peek().copied() {
            if c == '}' || is_separator(c) || c == '(' {
                true
            } else {
                self.emit_error(format!("unexpected `{c}` character"));
                false
            }
        } else {
            // The error will be caught on the next iteration.
            true
        }
    }

    fn parse_in_attribute_block(&mut self) -> Option<LangStringToken<'a>> {
        if let Some((pos, c)) = self.inner.next() {
            if c == '}' {
                self.is_in_attribute_block = false;
                return self.next();
            } else if c == '.' {
                return self.parse_class(pos);
            } else if c == '"' || is_leading_char(c) {
                return self.parse_key_value(c, pos);
            } else {
                self.emit_error(format!("unexpected character `{c}`"));
                return None;
            }
        }
        self.emit_error("unclosed attribute block (`{}`): missing `}` at the end");
        None
    }

    /// Returns `false` if an error was emitted.
    fn skip_paren_block(&mut self) -> bool {
        for (_, c) in self.inner.by_ref() {
            if c == ')' {
                return true;
            }
        }
        self.emit_error("unclosed comment: missing `)` at the end");
        false
    }

    fn parse_outside_attribute_block(&mut self, start: usize) -> Option<LangStringToken<'a>> {
        while let Some((pos, c)) = self.inner.next() {
            if c == '"' {
                if pos != start {
                    self.emit_error("expected ` `, `{` or `,` found `\"`");
                    return None;
                }
                let indices = self.parse_string(pos)?;
                if let Some((_, c)) = self.inner.peek().copied()
                    && c != '{'
                    && !is_separator(c)
                    && c != '('
                {
                    self.emit_error(format!("expected ` `, `{{` or `,` after `\"`, found `{c}`"));
                    return None;
                }
                return Some(LangStringToken::LangToken(&self.data[indices.start..indices.end]));
            } else if c == '{' {
                self.is_in_attribute_block = true;
                return self.next();
            } else if is_separator(c) {
                if pos != start {
                    return Some(LangStringToken::LangToken(&self.data[start..pos]));
                }
                return self.next();
            } else if c == '(' {
                if !self.skip_paren_block() {
                    return None;
                }
                if pos != start {
                    return Some(LangStringToken::LangToken(&self.data[start..pos]));
                }
                return self.next();
            } else if (pos == start && is_leading_char(c)) || (pos != start && is_bareword_char(c))
            {
                continue;
            } else {
                self.emit_error(format!("unexpected character `{c}`"));
                return None;
            }
        }
        let token = &self.data[start..];
        if token.is_empty() { None } else { Some(LangStringToken::LangToken(&self.data[start..])) }
    }
}

impl<'a> Iterator for TagIterator<'a /*, '_*/> {
    type Item = LangStringToken<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_error {
            return None;
        }
        let Some(start) = self.skip_separators() else {
            if self.is_in_attribute_block {
                self.emit_error("unclosed attribute block (`{}`): missing `}` at the end");
            }
            return None;
        };
        if self.is_in_attribute_block {
            self.parse_in_attribute_block()
        } else {
            self.parse_outside_attribute_block(start)
        }
    }
}

impl Default for LangString {
    fn default() -> Self {
        Self {
            original: String::new(),
            should_panic: false,
            no_run: false,
            ignore: Ignore::None,
            rust: true,
            test_harness: false,
            compile_fail: false,
            standalone_crate: false,
            error_codes: Vec::new(),
            edition: None,
            added_classes: Vec::new(),
            unknown: Vec::new(),
        }
    }
}

impl LangString {
    fn parse_without_check(string: &str, allow_error_code_check: ErrorCodes) -> Self {
        Self::parse(string, allow_error_code_check /*, None*/)
    }

    fn parse(
        string: &str,
        allow_error_code_check: ErrorCodes,
        //extra: Option<&ExtraInfo<'_, '_>>,
    ) -> Self {
        let allow_error_code_check = allow_error_code_check.as_bool();
        let mut seen_rust_tags = false;
        let mut seen_other_tags = false;
        let mut seen_custom_tag = false;
        let mut data = LangString::default();
        let mut ignores = vec![];

        data.original = string.to_owned();

        let mut call = |tokens: &mut dyn Iterator<Item = LangStringToken<'_>>| {
            for token in tokens {
                match token {
                    LangStringToken::LangToken("should_panic") => {
                        data.should_panic = true;
                        seen_rust_tags = !seen_other_tags;
                    }
                    LangStringToken::LangToken("no_run") => {
                        data.no_run = true;
                        seen_rust_tags = !seen_other_tags;
                    }
                    LangStringToken::LangToken("ignore") => {
                        data.ignore = Ignore::All;
                        seen_rust_tags = !seen_other_tags;
                    }
                    LangStringToken::LangToken(x)
                        if let Some(ignore) = x.strip_prefix("ignore-") =>
                    {
                        ignores.push(ignore.to_owned());
                        seen_rust_tags = !seen_other_tags;
                    }
                    LangStringToken::LangToken("rust") => {
                        data.rust = true;
                        seen_rust_tags = true;
                    }
                    LangStringToken::LangToken("custom") => {
                        seen_custom_tag = true;
                    }
                    LangStringToken::LangToken("test_harness") => {
                        data.test_harness = true;
                        seen_rust_tags = !seen_other_tags || seen_rust_tags;
                    }
                    LangStringToken::LangToken("compile_fail") => {
                        data.compile_fail = true;
                        seen_rust_tags = !seen_other_tags || seen_rust_tags;
                        data.no_run = true;
                    }
                    LangStringToken::LangToken("standalone_crate") => {
                        data.standalone_crate = true;
                        seen_rust_tags = !seen_other_tags || seen_rust_tags;
                    }
                    LangStringToken::LangToken(x)
                        if let Some(edition) = x.strip_prefix("edition") =>
                    {
                        data.edition = edition.parse::<Edition>().ok();
                    }
                    /*LangStringToken::LangToken(x)
                        if let Some(edition) = x.strip_prefix("rust")
                            && edition.parse::<Edition>().is_ok()
                            && let Some(extra) = extra =>
                    {
                        extra.error_invalid_codeblock_attr_with_help(
                            format!("unknown attribute `{x}`"),
                            |lint| {
                                lint.help(format!(
                                    "there is an attribute with a similar name: `edition{edition}`"
                                ));
                            },
                        );
                    }*/
                    LangStringToken::LangToken(x)
                        if allow_error_code_check
                            && let Some(error_code) = x.strip_prefix('E')
                            && error_code.len() == 4 =>
                    {
                        if error_code.parse::<u32>().is_ok() {
                            data.error_codes.push(x.to_owned());
                            seen_rust_tags = !seen_other_tags || seen_rust_tags;
                        } else {
                            seen_other_tags = true;
                        }
                    }
                    /*LangStringToken::LangToken(x) if let Some(extra) = extra => {
                        if let Some(help) = match x.to_lowercase().as_str() {
                            "compile-fail" | "compile_fail" | "compilefail" => Some(
                                "use `compile_fail` to invert the results of this test, so that it \
                                passes if it cannot be compiled and fails if it can",
                            ),
                            "should-panic" | "should_panic" | "shouldpanic" => Some(
                                "use `should_panic` to invert the results of this test, so that if \
                                passes if it panics and fails if it does not",
                            ),
                            "no-run" | "no_run" | "norun" => Some(
                                "use `no_run` to compile, but not run, the code sample during \
                                testing",
                            ),
                            "test-harness" | "test_harness" | "testharness" => Some(
                                "use `test_harness` to run functions marked `#[test]` instead of a \
                                potentially-implicit `main` function",
                            ),
                            "standalone" | "standalone_crate" | "standalone-crate"
                                if extra.sp.at_least_rust_2024() =>
                            {
                                Some(
                                    "use `standalone_crate` to compile this code block \
                                        separately",
                                )
                            }
                            _ => None,
                        } {
                            extra.error_invalid_codeblock_attr_with_help(
                                format!("unknown attribute `{x}`"),
                                |lint| {
                                    lint.help(help).help(
                                        "this code block may be skipped during testing, \
                                            because unknown attributes are treated as markers for \
                                            code samples written in other programming languages, \
                                            unless it is also explicitly marked as `rust`",
                                    );
                                },
                            );
                        }
                        seen_other_tags = true;
                        data.unknown.push(x.to_owned());
                    }*/
                    LangStringToken::LangToken(x) => {
                        seen_other_tags = true;
                        data.unknown.push(x.to_owned());
                    }
                    LangStringToken::KeyValueAttribute("class", value) => {
                        data.added_classes.push(value.to_owned());
                    }
                    /*LangStringToken::KeyValueAttribute(key, ..) if let Some(extra) = extra => {
                        extra
                            .error_invalid_codeblock_attr(format!("unsupported attribute `{key}`"));
                    }*/
                    LangStringToken::ClassAttribute(class) => {
                        data.added_classes.push(class.to_owned());
                    }
                    _ => {}
                }
            }
        };

        let mut tag_iter = TagIterator::new(string /*, extra*/);
        call(&mut tag_iter);

        // ignore-foo overrides ignore
        if !ignores.is_empty() {
            data.ignore = Ignore::Some(ignores);
        }

        data.rust &= !seen_custom_tag && (!seen_other_tags || seen_rust_tags) && !tag_iter.is_error;

        data
    }
}

/// Controls whether a line will be hidden or shown in HTML output.
///
/// All lines are used in documentation tests.
pub(crate) enum Line<'a> {
    Hidden(&'a str),
    Shown(Cow<'a, str>),
}

impl<'a> Line<'a> {
    fn for_html(self) -> Option<Cow<'a, str>> {
        match self {
            Line::Shown(l) => Some(l),
            Line::Hidden(_) => None,
        }
    }

    pub(crate) fn for_code(self) -> Cow<'a, str> {
        match self {
            Line::Shown(l) => l,
            Line::Hidden(l) => Cow::Borrowed(l),
        }
    }
}

/// This function is used to handle the "hidden lines" (ie starting with `#`) in
/// doctests. It also transforms `##` back into `#`.
// FIXME: There is a minor inconsistency here. For lines that start with ##, we
// have no easy way of removing a potential single space after the hashes, which
// is done in the single # case. This inconsistency seems okay, if non-ideal. In
// order to fix it we'd have to iterate to find the first non-# character, and
// then reallocate to remove it; which would make us return a String.
pub(crate) fn map_line(s: &str) -> Line<'_> {
    let trimmed = s.trim();
    if trimmed.starts_with("##") {
        Line::Shown(Cow::Owned(s.replacen("##", "#", 1)))
    } else if let Some(stripped) = trimmed.strip_prefix("# ") {
        // # text
        Line::Hidden(stripped)
    } else if trimmed == "#" {
        // We cannot handle '#text' because it could be #[attr].
        Line::Hidden("")
    } else {
        Line::Shown(Cow::Borrowed(s))
    }
}
