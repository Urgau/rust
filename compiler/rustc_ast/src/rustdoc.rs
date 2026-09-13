use std::range::Range;

use rustc_span::def_id::DefId;
use rustc_span::source_map::SourceMap;
use rustc_span::{DUMMY_SP, InnerSpan, Span, Symbol, sym};
use thin_vec::ThinVec;

use crate::AttrStyle;
use crate::attr::AttributeExt;
use crate::token::DocFragmentKind;
use crate::util::comments::beautify_doc_string;

/// A portion of documentation, extracted from a `#[doc]` attribute.
///
/// Each variant contains the line number within the complete doc-comment where the fragment
/// starts, as well as the Span where the corresponding doc comment or attribute is located.
///
/// Included files are kept separate from inline doc comments so that proper line-number
/// information can be given when a doctest fails. Sugared doc comments and "raw" doc comments are
/// kept separate because of issue #42760.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DocFragment {
    pub span: Span,
    /// The item this doc-comment came from.
    /// Used to determine the scope in which doc links in this fragment are resolved.
    /// Typically filled for reexport docs when they are merged into the docs of the
    /// original reexported item.
    /// If the id is not filled, which happens for the original reexported item, then
    /// it has to be taken from somewhere else during doc link resolution.
    pub item_id: Option<DefId>,
    pub doc: Symbol,
    pub kind: DocFragmentKind,
    pub indent: usize,
    /// Because we tamper with the spans context, this information cannot be correctly retrieved
    /// later on. So instead, we compute it and store it here.
    pub from_expansion: bool,
    pub style: AttrStyle,
}

/// Removes excess indentation on comments in order for the Markdown
/// to be parsed correctly. This is necessary because the convention for
/// writing documentation is to provide a space between the /// or //! marker
/// and the doc text, but Markdown is whitespace-sensitive. For example,
/// a block of text with four-space indentation is parsed as a code block,
/// so if we didn't unindent comments, these list items
///
/// /// A list:
/// ///
/// ///    - Foo
/// ///    - Bar
///
/// would be parsed as if they were in a code block, which is likely not what the user intended.
pub fn unindent_doc_fragments(docs: &mut [DocFragment]) {
    // `add` is used in case the most common sugared doc syntax is used ("/// "). The other
    // fragments kind's lines are never starting with a whitespace unless they are using some
    // markdown formatting requiring it. Therefore, if the doc block have a mix between the two,
    // we need to take into account the fact that the minimum indent minus one (to take this
    // whitespace into account).
    //
    // For example:
    //
    // /// hello!
    // #[doc = "another"]
    //
    // In this case, you want "hello! another" and not "hello!  another".
    let add = if docs.windows(2).any(|arr| arr[0].kind != arr[1].kind)
        && docs.iter().any(|d| d.kind.is_sugared())
    {
        // In case we have a mix of sugared doc comments and "raw" ones, we want the sugared one to
        // "decide" how much the minimum indent will be.
        1
    } else {
        0
    };

    // `min_indent` is used to know how much whitespaces from the start of each lines must be
    // removed. Example:
    //
    // ///     hello!
    // #[doc = "another"]
    //
    // In here, the `min_indent` is 1 (because non-sugared fragment are always counted with minimum
    // 1 whitespace), meaning that "hello!" will be considered a codeblock because it starts with 4
    // (5 - 1) whitespaces.
    let Some(min_indent) = docs
        .iter()
        .map(|fragment| {
            fragment
                .doc
                .as_str()
                .lines()
                .filter(|line| line.chars().any(|c| !c.is_whitespace()))
                .map(|line| {
                    // Compare against either space or tab, ignoring whether they are
                    // mixed or not.
                    let whitespace = line.chars().take_while(|c| *c == ' ' || *c == '\t').count();
                    whitespace + (if fragment.kind.is_sugared() { 0 } else { add })
                })
                .min()
                .unwrap_or(usize::MAX)
        })
        .min()
    else {
        return;
    };

    for fragment in docs {
        if fragment.doc == sym::empty {
            continue;
        }

        let indent = if !fragment.kind.is_sugared() && min_indent > 0 {
            min_indent - add
        } else {
            min_indent
        };

        fragment.indent = indent;
    }
}

/// The goal of this function is to apply the `DocFragment` transformation that is required when
/// transforming into the final Markdown, which is applying the computed indent to each line in
/// each doc fragment (a `DocFragment` can contain multiple lines in case of `#[doc = ""]`).
///
/// Note: remove the trailing newline where appropriate
pub fn add_doc_fragment(out: &mut String, frag: &DocFragment) {
    if frag.doc == sym::empty {
        out.push('\n');
        return;
    }
    let s = frag.doc.as_str();
    let mut iter = s.lines();

    while let Some(line) = iter.next() {
        if line.chars().any(|c| !c.is_whitespace()) {
            assert!(line.len() >= frag.indent);
            out.push_str(&line[frag.indent..]);
        } else {
            out.push_str(line);
        }
        out.push('\n');
    }
}

pub fn attrs_to_doc_fragments<'a, A: AttributeExt + Clone + 'a>(
    attrs: impl Iterator<Item = (&'a A, Option<DefId>)>,
    doc_only: bool,
) -> (Vec<DocFragment>, ThinVec<A>) {
    let (min_size, max_size) = attrs.size_hint();
    let size_hint = max_size.unwrap_or(min_size);
    let mut doc_fragments = Vec::with_capacity(size_hint);
    let mut other_attrs = ThinVec::<A>::with_capacity(if doc_only { 0 } else { size_hint });
    for (attr, item_id) in attrs {
        if let Some((doc_str, fragment_kind, attr_span)) = attr.doc_str_and_fragment_kind() {
            let doc = beautify_doc_string(doc_str, fragment_kind.comment_kind());
            let (span, from_expansion) = match fragment_kind {
                DocFragmentKind::Sugared(_) => (attr_span, attr_span.from_expansion()),
                DocFragmentKind::Raw(value_span) => {
                    (value_span.with_ctxt(attr_span.ctxt()), value_span.from_expansion())
                }
            };
            let fragment = DocFragment {
                span,
                doc,
                kind: fragment_kind,
                item_id,
                indent: 0,
                from_expansion,
                style: attr.doc_resolution_scope().unwrap(),
            };
            doc_fragments.push(fragment);
        } else if !doc_only {
            other_attrs.push(attr.clone());
        }
    }

    doc_fragments.shrink_to_fit();
    other_attrs.shrink_to_fit();

    unindent_doc_fragments(&mut doc_fragments);

    (doc_fragments, other_attrs)
}

/// Returns a span encompassing all the document fragments.
pub fn span_of_fragments(fragments: &[DocFragment]) -> Option<Span> {
    let (first_fragment, last_fragment) = match fragments {
        [] => return None,
        [first, .., last] => (first, last),
        [first] => (first, first),
    };
    if first_fragment.span == DUMMY_SP {
        return None;
    }
    Some(first_fragment.span.to(last_fragment.span))
}

// inner function used for unit testing
pub fn source_span_for_markdown_range_inner(
    map: &SourceMap,
    markdown: &str,
    md_range: &Range<usize>,
    fragments: &[DocFragment],
) -> Option<(Span, bool)> {
    use rustc_span::BytePos;

    if let &[fragment] = &fragments
        && !fragment.kind.is_sugared()
        && let Ok(snippet) = map.span_to_snippet(fragment.span)
        && snippet.trim_end() == markdown.trim_end()
        && let Ok(md_range_lo) = u32::try_from(md_range.start)
        && let Ok(md_range_hi) = u32::try_from(md_range.end)
    {
        // Single fragment with string that contains same bytes as doc.
        return Some((
            Span::new(
                fragment.span.lo() + rustc_span::BytePos(md_range_lo),
                fragment.span.lo() + rustc_span::BytePos(md_range_hi),
                fragment.span.ctxt(),
                fragment.span.parent(),
            ),
            fragment.from_expansion,
        ));
    }

    let is_all_sugared_doc = fragments.iter().all(|frag| frag.kind.is_sugared());

    if !is_all_sugared_doc {
        // This case ignores the markdown outside of the range so that it can
        // work in cases where the markdown is made from several different
        // doc fragments, but the target range does not span across multiple
        // fragments.
        let mut match_data = None;
        let pat = &markdown[md_range.clone()];
        // This heirustic doesn't make sense with a zero-sized range.
        if pat.is_empty() {
            return None;
        }
        let mut buffer = String::new();
        let mut offset = 0;
        for (i, fragment) in fragments.iter().enumerate() {
            // Ignore fragments outside of the specified range
            buffer.clear();
            add_doc_fragment(&mut buffer, fragment);
            let frag_start = offset;
            offset += buffer.len();
            let frag_end = offset;
            if !(frag_start <= md_range.start && md_range.end <= frag_end) {
                continue;
            }

            if let Ok(snippet) = map.span_to_snippet(fragment.span)
                && let Some(match_start) = snippet.find(pat)
            {
                // If there is either a match in a previous fragment, or
                // multiple matches in this fragment, there is ambiguity.
                // the snippet cannot be zero-sized, because it matches
                // the pattern, which is checked to not be zero sized.
                if match_data.is_none()
                    && !snippet.as_bytes()[match_start + 1..]
                        .windows(pat.len())
                        .any(|s| s == pat.as_bytes())
                {
                    match_data = Some((i, match_start));
                } else {
                    // Heuristic produced ambiguity, return nothing.
                    return None;
                }
            }
            break; // only one fragment can contain the range
        }
        if let Some((i, match_start)) = match_data {
            let fragment = &fragments[i];
            let sp = fragment.span;
            // we need to calculate the span start,
            // then use that in our calculations for the span end
            let lo = sp.lo() + BytePos(match_start as u32);
            return Some((
                sp.with_lo(lo).with_hi(lo + BytePos((md_range.end - md_range.start) as u32)),
                fragment.from_expansion,
            ));
        }
        return None;
    }

    let snippet = map.span_to_snippet(span_of_fragments(fragments)?).ok()?;

    let starting_line = markdown[..md_range.start].matches('\n').count();
    let ending_line = starting_line + markdown[md_range.start..md_range.end].matches('\n').count();

    // We use `split_terminator('\n')` instead of `lines()` when counting bytes so that we treat
    // CRLF and LF line endings the same way.
    let mut src_lines = snippet.split_terminator('\n');
    let md_lines = markdown.split_terminator('\n');

    // The number of bytes from the source span to the markdown span that are not part
    // of the markdown, like comment markers.
    let mut start_bytes = 0;
    let mut end_bytes = 0;

    let span_of_all_fragments: Span = span_of_fragments(fragments)?;

    let mut prev_lines_bytes = 0;
    'outer: for (line_no, md_line) in md_lines.enumerate() {
        loop {
            let source_line = src_lines.next()?;
            let source_line_len = u32::try_from(source_line.len()).unwrap();
            let source_line_span =
                span_of_all_fragments.split_at(prev_lines_bytes).1.split_at(source_line_len).0;
            let fragment = fragments
                .iter()
                // `source_line_span` might contain indentation that `fragment.span` doesn't contain
                .find(|fragment| fragment.span.overlaps(source_line_span));
            // Since we're counting bytes, `prev_line_bytes` includes the "\n".
            prev_lines_bytes += source_line_len + 1;
            if let Some(fragment) = fragment
                && let Some(offset) = source_line.find(md_line)
            {
                if fragment.span.lo() > source_line_span.lo()
                    && source_line
                        [..usize::try_from(fragment.span.lo().0 - source_line_span.lo().0).unwrap()]
                        .chars()
                        .any(|c| !c.is_whitespace())
                {
                    // Make sure anything between the start of this line and the fragment itself is just indentation.
                    // Because source_line is built by splitting the span that covers all fragments, this only finds
                    // characters *between* doc comments, not characters before or after doc comments.
                    //
                    //     1| /** doc */
                    //     2| #[inline] /** doc2 */
                    //        ^^^^^^^^^
                    //        | this
                    //
                    //     3| fn foo() {}
                    return None;
                }
                if fragment.span.hi() < source_line_span.hi()
                    && source_line
                        [usize::try_from(fragment.span.hi().0 - source_line_span.lo().0).unwrap()..]
                        .chars()
                        .any(|c| !c.is_whitespace())
                {
                    // Make sure anything between the start of this line and the fragment itself is just indentation.
                    // Because source_line is built by splitting the span that covers all fragments, this only finds
                    // characters *between* doc comments, not characters before or after doc comments.
                    //     1| /** doc */ #[inline]
                    //                   ^^^^^^^^^
                    //                   | this
                    //
                    //     2| /** doc2 */
                    //     3| fn foo() {}
                    return None;
                }
                if line_no == starting_line {
                    start_bytes += offset;

                    if starting_line == ending_line {
                        break 'outer;
                    }
                } else if line_no == ending_line {
                    end_bytes += offset;
                    break 'outer;
                } else if line_no < starting_line {
                    start_bytes += source_line.len() - md_line.len();
                } else {
                    end_bytes += source_line.len() - md_line.len();
                }
                break;
            } else {
                // Since this is a source line that doesn't include a markdown line,
                // we have to count it and its newline as non-markdown bytes.
                if line_no <= starting_line {
                    start_bytes += source_line.len() + 1;
                } else if source_line.chars().any(|c| !c.is_whitespace()) {
                    // We're past the first line, but haven't found the last line,
                    // but we found a non-empty non-markdown line.
                    // This could be an attribute, and we don't want a diagnostic
                    // suggesting to delete that attribute, so we return None to be safe.
                    //     1| /** doc */
                    //     2 | #[inline]
                    //          ^^^^^^^^^
                    //          | this
                    //     3| /** doc2 */
                    //     4| fn foo() {}
                    return None;
                } else {
                    end_bytes += source_line.len() + 1;
                }
            }
        }
    }

    let src_span = span_of_all_fragments.from_inner(InnerSpan::new(
        md_range.start + start_bytes,
        md_range.end + start_bytes + end_bytes,
    ));
    Some((
        src_span,
        fragments.iter().any(|frag| frag.span.overlaps(src_span) && frag.from_expansion),
    ))
}
