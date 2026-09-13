use itertools::Itertools;
use rustc_ast::ast;
use rustc_ast::rustdoc::pulldown_cmark::{
    BrokenLink, BrokenLinkCallback, CowStr, Event, LinkType, Parser, Tag,
};
pub use rustc_ast::rustdoc::*;
use rustc_data_structures::unord::UnordSet;

/// Simplified version of the corresponding function in rustdoc.
fn preprocess_link(link: &str) -> Box<str> {
    // IMPORTANT: To be kept in sync with the corresponding function in rustdoc.
    // Namely, whenever the rustdoc function returns a successful result for a given input,
    // this function *MUST* return a link that's equal to `PreprocessingInfo.path_str`!

    let link = link.replace('`', "");
    let link = link.split('#').next().unwrap();
    let link = link.trim();
    let link = link.split_once('@').map_or(link, |(_, rhs)| rhs);
    let link = link.trim_suffix("()");
    let link = link.trim_suffix("{}");
    let link = link.trim_suffix("[]");
    let link = if link != "!" { link.trim_suffix('!') } else { link };
    let link = link.trim();
    strip_generics_from_path(link).unwrap_or_else(|_| link.into())
}

/// Simplified version of `preprocessed_markdown_links` from rustdoc.
/// Must return at least the same links as it, but may add some more links on top of that.
pub(crate) fn attrs_to_preprocessed_links(attrs: &[ast::Attribute]) -> Vec<Box<str>> {
    let (doc_fragments, other_attrs) =
        attrs_to_doc_fragments(attrs.iter().map(|attr| (attr, None)), false);
    let doc = prepare_to_doc_link_resolution(&doc_fragments).into_values().next();
    let mut links = doc.as_deref().map(parse_links).unwrap_or_default();

    for attr in other_attrs {
        if let Some(note) = attr.deprecation_note() {
            links.extend(parse_links(note.as_str()));
        }
    }

    links
}

/// Similar version of `markdown_links` from rustdoc.
/// This will collect destination links and display text if exists.
fn parse_links<'md>(doc: &'md str) -> Vec<Box<str>> {
    let mut broken_link_callback = |link: BrokenLink<'md>| Some((link.reference, "".into()));
    let mut event_iter = Parser::new_with_broken_link_callback(
        doc,
        main_body_opts(),
        Some(&mut broken_link_callback),
    );
    let mut links = Vec::new();

    let mut refids = UnordSet::default();

    while let Some(event) = event_iter.next() {
        match event {
            Event::Start(Tag::Link { link_type, dest_url, title: _, id })
                if may_be_doc_link(link_type) =>
            {
                if matches!(
                    link_type,
                    LinkType::Inline
                        | LinkType::ReferenceUnknown
                        | LinkType::Reference
                        | LinkType::Shortcut
                        | LinkType::ShortcutUnknown
                ) {
                    if let Some(display_text) = collect_link_data(&mut event_iter) {
                        links.push(display_text);
                    }
                }
                if matches!(
                    link_type,
                    LinkType::Reference | LinkType::Shortcut | LinkType::Collapsed
                ) {
                    refids.insert(id);
                }

                links.push(preprocess_link(&dest_url));
            }
            _ => {}
        }
    }

    for (label, refdef) in event_iter.reference_definitions().iter().sorted_by_key(|x| x.0) {
        if !refids.contains(label) {
            links.push(preprocess_link(&refdef.dest));
        }
    }

    links
}

/// Collects additional data of link.
fn collect_link_data<'input, F: BrokenLinkCallback<'input>>(
    event_iter: &mut Parser<'input, F>,
) -> Option<Box<str>> {
    let mut display_text: Option<String> = None;
    let mut append_text = |text: CowStr<'_>| {
        if let Some(display_text) = &mut display_text {
            display_text.push_str(&text);
        } else {
            display_text = Some(text.to_string());
        }
    };

    while let Some(event) = event_iter.next() {
        match event {
            Event::Text(text) => {
                append_text(text);
            }
            Event::Code(code) => {
                append_text(code);
            }
            Event::End(_) => {
                break;
            }
            _ => {}
        }
    }

    display_text.map(String::into_boxed_str)
}
