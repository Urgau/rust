use rustc_ast::token::{Delimiter, TokenKind};
use rustc_ast::tokenstream::TokenTree;
use rustc_ast::{self as ast, AttrStyle, HasAttrs, Stmt, StmtKind};
use rustc_errors::DiagCtxtHandle;
use rustc_parse::lexer::StripTokens;
use rustc_parse::new_parser_from_source_str_with_syntax_context;
use rustc_session::parse::ParseSess;
use rustc_span::source_map::SourceMap;
use rustc_span::symbol::sym;
use rustc_span::{FileName, InnerSpan, Span, Symbol, SyntaxContext, kw};
use thin_vec::ThinVec;

use crate::doctests::parsing::CodeLineMapping;

#[derive(Default, Debug)]
pub(super) struct ParseSourceInfo {
    pub(super) stmts: ThinVec<Stmt>,
    pub(super) has_main_fn: bool,
    pub(super) already_has_extern_crate: bool,
    //pub(super) supports_color: bool,
    pub(super) has_global_allocator: bool,
    pub(super) has_macro_def: bool,
    pub(super) everything_else: String,
    pub(super) crates: String,
    /// Inner attributes (`#![...]`) from the source that have to be put at the crate level.
    pub(super) crate_attrs: ast::AttrVec,
    /// Inner attributes (`#![...]`) from the source that can be put into a module and therefore do
    /// not inhibit merging: even in the merged test, the attributes can be isolated to the test.
    pub(super) module_attrs: ast::AttrVec,
}

const DOCTEST_CODE_WRAPPER: &str = "fn f(){\n";

pub(super) fn parse_source(
    source: &str,
    psess: &ParseSess,
    crate_name: &Option<Symbol>,
    parent_dcx: Option<DiagCtxtHandle<'_>>,
    span: Span,
    syntax_context: SyntaxContext,
    code_mappings: &[CodeLineMapping],
) -> Result<ParseSourceInfo, ()> {
    let mut info =
        ParseSourceInfo { already_has_extern_crate: crate_name.is_none(), ..Default::default() };

    let wrapped_source = format!("{DOCTEST_CODE_WRAPPER}{source}\n}}");

    let filename = FileName::anon_source_code(&wrapped_source);

    // Don't strip any tokens; it wouldn't matter anyway because the source is wrapped in a function.
    let mut parser = match new_parser_from_source_str_with_syntax_context(
        psess,
        filename,
        wrapped_source,
        StripTokens::Nothing,
        syntax_context,
    ) {
        Ok(p) => p,
        Err(errs) => {
            errs.into_iter().for_each(|err| err.cancel());
            //reset_error_count(&psess);
            return Err(());
        }
    };

    fn push_to_s(s: &mut String, source: &str, span: rustc_span::Span, prev_span_hi: &mut usize) {
        let extra_len = DOCTEST_CODE_WRAPPER.len();
        // We need to shift by the length of `DOCTEST_CODE_WRAPPER` because we
        // added it at the beginning of the source we provided to the parser.
        let mut hi = span.hi().0 as usize - extra_len;
        if hi > source.len() {
            hi = source.len();
        }
        s.push_str(&source[*prev_span_hi..hi]);
        *prev_span_hi = hi;
    }

    fn check_item(
        item: &ast::Item,
        info: &mut ParseSourceInfo,
        crate_name: &Option<Symbol>,
    ) -> bool {
        let mut is_extern_crate = false;
        if !info.has_global_allocator
            && item.attrs.iter().any(|attr| attr.has_name(sym::global_allocator))
        {
            info.has_global_allocator = true;
        }
        match item.kind {
            ast::ItemKind::Fn(ref fn_item) if !info.has_main_fn => {
                if fn_item.ident.name == sym::main {
                    info.has_main_fn = true;
                }
            }
            ast::ItemKind::ExternCrate(original, ident) => {
                is_extern_crate = true;
                if !info.already_has_extern_crate
                    && let Some(crate_name) = crate_name
                {
                    info.already_has_extern_crate = match original {
                        Some(name) => name == *crate_name,
                        None => ident.name == *crate_name,
                    };
                }
            }
            ast::ItemKind::MacroDef(..) => {
                info.has_macro_def = true;
            }
            _ => {}
        }
        is_extern_crate
    }

    let mut prev_span_hi = 0;
    let not_crate_attrs = &[sym::forbid, sym::allow, sym::warn, sym::deny, sym::expect];
    let parsed = parser.parse_item(
        rustc_parse::parser::ForceCollect::No,
        rustc_parse::parser::AllowConstBlockItems::No,
    );

    let result = match parsed {
        Ok(Some(ast::Item {
            attrs,
            kind: ast::ItemKind::Fn(ast::Fn { body: Some(body), .. }),
            ..
        })) => {
            for attr in attrs {
                if attr.style == AttrStyle::Outer || attr.has_any_name(not_crate_attrs) {
                    // There is one exception to these attributes:
                    // `#![allow(internal_features)]`. If this attribute is used, we need to
                    // consider it only as a crate-level attribute.
                    if attr.has_name(sym::allow)
                        && let Some(list) = attr.meta_item_list()
                        && list.iter().any(|sub_attr| {
                            sub_attr.has_name(sym::internal_features)
                                || sub_attr.has_name(sym::incomplete_features)
                        })
                    {
                        info.crate_attrs.push(attr);
                    } else {
                        info.module_attrs.push(attr);
                    }
                } else {
                    info.crate_attrs.push(attr);
                }
            }
            let mut has_non_items = false;
            let mut first_non_item_span = None;
            for stmt in &body.stmts {
                let mut is_extern_crate = false;
                match stmt.kind {
                    StmtKind::Item(ref item) => {
                        is_extern_crate = check_item(item, &mut info, crate_name);
                    }
                    // We assume that the macro calls will expand to item(s) even though they could
                    // expand to statements and expressions.
                    StmtKind::MacCall(ref mac_call) => {
                        if !info.has_main_fn {
                            // For backward compatibility, we look for the token sequence `fn main(…)`
                            // in the macro input (!) to crudely detect main functions "masked by a
                            // wrapper macro". For the record, this is a horrible heuristic!
                            // See <https://github.com/rust-lang/rust/issues/56898>.
                            let mut iter = mac_call.mac.args.tokens.iter();
                            while let Some(token) = iter.next() {
                                if let TokenTree::Token(token, _) = token
                                    && let TokenKind::Ident(kw::Fn, _) = token.kind
                                    && let Some(TokenTree::Token(ident, _)) = iter.peek()
                                    && let TokenKind::Ident(sym::main, _) = ident.kind
                                    && let Some(TokenTree::Delimited(.., Delimiter::Parenthesis, _)) = {
                                        iter.next();
                                        iter.peek()
                                    }
                                {
                                    info.has_main_fn = true;
                                    break;
                                }
                            }
                        }
                    }
                    StmtKind::Expr(ref expr) => {
                        if matches!(expr.kind, ast::ExprKind::Err(_)) {
                            //reset_error_count(&psess);
                            return Err(());
                        }
                        has_non_items = true;
                        first_non_item_span.get_or_insert(stmt.span);
                    }
                    StmtKind::Let(_) | StmtKind::Semi(_) | StmtKind::Empty => {
                        has_non_items = true;
                        first_non_item_span.get_or_insert(stmt.span);
                    }
                }

                // Weirdly enough, the `Stmt` span doesn't include its attributes, so we need to
                // tweak the span to include the attributes as well.
                let mut span = stmt.span;
                if let Some(attr) =
                    stmt.kind.attrs().iter().find(|attr| attr.style == AttrStyle::Outer)
                {
                    span = span.with_lo(attr.span.lo());
                }
                if info.everything_else.is_empty()
                    && (!info.module_attrs.is_empty() || !info.crate_attrs.is_empty())
                {
                    // To keep the doctest code "as close as possible" to the original, we insert
                    // all the code located between this new span and the previous span which
                    // might contain code comments and backlines.
                    push_to_s(&mut info.crates, source, span.shrink_to_lo(), &mut prev_span_hi);
                }
                if !is_extern_crate {
                    push_to_s(&mut info.everything_else, source, span, &mut prev_span_hi);
                } else {
                    push_to_s(&mut info.crates, source, span, &mut prev_span_hi);
                }
            }
            info.stmts = body.stmts;
            if has_non_items {
                let warning_span = first_non_item_span
                    .and_then(|span| {
                        span_in_doctest_source(span, psess.source_map(), code_mappings)
                    })
                    .unwrap_or(span);
                if info.has_main_fn
                    && let Some(dcx) = parent_dcx
                    && !warning_span.is_dummy()
                {
                    dcx.span_warn(
                        warning_span,
                        "the `main` function of this doctest won't be run as it contains \
                         expressions at the top level, meaning that the whole doctest code will be \
                         wrapped in a function",
                    );
                }
                info.has_main_fn = false;
            }
            Ok(info)
        }
        Err(e) => {
            e.emit();
            //e.cancel();
            Err(())
        }
        _ => Err(()),
    };

    //reset_error_count(&psess);
    result
}

pub(crate) fn span_in_doctest_source(
    span: Span,
    source_map: &SourceMap,
    code_mappings: &[CodeLineMapping],
) -> Option<Span> {
    const EXTRA_LEN: usize = DOCTEST_CODE_WRAPPER.len();

    let lo = source_map.lookup_source_file(span.lo()).relative_position(span.lo());
    let hi = source_map.lookup_source_file(span.hi()).relative_position(span.hi());

    let lo = (lo.0 as usize).checked_sub(EXTRA_LEN)?;
    let hi = (hi.0 as usize).checked_sub(EXTRA_LEN)?;

    if hi < lo {
        return None;
    }
    code_mappings.iter().find_map(|mapping| {
        if mapping.generated.start <= lo && hi <= mapping.generated.end {
            let start = lo - mapping.generated.start;
            let end = hi - mapping.generated.start;
            Some(mapping.original.from_inner(InnerSpan::new(start, end)))
        } else {
            None
        }
    })
}
