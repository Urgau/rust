use rustc_ast::ast;
use rustc_ast::token;
use rustc_ast::token::Delimiter;
use rustc_ast::tokenstream::DelimSpacing;
use rustc_ast::tokenstream::DelimSpan;
use rustc_ast::tokenstream::Spacing;
use rustc_ast::tokenstream::TokenStream;
use rustc_ast::tokenstream::TokenTree;
use rustc_span::Span;

use thin_vec::ThinVec;

fn meta_item_tokens(mi: &ast::MetaItem, out: &mut Vec<TokenTree>) {
    // path: a::b::c
    for (i, seg) in mi.path.segments.iter().enumerate() {
        if i > 0 {
            out.push(TokenTree::token_alone(token::PathSep, mi.span));
        }
        out.push(TokenTree::token_alone(
            token::Ident(seg.ident.name, token::IdentKind::Raw),
            seg.ident.span,
        ));
    }
    match &mi.kind {
        ast::MetaItemKind::Word => {}
        ast::MetaItemKind::NameValue(lit) => {
            out.push(TokenTree::token_alone(token::Eq, mi.span));
            out.push(TokenTree::token_alone(token::Literal(lit.as_token_lit()), lit.span));
        }
        ast::MetaItemKind::List(items) => {
            out.push(delimited_list(items, mi.span));
        }
    }
}

fn delimited_list(items: &[ast::MetaItemInner], span: Span) -> TokenTree {
    let mut tts = Vec::new();
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            tts.push(TokenTree::token_alone(token::Comma, span));
        }
        match item {
            ast::MetaItemInner::MetaItem(mi) => meta_item_tokens(mi, &mut tts),
            ast::MetaItemInner::Lit(lit) => {
                tts.push(TokenTree::token_alone(token::Literal(lit.as_token_lit()), lit.span));
            }
        }
    }
    TokenTree::Delimited(
        DelimSpan::from_single(span),
        DelimSpacing::new(Spacing::Alone, Spacing::Alone),
        Delimiter::Parenthesis,
        TokenStream::new(tts),
    )
}

pub(super) fn meta_item_to_attr_args(mi: &ast::MetaItem) -> ast::AttrArgs {
    match &mi.kind {
        ast::MetaItemKind::Word => ast::AttrArgs::Empty,
        ast::MetaItemKind::List(items) => {
            let TokenTree::Delimited(dspan, _, delim, tokens) = delimited_list(items, mi.span)
            else {
                unreachable!()
            };
            ast::AttrArgs::Delimited(ast::DelimArgs { dspan, delim, tokens })
        }
        ast::MetaItemKind::NameValue(lit) => ast::AttrArgs::Eq {
            eq_span: mi.span,
            expr: Box::new(ast::Expr {
                id: ast::DUMMY_NODE_ID,
                kind: ast::ExprKind::Lit(lit.as_token_lit()),
                span: lit.span,
                attrs: ThinVec::new(),
                tokens: None,
            }),
        },
    }
}
