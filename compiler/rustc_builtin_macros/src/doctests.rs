// Code that generates a test runner to run all the tests in a crate

use std::{iter, mem};

use rustc_ast as ast;
use rustc_ast::mut_visit::*;
use rustc_ast::{ModKind, join_path_idents};
//use rustc_ast_pretty::pprust;
use rustc_expand::base::{ExtCtxt, ResolverExpand};
use rustc_expand::expand::{AstFragment, ExpansionConfig};
use rustc_feature::Features;
use rustc_session::Session;
use rustc_span::hygiene::{AstPass, Transparency};
use rustc_span::{DUMMY_SP, Ident, RemapPathScopeComponents, Span, Symbol, sym};
use thin_vec::{ThinVec, thin_vec};

//use tracing::debug;
use crate::doctests::source::ParseSourceInfo;

mod parsing;
mod source;

struct ExpanderCtxt<'a> {
    ext_cx: ExtCtxt<'a>,
}

/// Traverse the crate, collecting all the test functions, eliding any
/// existing main functions, and synthesizing a main test harness
pub fn expand_doctests(
    krate: &mut ast::Crate,
    sess: &Session,
    features: &Features,
    resolver: &mut dyn ResolverExpand,
) {
    let econfig = ExpansionConfig::default(sym::test, features);
    let ext_cx = ExtCtxt::new(sess, econfig, resolver, None);

    let cx = ExpanderCtxt { ext_cx };

    DocTestsExpander { cx, expanded_doctests: Vec::new() }.visit_crate(krate);
}

struct DocTestsExpander<'a> {
    cx: ExpanderCtxt<'a>,
    expanded_doctests: Vec<Box<ast::Item>>,
}

impl<'a> MutVisitor for DocTestsExpander<'a> {
    fn visit_crate(&mut self, c: &mut ast::Crate) {
        let prev_tests = mem::take(&mut self.expanded_doctests);

        walk_crate(self, c);

        let mut doctests = mem::replace(&mut self.expanded_doctests, prev_tests);
        c.items.extend(doctests.drain(..));
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        let doc_strs: String =
            item.attrs.iter().filter_map(|a| a.doc_str()).fold(String::new(), |mut acc, s| {
                acc.push_str(s.as_str());
                acc.push('\n');
                acc
            });

        struct DocTestsCollector {
            tests: Vec<String>,
        }

        impl parsing::DocTestVisitor for DocTestsCollector {
            fn visit_test(
                &mut self,
                test: String,
                _config: parsing::LangString,
                _rel_line: parsing::MdRelLine,
                _code_mappings: Vec<parsing::CodeLineMapping>,
            ) {
                self.tests.push(test);
            }
        }

        let mut collector = DocTestsCollector { tests: Vec::new() };

        parsing::find_testable_code(
            &doc_strs,
            &mut collector,
            parsing::ErrorCodes::Yes, /*, None*/
        );

        for test_source in collector.tests {
            if let Ok(parse_info) = source::parse_source(&test_source, &None, None, item.span, &[])
            {
                let items = mk_unit_test(&mut self.cx, parse_info, item.span);
                let items = AstFragment::Items(items.into());
                let items =
                    self.cx.ext_cx.monotonic_expander().fully_expand_fragment(items).make_items();
                self.expanded_doctests.extend(items);
            }
        }

        // We don't want to recurse into anything other than mods, since
        // mods or tests inside of functions will break things
        if let ast::ItemKind::Mod(
            _,
            _,
            ModKind::Loaded(.., ast::ModSpans { inner_span: _span, .. }),
        ) = item.kind
        {
            let prev_tests = mem::take(&mut self.expanded_doctests);

            ast::mut_visit::walk_item(self, item);

            let mut doctests = mem::replace(&mut self.expanded_doctests, prev_tests);
            if let ast::ItemKind::Mod(_, _, ModKind::Loaded(ref mut items, _, _)) = item.kind {
                items.extend(doctests.drain(..));
            }
        } /* else {
        // But in those cases, we emit a lint to warn the user of these missing tests.
        ast::visit::walk_item(&mut InnerItemLinter { sess: self.cx.ext_cx.sess }, item);
        }*/
    }
}

fn mk_unit_test(
    exp_ctxt: &mut ExpanderCtxt<'_>,
    parse_info: ParseSourceInfo,
    item_span: Span,
) -> Vec<Box<ast::Item>> {
    let mut parsed_item = parse_info.parsed_item.unwrap();
    let cx = &mut exp_ctxt.ext_cx;

    let ast::ItemKind::Fn(ref mut fn_) = parsed_item.kind else {
        return vec![];
    };

    {
        let expn_id = cx.resolver.expansion_for_ast_pass(
            item_span,
            AstPass::TestHarness,
            &[],
            Some(ast::CRATE_NODE_ID),
        );
        fn_.ident.span = item_span.apply_mark(expn_id.to_expn_id(), Transparency::Opaque);
    }

    let expn_id = cx.resolver.expansion_for_ast_pass(
        DUMMY_SP,
        AstPass::TestHarness,
        &[sym::test, sym::rustc_attrs, sym::coverage_attribute],
        Some(ast::CRATE_NODE_ID),
    );

    let sp = item_span.apply_mark(expn_id.to_expn_id(), Transparency::Opaque);
    let ret_ty_sp = item_span.apply_mark(expn_id.to_expn_id(), Transparency::Opaque);
    let attr_sp = item_span.apply_mark(expn_id.to_expn_id(), Transparency::Opaque);

    let test_ident = Ident::new(sym::test, attr_sp);

    // creates test::$name
    let test_path = |name| cx.path(ret_ty_sp, vec![test_ident, Ident::from_str_and_span(name, sp)]);

    // creates test::ShouldPanic::$name
    let should_panic_path = |name| {
        cx.path(
            sp,
            vec![
                test_ident,
                Ident::from_str_and_span("ShouldPanic", sp),
                Ident::from_str_and_span(name, sp),
            ],
        )
    };

    // creates test::TestType::$name
    let test_type_path = |name| {
        cx.path(
            sp,
            vec![
                test_ident,
                Ident::from_str_and_span("TestType", sp),
                Ident::from_str_and_span(name, sp),
            ],
        )
    };

    // crates ::core::option::Option::None
    let option_none_path = || {
        cx.path(
            sp,
            vec![
                Ident::from_str_and_span("core", sp),
                Ident::from_str_and_span("option", sp),
                Ident::from_str_and_span("Option", sp),
                Ident::from_str_and_span("None", sp),
            ],
        )
    };

    // creates $name: $expr
    let field = |name, expr| cx.field_imm(sp, Ident::from_str_and_span(name, sp), expr);

    // Adds `#[coverage(off)]` to a closure, so it won't be instrumented in
    // `-Cinstrument-coverage` builds.
    // This requires `#[allow_internal_unstable(coverage_attribute)]` on the
    // corresponding macro declaration in `core::macros`.
    let coverage_off = |mut expr: Box<ast::Expr>| {
        expr.attrs.push(cx.attr_nested_word(sym::coverage, sym::off, sp));
        expr
    };

    let test_fn = cx.expr_call(
        sp,
        cx.expr_path(test_path("StaticTestFn")),
        thin_vec![
            // #[coverage(off)]
            // || {
            coverage_off(cx.lambda0(
                sp,
                // test::assert_test_result(
                cx.expr_call(
                    sp,
                    cx.expr_path(test_path("assert_test_result")),
                    thin_vec![
                        // $test_fn()
                        cx.expr_call(
                            ret_ty_sp,
                            cx.expr_path(cx.path(sp, vec![fn_.ident])),
                            ThinVec::new(),
                        ), // )
                    ],
                ), // }
            )), // )
        ],
    );

    let test_path_symbol = Symbol::intern(&item_path(
        // skip the name of the root module
        //TODO: &cx.current_expansion.module.mod_path[1..],
        &[],
        &fn_.ident,
    ));

    let location_info = get_location_info(cx, item_span);

    let mut test_const = cx.item(
        sp,
        thin_vec![
            // #[cfg(test)]
            //TODO: cx.attr_nested_word(sym::cfg, sym::test, attr_sp),
            // #[rustc_test_marker = "test_case_sort_key"]
            cx.attr_name_value_str(sym::rustc_test_marker, test_path_symbol, attr_sp),
            // #[doc(hidden)]
            cx.attr_nested_word(sym::doc, sym::hidden, attr_sp),
        ],
        // const $ident: test::TestDescAndFn =
        ast::ItemKind::Const(
            ast::ConstItem {
                defaultness: ast::Defaultness::Implicit,
                ident: Ident::new(fn_.ident.name, sp),
                generics: ast::Generics::default(),
                ty: cx.ty(sp, ast::TyKind::Path(None, test_path("TestDescAndFn"))),
                define_opaque: None,
                kind: ast::ConstItemKind::Body,
                // test::TestDescAndFn {
                body: Some(
                    cx.expr_struct(
                        sp,
                        test_path("TestDescAndFn"),
                        thin_vec![
                            // desc: test::TestDesc {
                            field(
                                "desc",
                                cx.expr_struct(
                                    sp,
                                    test_path("TestDesc"),
                                    thin_vec![
                                        // name: "path::to::test"
                                        field(
                                            "name",
                                            cx.expr_call(
                                                sp,
                                                cx.expr_path(test_path("StaticTestName")),
                                                thin_vec![cx.expr_str(sp, test_path_symbol)],
                                            ),
                                        ),
                                        // ignore: true | false
                                        field(
                                            "ignore",
                                            cx.expr_bool(sp, false /*should_ignore(&item)),*/)
                                        ),
                                        // ignore_message: Some("...") | None
                                        field(
                                            "ignore_message",
                                            /*if let Some(msg) = should_ignore_message(&item) {
                                                cx.expr_some(sp, cx.expr_str(sp, msg))
                                            } else {*/
                                            //cx.expr_none(sp), /*}*/
                                            cx.expr_path(option_none_path())
                                        ),
                                        // source_file: <relative_path_of_source_file>
                                        field("source_file", cx.expr_str(sp, location_info.0)),
                                        // start_line: start line of the test fn identifier.
                                        field("start_line", cx.expr_usize(sp, location_info.1)),
                                        // start_col: start column of the test fn identifier.
                                        field("start_col", cx.expr_usize(sp, location_info.2)),
                                        // end_line: end line of the test fn identifier.
                                        field("end_line", cx.expr_usize(sp, location_info.3)),
                                        // end_col: end column of the test fn identifier.
                                        field("end_col", cx.expr_usize(sp, location_info.4)),
                                        // compile_fail: true | false
                                        field("compile_fail", cx.expr_bool(sp, false)),
                                        // no_run: true | false
                                        field("no_run", cx.expr_bool(sp, false)),
                                        // should_panic: ...
                                        field(
                                            "should_panic", /*match should_panic(cx, &item) {
                                                            // test::ShouldPanic::No
                                                            ShouldPanic::No => {*/
                                            cx.expr_path(should_panic_path("No")) /*}
                                                                                      // test::ShouldPanic::Yes
                                                                                      ShouldPanic::Yes(None) => {
                                                                                          cx.expr_path(should_panic_path("Yes"))
                                                                                      }
                                                                                      // test::ShouldPanic::YesWithMessage("...")
                                                                                      ShouldPanic::Yes(Some(sym)) => cx.expr_call(
                                                                                          sp,
                                                                                          cx.expr_path(should_panic_path("YesWithMessage")),
                                                                                          thin_vec![cx.expr_str(sp, sym)],
                                                                                      ),
                                                                                  },*/
                                        ),
                                        // test_type: ...
                                        field(
                                            "test_type",
                                            cx.expr_path(test_type_path("UnitTest"))
                                        ),
                                        // },
                                    ],
                                ),
                            ),
                            // testfn: test::StaticTestFn(...) | test::StaticBenchFn(...)
                            field("testfn", test_fn), // }
                        ],
                    ), // }
                ),
            }
            .into(),
        ),
    );
    test_const.vis.kind = ast::VisibilityKind::Public;

    // extern crate test
    let test_extern =
        cx.item(sp, ast::AttrVec::new(), ast::ItemKind::ExternCrate(None, test_ident));

    //debug!("synthetic test extern:\n{}\n", pprust::item_to_string(&test_extern));
    //debug!("synthetic test item:\n{}\n", pprust::item_to_string(&test_const));
    //debug!("synthetic parsed item:\n{}\n", pprust::item_to_string(&parsed_item));

    // this feels like a hack, but removing it makes the resolver explode as it
    // uses this id for expension but fails to find already expanded
    //cx.current_expansion.id = LocalExpnId::ZERO;

    vec![
        // Access to libtest under a hygienic name
        test_extern,
        // The generated test case
        test_const,
        // The doctest
        parsed_item,
    ]
}

fn item_path(mod_path: &[Ident], item_ident: &Ident) -> String {
    join_path_idents(mod_path.iter().chain(iter::once(item_ident)))
}

fn get_location_info(cx: &ExtCtxt<'_>, span: Span) -> (Symbol, usize, usize, usize, usize) {
    let (source_file, lo_line, lo_col, hi_line, hi_col) =
        cx.sess.source_map().span_to_location_info(span);

    let file_name = match source_file {
        Some(sf) => sf.name.display(RemapPathScopeComponents::MACRO).to_string(),
        None => "no-location".to_string(),
    };

    (Symbol::intern(&file_name), lo_line, lo_col, hi_line, hi_col)
}
