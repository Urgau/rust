// Code that generates a test runner to run all the tests in a crate

use std::{iter, mem};

use rustc_ast as ast;
use rustc_ast::mut_visit::*;
use rustc_ast::{ModKind, NodeId, join_path_idents};
use rustc_ast_pretty::pprust;
use rustc_expand::base::{ExtCtxt, ResolverExpand};
use rustc_expand::expand::{AstFragment, ExpansionConfig};
use rustc_feature::Features;
use rustc_session::Session;
use rustc_span::hygiene::{AstPass, Transparency};
use rustc_span::{DUMMY_SP, Ident, RemapPathScopeComponents, Span, Symbol, kw, sym};
use thin_vec::{ThinVec, thin_vec};
use tracing::debug;

use crate::doctests::source::ParseSourceInfo;

mod parsing;
mod source;

/// Traverse the crate, collecting all the test functions, eliding any
/// existing main functions, and synthesizing a main test harness
pub fn expand_doctests(
    krate: &mut ast::Crate,
    crate_name: Symbol,
    sess: &Session,
    features: &Features,
    resolver: &mut dyn ResolverExpand,
) {
    let econfig = ExpansionConfig::default(sym::test, features);
    let ext_cx = ExtCtxt::new(sess, econfig, resolver, None);

    DocTestsExpander {
        ext_cx,
        crate_name,
        expanded_doctests: Vec::new(),
        mod_path: Vec::new(),
        parent_node_id: ast::CRATE_NODE_ID,
    }
    .visit_crate(krate);
}

struct DocTestsExpander<'a> {
    ext_cx: ExtCtxt<'a>,
    crate_name: Symbol,
    expanded_doctests: Vec<Box<ast::Item>>,
    mod_path: Vec<Ident>,
    parent_node_id: NodeId,
}

struct CollectedDocTest {
    source: String,
    config: parsing::LangString,
    #[allow(dead_code)]
    rel_line: parsing::MdRelLine,
    code_mappings: Vec<parsing::CodeLineMapping>,
}

impl<'a> MutVisitor for DocTestsExpander<'a> {
    fn visit_crate(&mut self, c: &mut ast::Crate) {
        let prev_tests = mem::take(&mut self.expanded_doctests);

        walk_crate(self, c);

        let mut doctests = mem::replace(&mut self.expanded_doctests, prev_tests);
        c.items.extend(doctests.drain(..));
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        let (doc_fragments, _attrs) = rustc_ast::rustdoc::attrs_to_doc_fragments(
            item.attrs.iter().map(|attr| (attr, None)),
            true,
        );

        let mut doc_strs = String::new();
        for frag in &doc_fragments {
            rustc_ast::rustdoc::add_doc_fragment(&mut doc_strs, frag);
        }

        struct DocTestsCollector {
            tests: Vec<CollectedDocTest>,
        }

        impl parsing::DocTestVisitor for DocTestsCollector {
            fn visit_test(
                &mut self,
                source: String,
                config: parsing::LangString,
                rel_line: parsing::MdRelLine,
                code_mappings: Vec<parsing::CodeLineMapping>,
            ) {
                debug!(?source, ?config, ?rel_line, ?code_mappings);
                self.tests.push(CollectedDocTest { source, config, rel_line, code_mappings });
            }
        }

        let mut collector = DocTestsCollector { tests: Vec::new() };

        parsing::find_testable_code(
            &doc_strs,
            &mut collector,
            parsing::ErrorCodes::Yes,
            Some(&parsing::ExtraInfo::new(self.ext_cx.source_map(), Some(&doc_fragments))),
        );

        let has_more_than_one = collector.tests.len() > 1;
        let item_ident = item.kind.ident();

        for (doctest_i, collected_doctest) in
            collector.tests.into_iter().enumerate().filter(|(_, d)| {
                // don't take into account non-Rust doctests, as well as compile_fail and standalone ones
                d.config.rust && !d.config.compile_fail && !d.config.standalone_crate
            })
        {
            let Ok(parse_info) = source::parse_source(
                &collected_doctest.source,
                &self.ext_cx.sess.psess,
                &Some(self.crate_name),
                None,
                item.span,
                &collected_doctest.code_mappings,
            ) else {
                continue;
            };

            let name = if let Some(ident) = &item_ident {
                if has_more_than_one {
                    Symbol::intern(&format!("{}_{doctest_i}", ident.name.as_str()))
                } else {
                    ident.name
                }
            } else {
                sym::f
            };

            let item = mk_unit_test(self, collected_doctest, parse_info, item.span, name);
            let items = AstFragment::Items(smallvec::smallvec![item]);
            let items = self.ext_cx.monotonic_expander().fully_expand_fragment(items).make_items();
            self.expanded_doctests.extend(items);
        }

        // We don't want to recurse into anything other than mods, since
        // mods or tests inside of functions will break things
        if let ast::ItemKind::Mod(
            _,
            mod_ident,
            ModKind::Loaded(.., ast::ModSpans { inner_span: _span, .. }),
        ) = item.kind
        {
            //let prev_tests = mem::take(&mut self.expanded_doctests);
            let prev_parent_node_id = mem::replace(&mut self.parent_node_id, item.id);
            self.mod_path.push(mod_ident.clone());

            ast::mut_visit::walk_item(self, item);

            self.mod_path.pop();
            self.parent_node_id = prev_parent_node_id;

            /*
            TODO: we can't just add the doctests here, we need tell the resolver that we are
            adding the items here, figure-out how, otherwise all the imports are messed-up
            let mut doctests = mem::replace(&mut self.expanded_doctests, prev_tests);
            if let ast::ItemKind::Mod(_, _, ModKind::Loaded(ref mut items, _, _)) = item.kind {
                items.extend(doctests.drain(..));
            }
            */
        } /* else {
        // But in those cases, we emit a lint to warn the user of these missing tests.
        ast::visit::walk_item(&mut InnerItemLinter { sess: self.cx.ext_cx.sess }, item);
        }*/
    }
}

fn mk_unit_test(
    exp: &mut DocTestsExpander<'_>,
    collected_doctest: CollectedDocTest,
    parse_info: ParseSourceInfo,
    item_span: Span,
    doctest_name: Symbol,
) -> Box<ast::Item> {
    let cx = &mut exp.ext_cx;

    let mut doctest_mod_items = ThinVec::new();

    if !parse_info.already_has_extern_crate {
        let extern_crate_self = cx.item(
            item_span,
            ast::AttrVec::new(),
            ast::ItemKind::ExternCrate(Some(kw::SelfLower), Ident::new(exp.crate_name, item_span)),
        );

        doctest_mod_items.push(extern_crate_self);
    }

    let doctest_entry_point_ident = if parse_info.has_main_fn {
        for stmt in parse_info.stmts {
            match stmt.kind {
                ast::StmtKind::Item(item) => {
                    doctest_mod_items.push(item);
                }
                ast::StmtKind::MacCall(mac_stmt) => {
                    let item =
                        cx.item(item_span, mac_stmt.attrs, ast::ItemKind::MacCall(mac_stmt.mac));

                    doctest_mod_items.push(item);
                }
                _ => unreachable!(),
            }
        }

        Ident::new(sym::main, item_span)
    } else {
        let expn_id = cx.resolver.expansion_for_ast_pass(
            item_span,
            AstPass::TestHarness,
            &[],
            Some(exp.parent_node_id),
        );

        let entrypoint_sp = item_span.apply_mark(expn_id.to_expn_id(), Transparency::Opaque);

        // creates fn() -> ()
        let ret_ty = cx.ty(entrypoint_sp, ast::TyKind::Tup(ThinVec::new()));
        let decl = cx.fn_decl(ThinVec::new(), ast::FnRetTy::Ty(ret_ty));
        let sig = ast::FnSig { decl, header: ast::FnHeader::default(), span: entrypoint_sp };

        // creates fn doctest() -> () { ... }
        let entrypoint_ident = Ident::new(sym::doctest, entrypoint_sp);
        let entrypoint = cx.item(
            entrypoint_sp,
            ast::AttrVec::new(),
            ast::ItemKind::Fn(Box::new(ast::Fn {
                defaultness: ast::Defaultness::Implicit,
                ident: entrypoint_ident,
                generics: ast::Generics::default(),
                contract: None,
                define_opaque: None,
                eii_impl: None,
                sig,
                body: Some(cx.block(entrypoint_sp, parse_info.stmts)),
            })),
        );

        doctest_mod_items.push(entrypoint);

        entrypoint_ident
    };

    let expn_id = cx.resolver.expansion_for_ast_pass(
        DUMMY_SP,
        AstPass::TestHarness,
        &[sym::test, sym::rustc_attrs, sym::coverage_attribute],
        Some(exp.parent_node_id),
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
                            cx.expr_path(cx.path(sp, vec![doctest_entry_point_ident])),
                            ThinVec::new(),
                        ), // )
                    ],
                ), // }
            )), // )
        ],
    );

    let test_path_symbol =
        Symbol::intern(&item_path(&exp.mod_path, &Ident::new(doctest_name, DUMMY_SP)));

    let location_info = get_location_info(cx, item_span);

    let mut test_const = cx.item(
        sp,
        thin_vec![
            // #[cfg(doctest)]
            //TODO: cx.attr_nested_word(sym::cfg, sym::doctest, attr_sp),
            // #[rustc_test_marker = "test_case_sort_key"]
            cx.attr_name_value_str(sym::rustc_test_marker, test_path_symbol, attr_sp),
            // #[doc(hidden)]
            cx.attr_nested_word(sym::doc, sym::hidden, attr_sp),
        ],
        // const $ident: test::TestDescAndFn =
        ast::ItemKind::Const(
            ast::ConstItem {
                defaultness: ast::Defaultness::Implicit,
                ident: Ident::new(doctest_entry_point_ident.name, sp),
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
                                            // TODO: use collected_doctest.config.ignore
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
                                        field(
                                            "no_run",
                                            cx.expr_bool(sp, collected_doctest.config.no_run)
                                        ),
                                        // should_panic: ...
                                        field(
                                            "should_panic",
                                            cx.expr_path(should_panic_path(
                                                if collected_doctest.config.should_panic {
                                                    "Yes"
                                                } else {
                                                    "No"
                                                }
                                            ))
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

    //debug!("synthetic parsed item:\n{}\n", pprust::item_to_string(&mod_));
    //debug!("synthetic test extern:\n{}\n", pprust::item_to_string(&test_extern));
    //debug!("synthetic test item:\n{}\n", pprust::item_to_string(&test_const));

    // Access to libtest under a hygienic name
    doctest_mod_items.push(test_extern);

    // The generated test case
    doctest_mod_items.push(test_const);

    let mod_ = cx.item(
        sp,
        ast::AttrVec::new(),
        ast::ItemKind::Mod(
            rustc_ast::Safety::Default,
            Ident::new(sym::doctest, sp),
            ast::ModKind::Loaded(
                doctest_mod_items,
                ast::Inline::Yes,
                ast::ModSpans { inner_span: sp, inject_use_span: sp },
            ),
        ),
    );

    debug!("synthetic test extern:\n{}\n", pprust::item_to_string(&mod_));
    mod_
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
