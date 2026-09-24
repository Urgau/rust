// Code that generates a test runner to run all the tests in a crate

use std::path::Path;
use std::{iter, mem};

use rustc_ast::mut_visit::*;
use rustc_ast::{self as ast, BinOpKind, ModKind, NodeId, UnOp, join_path_idents, token};
use rustc_attr_ir::target::Target;
use rustc_attr_parsing::AttributeParser;
use rustc_expand::base::{ExtCtxt, ResolverExpand};
use rustc_expand::expand::{AstFragment, ExpansionConfig};
use rustc_feature::Features;
use rustc_session::Session;
use rustc_span::hygiene::{AstPass, Transparency};
use rustc_span::source_map::SourceMap;
use rustc_span::{DUMMY_SP, Ident, RemapPathScopeComponents, Span, Symbol, SyntaxContext, kw, sym};
use thin_vec::{ThinVec, thin_vec};
use tracing::debug;

use crate::doctests::source::ParseSourceInfo;

mod make;
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
        expanded_doctests_crate: Vec::new(),
        mod_path: Vec::new(),
        parent_node_id: ast::CRATE_NODE_ID,
    }
    .visit_crate(krate);
}

struct DocTestsExpander<'a> {
    ext_cx: ExtCtxt<'a>,
    crate_name: Symbol,
    expanded_doctests: Vec<Box<ast::Item>>,
    expanded_doctests_crate: Vec<Box<ast::Item>>,
    mod_path: Vec<Ident>,
    parent_node_id: NodeId,
}

struct CollectedDocTest {
    source: String,
    config: parsing::LangString,
    rel_line: parsing::MdRelLine,
    code_mappings: Vec<parsing::CodeLineMapping>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum ExpandMode {
    DefSite,
    CrateRoot,
    StandaloneCrate,
}

impl<'a> MutVisitor for DocTestsExpander<'a> {
    fn visit_crate(&mut self, c: &mut ast::Crate) {
        let prev_tests = mem::take(&mut self.expanded_doctests);

        walk_crate(self, c);

        let mut doctests = mem::replace(&mut self.expanded_doctests, prev_tests);
        c.items.extend(doctests.drain(..));
        c.items.extend(self.expanded_doctests_crate.drain(..));
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

        struct DocTestSpansAdjustor<'doc> {
            source_map: &'doc SourceMap,
            syntax_context: SyntaxContext,
            code_mappings: &'doc [parsing::CodeLineMapping],
        }

        impl MutVisitor for DocTestSpansAdjustor<'_> {
            fn visit_span(&mut self, sp: &mut Span) {
                if let Some(orig_sp) =
                    source::span_in_doctest_source(*sp, &self.source_map, &self.code_mappings)
                {
                    // we need to apply to syntax context, otherwise the edition is going to revert to
                    // the global one, not the one specified in the doctest
                    *sp = orig_sp.with_ctxt(self.syntax_context);
                }
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

        for collected_doctest in collector.tests.into_iter().filter(|d| {
            // don't take into account non-Rust doctests, as well as compile_fail and standalone ones
            d.config.rust /*&& !d.config.compile_fail && !d.config.standalone_crate*/
        }) {
            let expn_id = self.ext_cx.resolver.expansion_for_ast_pass(
                item.span,
                AstPass::DocTests,
                Some(collected_doctest.config.edition.unwrap_or(item.span.edition())),
                &[],
                Some(self.parent_node_id),
            );
            let syntax_context =
                SyntaxContext::root().apply_mark(expn_id.to_expn_id(), Transparency::Opaque);

            let Ok(mut parse_info) = source::parse_source(
                &collected_doctest.source,
                &self.ext_cx.sess.psess,
                &Some(self.crate_name),
                None,
                item.span,
                syntax_context,
                &collected_doctest.code_mappings,
            ) else {
                continue;
            };

            let name = if let Some(ident) = &item_ident {
                if has_more_than_one {
                    Symbol::intern(&format!(
                        "{}_{}",
                        ident.name.as_str(),
                        collected_doctest.rel_line.offset()
                    ))
                } else {
                    Symbol::intern(&format!("{}", ident.name.as_str()))
                }
            } else {
                sym::f
            };

            // This unfortunatly doesn't take into account macros input (like LazyAttrTokenStream)
            // we either need a new system or make the parsing create the right span from the start
            let mut span_adjustor = DocTestSpansAdjustor {
                syntax_context,
                source_map: self.ext_cx.source_map(),
                code_mappings: &collected_doctest.code_mappings,
            };
            for stmt in &mut parse_info.stmts {
                span_adjustor.visit_stmt(stmt);
            }
            for attr in &mut parse_info.attrs {
                span_adjustor.visit_attribute(attr);
            }

            let has_incompatible_fn_attrs = parse_info.attrs.iter().any(|attr| {
                AttributeParser::is_maybe_allowed_at_level(attr, Target::Fn) != Some(true)
                    && ![sym::allow, sym::deny, sym::warn, sym::forbid].contains(&attr.path()[0])
            });

            let expand_mode = if collected_doctest.config.compile_fail
                || collected_doctest.config.standalone_crate
                || has_incompatible_fn_attrs
            {
                ExpandMode::StandaloneCrate
            } else if collected_doctest.config.unknown.contains(&"private".to_string()) {
                ExpandMode::DefSite
            } else {
                ExpandMode::CrateRoot
            };

            let items = mk_unit_test(
                self,
                collected_doctest,
                parse_info,
                item.span,
                name,
                expand_mode,
                syntax_context,
            );
            let items = AstFragment::Items(items.into_iter().collect());

            match expand_mode {
                ExpandMode::DefSite => {
                    let prev = mem::replace(&mut self.ext_cx.current_expansion.id, expn_id);
                    let items =
                        self.ext_cx.monotonic_expander().fully_expand_fragment(items).make_items();
                    self.ext_cx.current_expansion.id = prev;
                    self.expanded_doctests.extend(items);
                }
                ExpandMode::CrateRoot | ExpandMode::StandaloneCrate => {
                    let items =
                        self.ext_cx.monotonic_expander().fully_expand_fragment(items).make_items();
                    self.expanded_doctests_crate.extend(items);
                }
            }
        }

        // We don't want to recurse into anything other than mods, since
        // mods or tests inside of functions will break things
        if let ast::ItemKind::Mod(
            _,
            mod_ident,
            ModKind::Loaded(.., ast::ModSpans { inner_span: _span, .. }),
        ) = item.kind
        {
            let prev_tests = mem::take(&mut self.expanded_doctests);
            let prev_parent_node_id = mem::replace(&mut self.parent_node_id, item.id);
            self.mod_path.push(mod_ident.clone());

            ast::mut_visit::walk_item(self, item);

            self.mod_path.pop();
            self.parent_node_id = prev_parent_node_id;

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
    exp: &mut DocTestsExpander<'_>,
    collected_doctest: CollectedDocTest,
    parse_info: ParseSourceInfo,
    item_span: Span,
    doctest_name: Symbol,
    expand_mode: ExpandMode,
    syntax_context_inside_the_generated_code: SyntaxContext,
) -> ThinVec<Box<ast::Item>> {
    let cx = &mut exp.ext_cx;

    let mut doctest_mod_items = ThinVec::new();

    if !parse_info.already_has_extern_crate && expand_mode != ExpandMode::StandaloneCrate {
        let extern_crate_self = cx.item(
            item_span,
            ast::AttrVec::new(),
            ast::ItemKind::ExternCrate(
                Some(kw::SelfLower),
                Ident::new(
                    exp.crate_name,
                    item_span.with_ctxt(syntax_context_inside_the_generated_code),
                ),
            ),
        );

        doctest_mod_items.push(extern_crate_self);
    }

    let doctest_expn_id = cx.resolver.expansion_for_ast_pass(
        item_span,
        AstPass::DocTests,
        None,
        &[],
        Some(exp.parent_node_id),
    );

    let entrypoint_sp = item_span.apply_mark(doctest_expn_id.to_expn_id(), Transparency::Opaque);

    // creates fn() -> ()
    let ret_ty = cx.ty(entrypoint_sp, ast::TyKind::Tup(ThinVec::new()));
    let decl = cx.fn_decl(ThinVec::new(), ast::FnRetTy::Ty(ret_ty));
    let sig = ast::FnSig { decl, header: ast::FnHeader::default(), span: entrypoint_sp };

    let entrypoint_ident = Ident::new(doctest_name, entrypoint_sp);

    match expand_mode {
        ExpandMode::DefSite | ExpandMode::CrateRoot => {
            let mut attrs = parse_info.attrs;
            for attr in &mut attrs {
                attr.style = rustc_ast::AttrStyle::Inner;
            }

            let mut stmts = parse_info.stmts;
            if parse_info.has_main_fn {
                let main_ident = Ident::new(
                    sym::main,
                    item_span.with_ctxt(syntax_context_inside_the_generated_code),
                );

                // creates main()
                let call = cx.expr_call_ident(entrypoint_sp, main_ident, ThinVec::new());
                stmts.push(cx.stmt_expr(call));
            }

            // creates fn <entrypoint>() -> () { ... }
            let entrypoint = cx.item(
                entrypoint_sp,
                attrs,
                ast::ItemKind::Fn(Box::new(ast::Fn {
                    defaultness: ast::Defaultness::Implicit,
                    ident: entrypoint_ident,
                    generics: ast::Generics::default(),
                    contract: None,
                    define_opaque: None,
                    eii_impl: None,
                    sig,
                    body: Some(cx.block(entrypoint_sp, stmts)),
                })),
            );
            doctest_mod_items.push(entrypoint);
        }
        ExpandMode::StandaloneCrate => {
            let builder = make::DocTestBuilder {
                already_has_extern_crate: parse_info.already_has_extern_crate,
                has_main_fn: parse_info.has_main_fn,
                global_crate_attrs: Vec::new(), // todo
                attrs: parse_info.str_attrs,
                crates: parse_info.crates,
                everything_else: parse_info.everything_else,
                test_id: None,
            };

            let source = builder.generate_unique_doctest(Some(exp.crate_name.as_str()));
            debug!(?source);

            let rustc = cx
                .sess
                .opts
                .sysroot
                .path()
                .join("bin")
                .join(format!("rustc{}", std::env::consts::EXE_SUFFIX));
            let body = mk_rustc_doctest_body(
                cx,
                entrypoint_sp,
                &rustc,
                &[],
                &source,
                "",
                collected_doctest.config.compile_fail,
            );

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
                    body: Some(body),
                })),
            );
            doctest_mod_items.push(entrypoint);
        }
    }

    let expn_id = cx.resolver.expansion_for_ast_pass(
        DUMMY_SP,
        AstPass::DocTests,
        None,
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
                            cx.expr_path(cx.path(sp, vec![entrypoint_ident])),
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
                ident: Ident::new(
                    Symbol::intern(&entrypoint_ident.name.as_str().to_ascii_uppercase()),
                    sp,
                ),
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
                                        field("test_type", cx.expr_path(test_type_path("DocTest"))),
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

    if expand_mode == ExpandMode::DefSite {
        doctest_mod_items
    } else {
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

        thin_vec![mod_]
    }
}

/// Builds the *body* of a doctest unit test:
/// compile `source` with `rustc` (source on stdin), then run the binary,
/// or, for `compile_fail`, check that compilation fails.
///
/// - `rustc_args`: flags for the child rustc, WITHOUT `-o <out>` and WITHOUT the trailing `-`
/// - `out_stem`: file stem for the produced binary (unique per test, no dots)
pub(crate) fn mk_rustc_doctest_body(
    ecx: &ExtCtxt<'_>,
    sp: Span,
    rustc: &Path,
    rustc_args: &[String],
    source: &str,
    out_stem: &str,
    compile_fail: bool,
) -> Box<ast::Block> {
    const OUT: &str = "__doctest_out";
    const CHILD: &str = "__doctest_child";
    const COMPILE: &str = "__doctest_compile";
    const RUN: &str = "__doctest_run";
    const MSG: &str = "__doctest_msg";

    // Locals must all use the same syntax context, so they all go through `ident`.
    let ident = |s: &str| Ident::new(Symbol::intern(s), sp);
    let local = |s: &str| ecx.expr_ident(sp, ident(s));
    let str_lit = |s: &str| ecx.expr_str(sp, Symbol::intern(s)); // handles escaping
    let field = |base: &str, f: &str| ecx.expr(sp, ast::ExprKind::Field(local(base), ident(f)));
    let semi = |e: Box<ast::Expr>| ast::Stmt {
        id: ast::DUMMY_NODE_ID,
        kind: ast::StmtKind::Semi(e),
        span: sp,
    };
    // `::a::b::c(args)`; path segments use dummy spans, like `ExtCtxt::std_path` does
    let gpath = |segs: &[&str]| -> Vec<Ident> {
        segs.iter().map(|s| Ident::with_dummy_span(Symbol::intern(s))).collect()
    };
    let call =
        |segs: &[&str], args: ThinVec<Box<ast::Expr>>| ecx.expr_call_global(sp, gpath(segs), args);
    let method = |recv: Box<ast::Expr>, name: &str, args: ThinVec<Box<ast::Expr>>| {
        ecx.expr_method_call(sp, recv, ident(name), args)
    };
    let not = |e| ecx.expr(sp, ast::ExprKind::Unary(UnOp::Not, e));
    let mut_ref =
        |e| ecx.expr(sp, ast::ExprKind::AddrOf(ast::BorrowKind::Ref, ast::Mutability::Mut, e));

    // { let mut msg = prefix.to_owned(); msg.push_str(&String::from_utf8_lossy(&bytes));
    //   ::std::panic::panic_any(msg); }
    let fail = |prefix: &str, bytes: Box<ast::Expr>| -> Box<ast::Expr> {
        let to_owned = call(&["std", "borrow", "ToOwned", "to_owned"], thin_vec![str_lit(prefix)]);
        let lossy = call(
            &["std", "string", "String", "from_utf8_lossy"],
            thin_vec![ecx.expr_addr_of(sp, bytes)],
        );
        let stmts = thin_vec![
            ecx.stmt_let(sp, true, ident(MSG), to_owned),
            semi(method(local(MSG), "push_str", thin_vec![ecx.expr_addr_of(sp, lossy)])),
            semi(call(&["std", "panic", "panic_any"], thin_vec![local(MSG)])),
        ];
        ecx.expr_block(ecx.block(sp, stmts))
    };
    // let _ = ::std::fs::remove_file(&out);
    let remove_out = || {
        ecx.stmt_let(
            sp,
            false,
            ident("_doctest_removed"),
            call(&["std", "fs", "remove_file"], thin_vec![ecx.expr_addr_of(sp, local(OUT))]),
        )
    };

    let mut stmts: ThinVec<ast::Stmt> = ThinVec::new();

    // let mut out = ::std::env::temp_dir(); out.push(stem); out.set_extension(EXE_EXTENSION);
    stmts.push(ecx.stmt_let(sp, true, ident(OUT), call(&["std", "env", "temp_dir"], thin_vec![])));
    stmts.push(semi(method(local(OUT), "push", thin_vec![str_lit(out_stem)])));
    let exe_ext =
        ecx.expr_path(ecx.path_global(sp, gpath(&["std", "env", "consts", "EXE_EXTENSION"])));
    stmts.push(semi(method(local(OUT), "set_extension", thin_vec![exe_ext])));

    // let mut child = Command::new(RUSTC).arg(..)...arg("-o").arg(&out).arg("-")
    //     .stdin(piped()).stdout(piped()).stderr(piped()).spawn().expect(..);
    let mut cmd =
        call(&["std", "process", "Command", "new"], thin_vec![str_lit(&rustc.to_string_lossy())]);
    for a in rustc_args {
        cmd = method(cmd, "arg", thin_vec![str_lit(a)]);
    }
    cmd = method(cmd, "arg", thin_vec![str_lit("-o")]);
    cmd = method(cmd, "arg", thin_vec![ecx.expr_addr_of(sp, local(OUT))]);
    cmd = method(cmd, "arg", thin_vec![str_lit("-")]);
    for stream in ["stdin", "stdout", "stderr"] {
        let piped = call(&["std", "process", "Stdio", "piped"], thin_vec![]);
        cmd = method(cmd, stream, thin_vec![piped]);
    }
    let spawn = method(
        method(cmd, "spawn", thin_vec![]),
        "expect",
        thin_vec![str_lit("failed to spawn rustc")],
    );
    stmts.push(ecx.stmt_let(sp, true, ident(CHILD), spawn));

    // ::std::io::Write::write_all(&mut child.stdin.take().expect(..), SRC.as_bytes()).expect(..);
    // (the temporary ChildStdin is dropped at the end of the statement => EOF for rustc)
    let stdin = method(field(CHILD, "stdin"), "take", thin_vec![]);
    let stdin = method(stdin, "expect", thin_vec![str_lit("stdin was piped")]);
    let bytes = method(str_lit(source), "as_bytes", thin_vec![]);
    let write = call(&["std", "io", "Write", "write_all"], thin_vec![mut_ref(stdin), bytes]);
    stmts.push(semi(method(
        write,
        "expect",
        thin_vec![str_lit("failed to write the doctest to rustc's stdin")],
    )));

    // let compile = child.wait_with_output().expect(..);
    let wait = method(local(CHILD), "wait_with_output", thin_vec![]);
    stmts.push(ecx.stmt_let(
        sp,
        false,
        ident(COMPILE),
        method(wait, "expect", thin_vec![str_lit("failed to wait on rustc")]),
    ));

    if compile_fail {
        stmts.push(remove_out()); // in case it unexpectedly compiled
        // if compile.status.code() != Some(1) { fail } -- 1 = ordinary compile errors,
        // 101 = ICE, None = killed by a signal: none of those is a legit compile_fail
        let code = method(field(COMPILE, "status"), "code", thin_vec![]);
        let one = ecx
            .expr(sp, ast::ExprKind::Lit(token::Lit::new(token::Integer, sym::integer(1), None)));
        let some_one = call(&["std", "option", "Option", "Some"], thin_vec![one]);
        let cond = ecx.expr_binary(sp, BinOpKind::Ne, code, some_one);
        let fail = fail(
            "compile_fail doctest: rustc did not fail with a normal compile error:\n",
            field(COMPILE, "stderr"),
        );
        stmts.push(ecx.stmt_expr(ecx.expr_if(sp, cond, fail, None)));
    } else {
        // if !compile.status.success() { fail }
        let ok = method(field(COMPILE, "status"), "success", thin_vec![]);
        let fail_c = fail("rustc failed to compile the doctest:\n", field(COMPILE, "stderr"));
        stmts.push(ecx.stmt_expr(ecx.expr_if(sp, not(ok), fail_c, None)));

        // let run = Command::new(&out).output().expect(..); let _ = remove_file(&out);
        let run = call(
            &["std", "process", "Command", "new"],
            thin_vec![ecx.expr_addr_of(sp, local(OUT))],
        );
        let run = method(
            method(run, "output", thin_vec![]),
            "expect",
            thin_vec![str_lit("failed to run the doctest binary")],
        );
        stmts.push(ecx.stmt_let(sp, false, ident(RUN), run));
        stmts.push(remove_out());

        // if !run.status.success() { fail }
        let ok = method(field(RUN, "status"), "success", thin_vec![]);
        let fail_r = fail("the doctest binary failed:\n", field(RUN, "stderr"));
        stmts.push(ecx.stmt_expr(ecx.expr_if(sp, not(ok), fail_r, None)));
    }

    ecx.block(sp, stmts)
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
