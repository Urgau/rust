// Code that generates a test runner to run all the tests in a crate

use rustc_ast as ast;
use rustc_ast::ModKind;
use rustc_ast::mut_visit::*;
use rustc_expand::base::{ExtCtxt, ResolverExpand};
use rustc_expand::expand::ExpansionConfig;
use rustc_feature::Features;
use rustc_session::Session;
use rustc_span::hygiene::AstPass;
use rustc_span::{DUMMY_SP, Span, sym};

mod parsing;

#[allow(dead_code)]
struct ExpanderCtxt<'a> {
    ext_cx: ExtCtxt<'a>,
    def_site: Span,
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

    let expn_id = ext_cx.resolver.expansion_for_ast_pass(
        DUMMY_SP,
        AstPass::TestHarness,
        &[sym::test, sym::rustc_attrs, sym::coverage_attribute],
        None,
    );
    let def_site = DUMMY_SP.with_def_site_ctxt(expn_id.to_expn_id());

    let cx = ExpanderCtxt { ext_cx, def_site };

    DocTestsExpander { cx }.visit_crate(krate);
}

#[allow(dead_code)]
struct DocTestsExpander<'a> {
    cx: ExpanderCtxt<'a>,
}

impl<'a> MutVisitor for DocTestsExpander<'a> {
    fn visit_crate(&mut self, c: &mut ast::Crate) {
        walk_crate(self, c);
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
                dbg!(&_config, &_rel_line, &_code_mappings);
            }
        }

        let mut collector = DocTestsCollector { tests: Vec::new() };

        parsing::find_testable_code(
            dbg!(&doc_strs),
            &mut collector,
            parsing::ErrorCodes::Yes, /*, None*/
        );

        dbg!(&collector.tests);

        // We don't want to recurse into anything other than mods, since
        // mods or tests inside of functions will break things
        if let ast::ItemKind::Mod(
            _,
            _,
            ModKind::Loaded(.., ast::ModSpans { inner_span: _span, .. }),
        ) = item.kind
        {
            ast::mut_visit::walk_item(self, item);
        } /* else {
        // But in those cases, we emit a lint to warn the user of these missing tests.
        ast::visit::walk_item(&mut InnerItemLinter { sess: self.cx.ext_cx.sess }, item);
        }*/
    }
}

/*
/// Creates a function item for use as the main function of a test build.
/// This function will call the `test_runner` as specified by the crate attribute
///
/// By default this expands to
///
/// ```ignore (messes with test internals)
/// #[rustc_main]
/// pub fn main() {
///     extern crate test;
///     test::test_main_static(&[
///         &test_const1,
///         &test_const2,
///         &test_const3,
///     ]);
/// }
/// ```
///
/// Most of the Ident have the usual def-site hygiene for the AST pass. The
/// exception is the `test_const`s. These have a syntax context that has two
/// opaque marks: one from the expansion of `test` or `test_case`, and one
/// generated  in `TestHarnessGenerator::visit_item`. When resolving this
/// identifier after failing to find a matching identifier in the root module
/// we remove the outer mark, and try resolving at its def-site, which will
/// then resolve to `test_const`.
///
/// The expansion here can be controlled by two attributes:
///
/// [`TestCtxt::reexport_test_harness_main`] provides a different name for the `main`
/// function and [`TestCtxt::test_runner`] provides a path that replaces
/// `test::test_main_static`.
fn mk_main(cx: &mut TestCtxt<'_>) -> Box<ast::Item> {
    let sp = cx.def_site;
    let ecx = &cx.ext_cx;
    let test_ident = Ident::new(sym::test, sp);

    let runner_name =
        if cx.panic_strategy.unwinds() { "test_main_static" } else { "test_main_static_abort" };

    // test::test_main_static(...)
    let mut test_runner = cx.test_runner.clone().unwrap_or_else(|| {
        ecx.path(sp, vec![test_ident, Ident::from_str_and_span(runner_name, sp)])
    });

    test_runner.span = sp;

    let test_main_path_expr = ecx.expr_path(test_runner);
    let call_test_main = ecx.expr_call(sp, test_main_path_expr, thin_vec![mk_tests_slice(cx, sp)]);
    let call_test_main = ecx.stmt_expr(call_test_main);

    // extern crate test
    let test_extern_stmt = ecx.stmt_item(
        sp,
        ecx.item(sp, ast::AttrVec::new(), ast::ItemKind::ExternCrate(None, test_ident)),
    );

    // #[rustc_main]
    let main_attr = ecx.attr_word(sym::rustc_main, sp);
    // #[coverage(off)]
    let coverage_attr = ecx.attr_nested_word(sym::coverage, sym::off, sp);
    // #[doc(hidden)]
    let doc_hidden_attr = ecx.attr_nested_word(sym::doc, sym::hidden, sp);

    // pub fn main() { ... }
    let main_ret_ty = ecx.ty(sp, ast::TyKind::Tup(ThinVec::new()));

    // If no test runner is provided we need to import the test crate
    let main_body = if cx.test_runner.is_none() {
        ecx.block(sp, thin_vec![test_extern_stmt, call_test_main])
    } else {
        ecx.block(sp, thin_vec![call_test_main])
    };

    let decl = ecx.fn_decl(ThinVec::new(), ast::FnRetTy::Ty(main_ret_ty));
    let sig = ast::FnSig { decl, header: ast::FnHeader::default(), span: sp };
    let defaultness = ast::Defaultness::Implicit;

    // Honor the reexport_test_harness_main attribute
    let main_ident = match cx.reexport_test_harness_main {
        Some(sym) => Ident::new(sym, sp.with_ctxt(SyntaxContext::root())),
        None => Ident::new(sym::main, sp),
    };

    let main = ast::ItemKind::Fn(Box::new(ast::Fn {
        defaultness,
        sig,
        ident: main_ident,
        generics: ast::Generics::default(),
        contract: None,
        body: Some(main_body),
        define_opaque: None,
        eii_impl: None,
    }));

    let main = Box::new(ast::Item {
        attrs: thin_vec![main_attr, coverage_attr, doc_hidden_attr],
        id: ast::DUMMY_NODE_ID,
        kind: main,
        vis: ast::Visibility { span: sp, kind: ast::VisibilityKind::Public },
        span: sp,
        tokens: None,
    });

    // Integrate the new item into existing module structures.
    let main = AstFragment::Items(smallvec![main]);
    cx.ext_cx.monotonic_expander().fully_expand_fragment(main).make_items().pop().unwrap()
}

/// Creates a slice containing every test like so:
/// &[&test1, &test2]
fn mk_tests_slice(cx: &TestCtxt<'_>, sp: Span) -> Box<ast::Expr> {
    debug!("building test vector from {} tests", cx.test_cases.len());
    let ecx = &cx.ext_cx;

    let mut tests = cx.test_cases.clone();
    // Note that this sort is load-bearing: the libtest harness uses binary search to find tests by
    // name.
    tests.sort_by(|a, b| a.name.as_str().cmp(b.name.as_str()));

    ecx.expr_array_ref(
        sp,
        tests
            .iter()
            .map(|test| {
                ecx.expr_addr_of(test.span, ecx.expr_path(ecx.path(test.span, vec![test.ident])))
            })
            .collect(),
    )
}

fn get_test_name(i: &ast::Item) -> Option<Symbol> {
    attr::first_attr_value_str_by_name(&i.attrs, sym::rustc_test_marker)
}

fn get_test_runner(sess: &Session, krate: &ast::Crate) -> Option<ast::Path> {
    match AttributeParser::parse_limited_sym(sess, &krate.attrs, &[sym::test_runner]) {
        Some(rustc_attr_ir::Attribute::Parsed(AttributeKind::TestRunner(path))) => Some(path),
        _ => None,
    }
}
*/
