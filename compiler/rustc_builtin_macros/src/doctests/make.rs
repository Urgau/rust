/// Information about a doctest, used to generate the doctest source code.
pub(crate) struct DocTestBuilder {
    pub(crate) already_has_extern_crate: bool,
    pub(crate) has_main_fn: bool,
    pub(crate) global_crate_attrs: Vec<String>,
    pub(crate) attrs: String,
    pub(crate) crates: String,
    pub(crate) everything_else: String,
    pub(crate) test_id: Option<String>,
}

impl DocTestBuilder {
    /// Transforms a test into a complete Rust source file that can be compiled into a binary.
    pub(crate) fn generate_unique_doctest(&self, crate_name: Option<&str>) -> String {
        let processed_code = self.everything_else.trim();
        let mut source = String::new();

        if self.global_crate_attrs.is_empty() {
            // If there aren't any attributes supplied by `#![doc(test(attr(...)))]`, allow some
            // lints that are commonly triggered in doctests. The crate-level test attributes are
            // commonly used to make tests fail in case they trigger warnings, so having this
            // there in that case may cause some tests to pass when they shouldn't have.
            source.push_str("#![allow(unused)]\n");
        }

        // Attributes that came from `#![doc(test(attr(...)))]`.
        for attr in &self.global_crate_attrs {
            source.push_str(&format!("#![{attr}]\n"));
        }

        // Outer attributes from the example (attributes, crates).
        for chunk in [&self.attrs, &self.crates] {
            if !chunk.is_empty() {
                source.push_str(chunk);
                if !chunk.ends_with('\n') {
                    source.push('\n');
                }
            }
        }

        // Don't inject `extern crate std` because it's already injected by the compiler.
        if !self.already_has_extern_crate
            && let Some(crate_name) = crate_name
            && crate_name != "std"
        {
            // rustdoc implicitly inserts an `extern crate` item for the own crate, which may be
            // unused, so we need to allow the lint.
            source.push_str("#[allow(unused_extern_crates)]\n");
            source.push_str(&format!("extern crate r#{crate_name};\n"));
        }

        // FIXME: This code cannot yet handle `no_std` test cases.
        if self.has_main_fn || source.contains("![no_std]") {
            source.push_str(processed_code);
            return source;
        }

        let returns_result = processed_code.ends_with("(())");

        // Give each doctest main function a unique name.
        // This is for example needed for the tooling around `-C instrument-coverage`.
        let (inner_fn_name, inner_attr) = match &self.test_id {
            Some(test_id) => (format!("_doctest_main_{test_id}"), "#[allow(non_snake_case)] "),
            None => ("_inner".to_string(), ""),
        };

        // Note on newlines: we insert a newline *before* and *after* the doctest so that, with
        // `-C instrument-coverage`, the generated inner `main` spans from the opening code block
        // to the closing one.
        if returns_result {
            source.push_str(&format!(
                "fn main() {{ {inner_attr}fn {inner_fn_name}() -> core::result::Result<(), impl core::fmt::Debug> {{\n"
            ));
            source.push_str(processed_code);
            source.push_str(&format!("\n}} {inner_fn_name}().unwrap() }}"));
        } else if self.test_id.is_some() {
            source.push_str(&format!("fn main() {{ {inner_attr}fn {inner_fn_name}() {{\n"));
            source.push_str(processed_code);
            source.push_str(&format!("\n}} {inner_fn_name}() }}"));
        } else {
            source.push_str("fn main() {\n");
            source.push_str(processed_code);
            source.push_str("\n}");
        }

        source
    }
}
