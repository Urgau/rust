// This test checks the diganostic output for the unexpected
// `test` cfg with Cargo.
//
//@ check-pass
//@ no-auto-check-cfg
//@ rustc-env:CARGO_CRATE_NAME=foo
//@ compile-flags: --check-cfg=cfg()

#[cfg(test)]
//~^ WARNING unexpected `cfg` condition name
fn ser() {}

fn main() {}
