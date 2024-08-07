//! This test is a part of quality control and makes clippy eat what it produces. Awesome lints and
//! long error messages
//!
//! See [Eating your own dog food](https://en.wikipedia.org/wiki/Eating_your_own_dog_food) for context

#![cfg_attr(feature = "deny-warnings", deny(warnings))]
#![warn(rust_2018_idioms, unused_lifetimes)]

use itertools::Itertools;
use std::fs::File;
use std::io::{self, IsTerminal};
use std::path::PathBuf;
use std::process::Command;
use std::time::SystemTime;
use test_utils::IS_RUSTC_TEST_SUITE;
use ui_test::Args;

mod test_utils;

fn main() {
    if IS_RUSTC_TEST_SUITE {
        return;
    }

    let args = Args::test().unwrap();

    if args.list {
        if !args.ignored {
            println!("dogfood: test");
        }
    } else if !args.skip.iter().any(|arg| arg == "dogfood") {
        if args.filters.iter().any(|arg| arg == "collect_metadata") {
            collect_metadata();
        } else {
            dogfood();
        }
    }
}

fn dogfood() {
    let mut failed_packages = Vec::new();

    for package in [
        "./",
        "clippy_dev",
        "clippy_lints",
        "clippy_utils",
        "clippy_config",
        "lintcheck",
        "rustc_tools_util",
    ] {
        println!("linting {package}");
        if !run_clippy_for_package(package, &["-D", "clippy::all", "-D", "clippy::pedantic"]) {
            failed_packages.push(if package.is_empty() { "root" } else { package });
        }
    }

    assert!(
        failed_packages.is_empty(),
        "Dogfood failed for packages `{}`",
        failed_packages.iter().join(", "),
    );
}

fn collect_metadata() {
    assert!(cfg!(feature = "internal"));

    // Setup for validation
    let metadata_output_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("util/gh-pages/lints.json");
    let start_time = SystemTime::now();

    // Run collection as is
    std::env::set_var("ENABLE_METADATA_COLLECTION", "1");
    assert!(run_clippy_for_package(
        "clippy_lints",
        &["-A", "unfulfilled_lint_expectations"]
    ));

    // Check if cargo caching got in the way
    if let Ok(file) = File::open(metadata_output_path) {
        if let Ok(metadata) = file.metadata() {
            if let Ok(last_modification) = metadata.modified() {
                if last_modification > start_time {
                    // The output file has been modified. Most likely by a hungry
                    // metadata collection monster. So We'll return.
                    return;
                }
            }
        }
    }

    // Force cargo to invalidate the caches
    filetime::set_file_mtime(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("clippy_lints/src/lib.rs"),
        filetime::FileTime::now(),
    )
    .unwrap();

    // Running the collection again
    assert!(run_clippy_for_package(
        "clippy_lints",
        &["-A", "unfulfilled_lint_expectations"]
    ));
}

#[must_use]
fn run_clippy_for_package(project: &str, args: &[&str]) -> bool {
    let root_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let mut command = Command::new(&*test_utils::CARGO_CLIPPY_PATH);

    command
        .current_dir(root_dir.join(project))
        .env("CARGO_INCREMENTAL", "0")
        .arg("clippy")
        .arg("--all-targets")
        .arg("--all-features");

    if !io::stdout().is_terminal() {
        command.arg("-q");
    }

    if let Ok(dogfood_args) = std::env::var("__CLIPPY_DOGFOOD_ARGS") {
        for arg in dogfood_args.split_whitespace() {
            command.arg(arg);
        }
    }

    command.arg("--").args(args);
    command.arg("-Cdebuginfo=0"); // disable debuginfo to generate less data in the target dir

    if cfg!(feature = "internal") {
        // internal lints only exist if we build with the internal feature
        command.args(["-D", "clippy::internal"]);
    } else {
        // running a clippy built without internal lints on the clippy source
        // that contains e.g. `allow(clippy::invalid_paths)`
        command.args(["-A", "unknown_lints"]);
    }

    command.status().unwrap().success()
}
