// This binary is just a shim that calls 'truth' with the first argument set.
//
// IMPORTANT: DO NOT USE ANYTHING FROM THE LIB CRATE HERE!
//
//            If you do, you'll cause linking to occur and full package builds using --all-targets
//            or --tests will take quite measurably longer!

mod common;

fn main() {
    common::run_truth_subcommand("anm-modify");
}
