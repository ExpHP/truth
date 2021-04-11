//! Entry point for integration tests that run the 'compile' and 'decompile' subcommands.
#![allow(non_snake_case)]

#[macro_use]
mod integration_impl;

mod integration {
    mod general;
    mod anm_features;
    mod std_features;
    mod msg_features;
    mod bits_2_bits;
    mod type_check;
    mod decompile_loop;
}

// a dumb test to make sure that we don't just dump files in the input directory and
// forget to add tests for them.
#[test]
fn all_files_tested() {
    let mut not_mentioned = vec![];

    let mut test_file_contents = vec![];
    for entry in std::fs::read_dir("tests/integration").unwrap() {
        let path = entry.unwrap().path();
        if path.extension() == Some(std::ffi::OsStr::new("rs")) {
            test_file_contents.push(std::fs::read_to_string(path).unwrap());
        }
    }
    let concatenated_tests = test_file_contents.join("\n");

    for entry in std::fs::read_dir("tests/integration/resources").unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() {
            let file_name = path.file_name().unwrap().to_str().unwrap();

            if !concatenated_tests.contains(file_name) {
                not_mentioned.push(file_name.to_string());
            }
        }
    }

    if !not_mentioned.is_empty() {
        panic!("Files not mentioned in integration/*.rs: {:?}", not_mentioned);
    }
}
