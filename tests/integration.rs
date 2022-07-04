//! Entry point for integration tests that run the 'compile' and 'decompile' subcommands.
#![allow(non_snake_case)]

#[macro_use]
mod integration_impl;

macro_rules! regex {
    ($s:expr) => { regex::Regex::new($s).unwrap() }
}

mod integration {
    mod anm_consts;
    mod anm_features;
    mod bits_2_bits;
    mod count_jmps;
    mod decompile_block;
    mod difficulty;
    mod ecl_features;
    mod enums;
    mod expr_compile;
    mod general;
    mod image_sources;
    mod interrupts;
    mod mapfiles;
    mod msg_features;
    mod pseudo;
    mod std_features;
    mod strings;
    mod time_label_compilation;
    mod time_label_formatting;
    mod timelines;
    mod timeline_arg0;
    mod type_check;
}

// a dumb test to make sure that we don't just dump files in the input directory and
// forget to add tests for them.
#[test]
fn all_files_tested() {
    let mut not_mentioned = vec![];

    let mut test_file_contents = vec![];
    let mut test_file_names = vec![];
    for entry in std::fs::read_dir("tests/integration").unwrap() {
        let path = entry.unwrap().path();
        if path.extension() == Some(std::ffi::OsStr::new("rs")) {
            test_file_contents.push(std::fs::read_to_string(&path).unwrap());
            test_file_names.push(path.file_name().unwrap().to_owned());
        }
    }
    let concatenated_tests = test_file_contents.join("\n");

    // all resources must be mentioned in at least one test module
    for entry in std::fs::read_dir("tests/integration/resources").unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() {
            let file_name = path.file_name().unwrap().to_str().unwrap();

            if !concatenated_tests.contains(file_name) {
                not_mentioned.push(file_name.to_string());
            }
        }
    }

    // this file must include all modules
    let this_source_file = std::fs::read_to_string(file!()).unwrap();
    for name in test_file_names {
        let name = name.to_string_lossy();
        let stem = &name[..name.len() - ".rs".len()];
        let mod_line = format!("mod {};", stem);
        if !this_source_file.contains(&mod_line) {
            not_mentioned.push(name.to_string());
        }
    }

    if !not_mentioned.is_empty() {
        panic!("Files not mentioned in integration/*.rs: {:?}", not_mentioned);
    }
}
