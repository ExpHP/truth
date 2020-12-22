use ecl_parser::{self};

use getopts::Options;
use std::env;

fn print_usage(program: &str, opts: Options) {
    let brief = format!("Usage: {} FILE (-o|--output) OUTPUT", program);
    print!("{}", opts.usage(&brief));
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let program = args[0].clone();

    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help menu");
    opts.optopt("o", "output", "output file", "OUTPUT");
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => { m }
        Err(f) => { panic!(f.to_string()) }
    };
    if matches.opt_present("h") || !matches.opt_present("output") {
        print_usage(&program, opts);
        return;
    }

    let output = matches.opt_str("output").unwrap();
    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };
    run(&input, output);
}

fn run(path: impl AsRef<std::path::Path>, output: impl AsRef<std::path::Path>) {
    use ecl_parser::Parse;
    use codespan_reporting::term::{self, termcolor as tc};

    let functions = {
        let eclmap: ecl_parser::Eclmap = std::fs::read_to_string("src/std-14.stdm").unwrap().parse().unwrap();
        let mut functions = ecl_parser::signature::Functions::new();
        functions.add_from_eclmap(&eclmap);
        functions
    };

    let text = std::fs::read(&path).unwrap();
    let script = match ecl_parser::Script::parse(&text) {
        Ok(x) => x,
        Err(e) => panic!("{}", e),
    };
    let mut files = ecl_parser::pos::Files::new();
    let file_id = files.add(&path, &text);

    let std = match ecl_parser::std::StdFile::compile(file_id, &script, &functions) {
        Ok(x) => x,
        Err(e) => {
            let writer = tc::StandardStream::stderr(tc::ColorChoice::Always);
            let config = term::Config::default();
            term::emit(&mut writer.lock(), &config, &files, &e.0).unwrap();
            return
        },
    };

    let mut out = std::fs::File::create(output).unwrap();
    ecl_parser::std::write_std_10(&mut out, &std).unwrap();
}
