use ecl_parser;

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
    let bytes = std::fs::read(path).unwrap();
    let parsed = ecl_parser::std::read_std(&ecl_parser::std::FileFormat10, &bytes);
    let mut out = std::fs::File::create(output).unwrap();
    ecl_parser::std::write_std(&ecl_parser::std::FileFormat10, &mut out, &parsed).unwrap();
}
