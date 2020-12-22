use ecl_parser::{self, Format};

use getopts::Options;
use std::env;

fn print_usage(program: &str, opts: Options) {
    let brief = format!("Usage: {} FILE", program);
    print!("{}", opts.usage(&brief));
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let program = args[0].clone();

    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help menu");
    opts.optopt("", "max-columns", "where possible, will attempt to break lines for < NUM columns", "NUM");
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => { m }
        Err(f) => { panic!(f.to_string()) }
    };
    if matches.opt_present("h") {
        print_usage(&program, opts);
        return;
    }

    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };
    run(&input, matches.opt_get_default("max-columns", 100).unwrap());
}

fn run(path: impl AsRef<std::path::Path>, ncol: usize) {
    let functions = {
        let eclmap: ecl_parser::Eclmap = std::fs::read_to_string("src/std-14.stdm").unwrap().parse().unwrap();
        let mut functions = ecl_parser::signature::Functions::new();
        functions.add_from_eclmap(&eclmap);
        functions
    };

    let script = {
        let bytes = std::fs::read(path).unwrap();
        let parsed = ecl_parser::std::read_std_10(&bytes);
        parsed.decompile(&functions)
    };

    let stdout = std::io::stdout();
    let mut f = ecl_parser::fmt::Formatter::new(stdout.lock()).with_max_columns(ncol);
    script.fmt(&mut f).unwrap();
}
