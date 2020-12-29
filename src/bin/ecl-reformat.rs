use ecl_parser;
use ecl_parser::Parse;

use getopts::Options;
use std::env;

fn usage(program: &str) -> String {
    format!("Usage: {} FILE [OPTIONS...]", program)
}
fn print_usage(program: &str) {
    eprintln!("{}", usage(program));
}
fn print_help(program: &str, opts: Options) {
    eprint!("{}", opts.usage(&usage(program)));
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let program = args[0].clone();

    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help menu");
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => { m }
        Err(e) => {
            print_usage(&program);
            eprintln!("ERROR: {}", e);
            std::process::exit(1);
        }
    };
    if matches.opt_present("h") {
        print_help(&program, opts);
        return;
    }

    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_help(&program, opts);
        std::process::exit(1);
    };
    run(&input);
}

fn run(path: impl AsRef<std::path::Path>) {
    let text = std::fs::read(path).unwrap();

    let script = match ecl_parser::Script::parse(&text) {
        Ok(x) => x,
        Err(e) => panic!("{}", e),
    };
    let stdout = std::io::stdout();
    let mut f = ecl_parser::fmt::Formatter::new(stdout.lock());
    f.fmt(&script).unwrap();
}
