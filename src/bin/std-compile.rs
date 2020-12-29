use ecl_parser::{self};

use getopts::Options;
use std::env;

fn usage(program: &str) -> String {
    format!("Usage: {} FILE -g GAME -o OUTPUT [OPTIONS...]", program)
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
    opts.reqopt("o", "output", "output file", "OUTPUT");
    opts.optopt("m", "map", "use a stdmap", "STDMAP");
    opts.reqopt("g", "game", "game number, e.g. 'th095' or '8'. Don't include a point in point titles. Also supports 'alcostg'.", "GAME");
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

    let game = matches.opt_get("game").expect("bad game").unwrap();
    let output = matches.opt_str("output").unwrap();
    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_help(&program, opts);
        std::process::exit(1);
    };
    run(game, &input, output, matches.opt_str("map"));
}

fn run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    output: impl AsRef<std::path::Path>,
    map_path: Option<impl AsRef<std::path::Path>>,
) {
    let functions = {
        let mut functions = ecl_parser::signature::Functions::new();
        if let Some(map_path) = map_path {
            let eclmap: ecl_parser::Eclmap = std::fs::read_to_string(map_path).unwrap().parse().unwrap();
            functions.add_from_eclmap(&eclmap);
        }
        functions
    };

    let text = std::fs::read(&path).unwrap();
    let mut files = ecl_parser::pos::Files::new();
    let script = match files.parse(&path.as_ref().to_string_lossy(), &text) {
        Ok(x) => x,
        Err(e) => panic!("{}", e),
    };

    let std = match ecl_parser::std::StdFile::compile(game, &script, &functions) {
        Ok(x) => x,
        Err(mut es) => {
            es.emit(&files).expect("error while writing errors?!");
            return
        },
    };

    let mut out = std::fs::File::create(output).unwrap();
    ecl_parser::std::write_std(game, &mut out, &std).unwrap();
}
