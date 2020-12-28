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
    opts.optopt("m", "map", "use a stdmap", "STDMAP");
    opts.reqopt("g", "game", "game number, e.g. 'th095' or '8'. Don't include a point in point titles. Also supports 'alcostg'.", "GAME");
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => { m }
        Err(f) => { panic!(f.to_string()) }
    };
    if matches.opt_present("h") || !matches.opt_present("output") {
        print_usage(&program, opts);
        return;
    }

    let game = matches.opt_get("game").expect("bad game").unwrap();
    let output = matches.opt_str("output").unwrap();
    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
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
