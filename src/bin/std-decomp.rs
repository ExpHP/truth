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
    opts.optopt("m", "map", "use a stdmap", "STDMAP");
    opts.reqopt("g", "game", "game number, e.g. 'th095' or '8'. Don't include a point in point titles. Also supports 'alcostg'.", "GAME");
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => { m }
        Err(f) => { panic!(f.to_string()) }
    };
    if matches.opt_present("h") {
        print_usage(&program, opts);
        return;
    }

    let game = matches.opt_get("game").expect("bad game").unwrap();
    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };
    run(game, &input, matches.opt_get_default("max-columns", 100).unwrap(), matches.opt_str("map"));
}

fn run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    ncol: usize,
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

    let script = {
        let bytes = std::fs::read(path).unwrap();
        let parsed = ecl_parser::std::read_std(game, &bytes);
        parsed.decompile(game, &functions)
    };

    let stdout = std::io::stdout();
    let mut f = ecl_parser::fmt::Formatter::new(stdout.lock()).with_max_columns(ncol);
    script.fmt(&mut f).unwrap();
}
