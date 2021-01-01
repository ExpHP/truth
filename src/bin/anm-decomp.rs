use ecl_parser::{self, Format, CompileError};

use anyhow::Context;
use getopts::Options;
use std::env;

fn usage(program: &str) -> String {
    format!("Usage: {} FILE -g GAME [OPTIONS...]", program)
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
    opts.optopt("", "max-columns", "where possible, will attempt to break lines for < NUM columns", "NUM");
    opts.optopt("m", "map", "use an anmmap", "ANMMAP");
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
    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_help(&program, opts);
        std::process::exit(1);
    };
    run(game, &input, matches.opt_get_default("max-columns", 100).unwrap(), matches.opt_str("map"));
}

fn run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    ncol: usize,
    map_path: Option<impl AsRef<std::path::Path>>,
) {
    let ty_ctx = {
        use ecl_parser::Eclmap;

        let mut ty_ctx = ecl_parser::type_system::TypeSystem::new();

        let map_path = map_path.map(|p| p.as_ref().to_owned());
        if let Some(map_path) = map_path.or_else(|| Eclmap::default_map_file(".anmm")) {
            let eclmap = Eclmap::load(map_path, Some(game)).unwrap();
            ty_ctx.extend_from_eclmap(&eclmap);
        }
        ty_ctx
    };

    let script = {
        let bytes = std::fs::read(&path).unwrap();
        let parsed = {
            ecl_parser::anm::read_anm(game, &bytes)
                .with_context(|| format!("in file: {}", path.as_ref().display()))
        };
        match parsed {
            Ok(parsed) => ecl_parser::anm::decompile(game, &parsed, &ty_ctx),
            Err(e) => {
                CompileError::from(e).emit_nospans();
                return;
            },
        }
    };

    let stdout = std::io::stdout();
    let mut f = ecl_parser::fmt::Formatter::new(stdout.lock()).with_max_columns(ncol);
    script.fmt(&mut f).unwrap();
}
