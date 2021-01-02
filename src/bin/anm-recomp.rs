use ecl_parser::{self};

use getopts::Options;
use std::env;

use ecl_parser::CompileError;

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
    let output = matches.opt_str("output").unwrap();
    let input = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_help(&program, opts);
        std::process::exit(1);
    };

    let mut files = ecl_parser::pos::Files::new();
    if let Err(mut e) = run(&mut files, game, &input, output, matches.opt_str("map")) {
        e.emit(&files).expect("error while writing errors?!");
        std::process::exit(1);
    }
}

fn run(
    files: &mut ecl_parser::pos::Files,
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    output: impl AsRef<std::path::Path>,
    map_path: Option<impl AsRef<std::path::Path>>,
) -> Result<(), CompileError> {
    let mut ty_ctx = ecl_parser::type_system::TypeSystem::new();
    if let Some(map_path) = map_path {
        let eclmap = ecl_parser::Eclmap::load(&map_path, Some(game)).unwrap();
        ty_ctx.extend_from_eclmap(map_path.as_ref(), &eclmap);
    }

    let text = std::fs::read(&path).unwrap();
    let script = files.parse::<ecl_parser::Script>(&path.as_ref().to_string_lossy(), &text)?;

    // FIXME nightmarish error handling
    for path_literal in &script.mapfiles {
        let path = path_literal.as_path()?;
        match ecl_parser::Eclmap::load(&path, Some(game)) {
            Ok(eclmap) => ty_ctx.extend_from_eclmap(path, &eclmap),
            Err(e) => { return Err(ecl_parser::error!(
                message("{}", e), primary(path_literal, "error loading file"),
            ))},
        }
    }
    let anm = ecl_parser::anm::AnmFile::compile(game, &script, &ty_ctx)?;

    let mut out = std::fs::File::create(output)?;
    ecl_parser::anm::write_anm(game, &mut out, &anm)?;
    Ok(())
}

fn _run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    output: impl AsRef<std::path::Path>,
    map_path: Option<impl AsRef<std::path::Path>>,
) -> Result<(), CompileError> {
    let mut ty_ctx = ecl_parser::type_system::TypeSystem::new();
    if let Some(map_path) = map_path {
        let eclmap = ecl_parser::Eclmap::load(&map_path, Some(game)).unwrap();
        ty_ctx.extend_from_eclmap(map_path.as_ref(), &eclmap);
    }

    let text = std::fs::read(&path).unwrap();
    let mut files = ecl_parser::pos::Files::new();
    let script = files.parse::<ecl_parser::Script>(&path.as_ref().to_string_lossy(), &text)?;

    // FIXME nightmarish error handling
    for path_literal in &script.mapfiles {
        let path = path_literal.as_path()?;
        match ecl_parser::Eclmap::load(&path, Some(game))? {
            Ok(eclmap) => {
                ty_ctx.extend_from_eclmap(path, &eclmap)
            },
            Err(e) => {
                ecl_parser::error!(message("{}", e), primary(path_literal, "error loading file")).emit(&files).expect("error while writing errors?!");
                return false;
            }
        }
    }
    let std = match ecl_parser::anm::AnmFile::compile(game, &script, &ty_ctx) {
        Ok(x) => x,
        Err(mut es) => {
            es.emit(&files).expect("error while writing errors?!");
            return false;
        },
    };

    let mut out = std::fs::File::create(output).unwrap();
    ecl_parser::std::write_std(game, &mut out, &std).unwrap();
    true
}
