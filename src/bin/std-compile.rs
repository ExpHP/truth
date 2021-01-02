use ecl_parser::{self};

fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![input, output, mapfile, game] = cli::cli(
        "FILE -g GAME -o OUTPUT [OPTIONS...]",
        args![cli::input(), cli::required_output(), cli::mapfile(), cli::game()],
    );

    if !run(game, &input, output, mapfile) {
        std::process::exit(1);
    }
}

fn run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    output: impl AsRef<std::path::Path>,
    map_path: Option<impl AsRef<std::path::Path>>,
) -> bool {
    let mut ty_ctx = ecl_parser::type_system::TypeSystem::new();
    if let Some(map_path) = map_path {
        let eclmap = ecl_parser::Eclmap::load(&map_path, Some(game)).unwrap();
        ty_ctx.extend_from_eclmap(map_path.as_ref(), &eclmap);
    }

    let text = std::fs::read(&path).unwrap();
    let mut files = ecl_parser::pos::Files::new();
    let script = match files.parse::<ecl_parser::Script>(&path.as_ref().to_string_lossy(), &text) {
        Ok(x) => x,
        Err(e) => panic!("{}", e),
    };

    // FIXME nightmarish error handling
    for path_literal in &script.mapfiles {
        let path = match path_literal.as_path() {
            Ok(x) => x,
            Err(mut es) => {
                es.emit(&files).expect("error while writing errors?!");
                return false;
            },
        };
        match ecl_parser::Eclmap::load(&path, Some(game)) {
            Ok(eclmap) => {
                ty_ctx.extend_from_eclmap(path, &eclmap)
            },
            Err(e) => {
                ecl_parser::error!(message("{}", e), primary(path_literal, "error loading file")).emit(&files).expect("error while writing errors?!");
                return false;
            }
        }
    }
    let std = match ecl_parser::std::StdFile::compile(game, &script, &ty_ctx) {
        Ok(x) => x,
        Err(mut es) => {
            es.emit(&files).expect("error while writing errors?!");
            return false;
        },
    };

    let mut out = std::fs::File::create(output).unwrap();
    ecl_parser::std::write_std(&mut out, game, &std).unwrap();
    true
}
