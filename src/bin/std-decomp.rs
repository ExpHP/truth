use ecl_parser::{self, Format, CompileError};

use anyhow::Context;
fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![input, max_columns, mapfile, game] = cli::cli(
        "FILE -g GAME [OPTIONS...]",
        args![cli::input(), cli::max_columns(), cli::mapfile(), cli::game()],
    );
    run(game, &input, max_columns, mapfile);
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
        if let Some(map_path) = map_path.or_else(|| Eclmap::default_map_file(".stdm")) {
            let eclmap = Eclmap::load(&map_path, Some(game)).unwrap();
            ty_ctx.extend_from_eclmap(&map_path, &eclmap);
        }
        ty_ctx
    };

    let script = {
        let bytes = std::fs::read(&path).unwrap();
        let parsed = {
            ecl_parser::StdFile::read_from_bytes(game, &bytes)
                .with_context(|| format!("in file: {}", path.as_ref().display()))
        };
        match parsed {
            Ok(parsed) => parsed.decompile_to_ast(game, &ty_ctx),
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
