use std::path::Path;
use ecl_parser::{self, CompileError};
use anyhow::Context;

fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![input, output, mapfile, game] = cli::cli(
        "FILE -g GAME -o OUTPUT [OPTIONS...]",
        args![cli::input(), cli::required_output(), cli::mapfile(), cli::game()],
    );

    if !run(game, &input, &output, mapfile.as_ref().map(AsRef::as_ref)) {
        std::process::exit(1);
    }
}

fn run(
    game: ecl_parser::Game,
    path: &Path,
    outpath: &Path,
    map_path: Option<&Path>,
) -> bool {
    let mut files = ecl_parser::Files::new();
    match _run(&mut files, game, path, outpath, map_path) {
        Ok(()) => true,
        Err(mut e) => { let _ = e.emit(&files); false }
    }
}

fn _run(
    files: &mut ecl_parser::Files,
    game: ecl_parser::Game,
    path: &Path,
    outpath: &Path,
    map_path: Option<&Path>,
) -> Result<(), CompileError> {
    let mut ty_ctx = ecl_parser::type_system::TypeSystem::new();
    if let Some(map_path) = map_path {
        let eclmap = ecl_parser::Eclmap::load(&map_path, Some(game)).unwrap();
        ty_ctx.extend_from_eclmap(map_path.as_ref(), &eclmap);
    }

    let script = files.read_file::<ecl_parser::Script>(&path)?;

    for path_literal in &script.mapfiles {
        let path = path_literal.as_path()?;
        match ecl_parser::Eclmap::load(&path, Some(game)) {
            Ok(eclmap) => ty_ctx.extend_from_eclmap(path, &eclmap),
            Err(e) => return Err(ecl_parser::error!(
                message("{}", e), primary(path_literal, "error loading file"),
            )),
        }
    }
    let std = ecl_parser::StdFile::compile_from_ast(game, &script, &mut ty_ctx)?;

    let mut out = std::fs::File::create(outpath).with_context(|| format!("creating file '{}'", outpath.display()))?;
    std.write_to_stream(&mut out, game).unwrap();
    Ok(())
}
