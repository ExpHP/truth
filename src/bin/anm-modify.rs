use anyhow::Context;
use std::path::Path;

use ecl_parser::{self, CompileError};

fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![anm_path, script_path, game, output, mapfile] = cli::cli(
        "ANMFILE SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
        args![
            cli::path_arg("ANMFILE"), cli::path_arg("SCRIPT"),
            cli::game(), cli::required_output(), cli::mapfile(),
        ],
    );

    if !run(game, &anm_path, &script_path, &output, mapfile.as_ref().map(AsRef::as_ref)) {
        std::process::exit(1);
    }
}

fn run(
    game: ecl_parser::Game,
    anm_path: &Path,
    script_path: &Path,
    outpath: &Path,
    map_path: Option<&Path>,
) -> bool {
    let mut files = ecl_parser::Files::new();
    match _run(&mut files, game, anm_path, script_path, outpath, map_path) {
        Ok(()) => true,
        Err(mut e) => { let _ = e.emit(&files); false }
    }
}

fn _run(
    files: &mut ecl_parser::Files,
    game: ecl_parser::Game,
    anm_path: &Path,
    script_path: &Path,
    outpath: &Path,
    map_path: Option<&Path>,
) -> Result<(), CompileError> {
    let mut ty_ctx = ecl_parser::type_system::TypeSystem::new();
    if let Some(map_path) = map_path {
        let eclmap = ecl_parser::Eclmap::load(&map_path, Some(game))?;
        ty_ctx.extend_from_eclmap(map_path.as_ref(), &eclmap);
    }

    let ast = files.read_file::<ecl_parser::Script>(&script_path)?;
    for path_literal in &ast.mapfiles {
        let path = path_literal.as_path()?;
        match ecl_parser::Eclmap::load(&path, Some(game)) {
            Ok(eclmap) => ty_ctx.extend_from_eclmap(path, &eclmap),
            Err(e) => return Err(ecl_parser::error!(
                message("{}", e), primary(path_literal, "error loading file"),
            )),
        }
    }

    let bytes = std::fs::read(&anm_path).unwrap();
    let mut anm_file = {
        ecl_parser::AnmFile::read_from_bytes(game, &bytes)
            .with_context(|| format!("in file: {}", anm_path.display()))?
    };

    let compiled_ast = ecl_parser::AnmFile::compile_from_ast(game, &ast, &ty_ctx)?;
    anm_file.merge(&compiled_ast)?;

    let mut buf = std::io::Cursor::new(vec![]);
    anm_file.write_to_stream(&mut buf, game)?;

    std::fs::write(outpath, buf.into_inner())?;
    Ok(())
}
