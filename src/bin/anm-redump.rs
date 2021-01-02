use anyhow::Context;

use ecl_parser::{self, CompileError};

fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![input, output, game] = cli::cli(
        "FILE -g GAME -o OUTPUT [OPTIONS...]",
        args![cli::input(), cli::required_output(), cli::game()],
    );

    if !run(game, &input, output) {
        std::process::exit(1);
    }
}

fn run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    outpath: impl AsRef<std::path::Path>,
) -> bool {
    match _run(game, path, outpath) {
        Ok(()) => true,
        Err(mut e) => {
            e.emit_nospans();
            false
        }
    }
}

fn _run(
    game: ecl_parser::Game,
    path: impl AsRef<std::path::Path>,
    outpath: impl AsRef<std::path::Path>,
) -> Result<(), CompileError> {
    let bytes = std::fs::read(&path).unwrap();
    let anm_file = {
        ecl_parser::anm::read_anm(game, &bytes)
            .with_context(|| format!("in file: {}", path.as_ref().display()))?
    };

    let mut buf = std::io::Cursor::new(vec![]);
    ecl_parser::anm::write_anm(&mut buf, game, &anm_file)?;

    std::fs::write(outpath, buf.into_inner())?;
    Ok(())
}
