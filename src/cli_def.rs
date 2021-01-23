// FIXME cleanup this file;
//       for now I just made modules with the contents of the individual files that used to exist in bin/
//       in order to speed up test compilation, without doing any cleanup.
//       I want to change the structure of the commands to be 'truanm' and 'trustd' anyways so
//       we'll have to do some refactoring then

use std::path::{Path, PathBuf};
use std::fs;
use std::io;
use anyhow::Context;
use crate::game::Game;
use crate::error::CompileError;

pub fn main() -> ! {
    let mut args = std::env::args();
    let _ = args.next();

    let subcommands: Vec<(&str, fn() -> !, bool)> = vec![
        ("anm-decompile", anm_decompile::main, true),
        ("anm-compile", anm_compile::main, true),
        ("anm-redump", anm_redump::main, false),
        ("anm-benchmark", anm_benchmark::main, false),
        ("ecl-reformat", ecl_reformat::main, false),
        ("std-decompile", std_decompile::main, true),
        ("std-compile", std_compile::main, true),
    ];

    let err_with_usage = || -> ! {
        let mut usage_or_align = "usage: ";
        for &(subcommand, _, public) in &subcommands {
            if public {
                eprintln!("{} truth {} ARGS...", usage_or_align, subcommand);
                usage_or_align = "       ";
            }
        }
        std::process::exit(1);
    };

    let user_subcommand = args.next().unwrap_or_else(|| err_with_usage());
    for &(subcommand, function, _) in &subcommands {
        if subcommand == user_subcommand {
            function();
        }
    }

    err_with_usage();
}

pub mod ecl_reformat {
    use super::*;

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

        let args_pat![input, ] = cli::cli(
            "FILE [OPTIONS...]", args![cli::input()],
        );

        run(input);
        std::process::exit(0);
    }

    fn run(path: impl AsRef<Path>) {
        let mut files = crate::Files::new();
        let script = match files.read_file::<crate::ast::Script>(path.as_ref()) {
            Ok(x) => x,
            Err(mut e) => {
                let _ = e.emit(&files);
                std::process::exit(1);
            },
        };
        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock()));
        f.fmt(&script).unwrap();
    }
}

pub mod anm_decompile {
    use super::*;
    use crate::{Format};

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

        let args_pat![input, max_columns, mapfile, game] = cli::cli(
            "FILE -g GAME [OPTIONS...]",
            args![cli::input(), cli::max_columns(), cli::mapfile(), cli::game()],
        );
        run(game, &input, max_columns, mapfile);
        std::process::exit(0);
    }

    fn run(
        game: crate::Game,
        path: impl AsRef<Path>,
        ncol: usize,
        map_path: Option<impl AsRef<Path>>,
    ) {
        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock())).with_max_columns(ncol);
        _run(&mut f, game, path, map_path)
    }

    pub(super) fn _run(
        out: &mut crate::Formatter<impl io::Write>,
        game: crate::Game,
        path: impl AsRef<Path>,
        map_path: Option<impl AsRef<Path>>,
    ) {
        let ty_ctx = {
            use crate::Eclmap;

            let mut ty_ctx = crate::type_system::TypeSystem::new();

            ty_ctx.extend_from_eclmap(None, &Eclmap::parse(&crate::anm::game_core_mapfile(game)).unwrap());

            let map_path = map_path.map(|p| p.as_ref().to_owned());
            if let Some(map_path) = map_path.or_else(|| Eclmap::decomp_map_file_from_env(".anmm")) {
                let eclmap = Eclmap::load(&map_path, Some(game)).unwrap();
                ty_ctx.extend_from_eclmap(Some(&map_path), &eclmap);
            }
            ty_ctx
        };

        let script = {
            // tiny buffer due to seeking
            let reader = io::BufReader::with_capacity(64, fs::File::open(&path).unwrap());
            let anm_result = {
                crate::AnmFile::read_from_stream(reader, game, false)
                    .and_then(|anm| anm.decompile_to_ast(game, &ty_ctx, crate::DecompileKind::Fancy))
                    .with_context(|| format!("in file: {}", path.as_ref().display()))
            };

            match anm_result {
                Ok(anm) => anm,
                Err(e) => {
                    CompileError::from(e).emit_nospans();
                    std::process::exit(1); // FIXME skips RAII
                },
            }
        };

        script.fmt(out).unwrap();
    }
}

pub mod anm_compile {
    use super::*;

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

        let args_pat![script_path, game, output, mapfile, image_sources] = cli::cli(
            "SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            args![
                cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfile(), cli::image_sources(),
            ],
        );

        if !run(game, &script_path, &output, &image_sources, mapfile.as_ref().map(AsRef::as_ref)) {
            std::process::exit(1);
        }
        std::process::exit(0);
    }

    fn run(
        game: crate::Game,
        script_path: &Path,
        outpath: &Path,
        image_source_paths: &[PathBuf],
        map_path: Option<&Path>,
    ) -> bool {
        let mut files = crate::Files::new();
        match _run(&mut files, game, script_path, outpath, image_source_paths, map_path) {
            Ok(()) => true,
            Err(mut e) => { let _ = e.emit(&files); false }
        }
    }

    pub(super) fn _run(
        files: &mut crate::Files,
        game: crate::Game,
        script_path: &Path,
        outpath: &Path,
        cli_image_source_paths: &[PathBuf],
        map_path: Option<&Path>,
    ) -> Result<(), CompileError> {
        let mut ty_ctx = crate::type_system::TypeSystem::new();

        ty_ctx.extend_from_eclmap(None, &crate::Eclmap::parse(&crate::anm::game_core_mapfile(game)).unwrap());

        if let Some(map_path) = map_path {
            let eclmap = crate::Eclmap::load(&map_path, Some(game))?;
            ty_ctx.extend_from_eclmap(Some(map_path.as_ref()), &eclmap);
        }

        let ast = files.read_file::<crate::ast::Script>(&script_path)?;

        for path_literal in &ast.mapfiles {
            let path = path_literal.as_path()?;
            match crate::Eclmap::load(&path, Some(game)) {
                Ok(eclmap) => ty_ctx.extend_from_eclmap(Some(path), &eclmap),
                Err(e) => return Err(crate::error!(
                    message("{}", e), primary(path_literal, "error loading file"),
                )),
            }
        }

        let mut compiled = crate::AnmFile::compile_from_ast(game, &ast, &mut ty_ctx)?;

        // image sources referenced in file take precedence
        let mut image_source_paths = vec![];
        for path_literal in &ast.image_sources {
            image_source_paths.push(path_literal.as_path()?.to_owned());
        }
        image_source_paths.extend(cli_image_source_paths.iter().cloned());

        for image_source_path in image_source_paths.iter() {
            let reader = io::Cursor::new(fs::read(image_source_path).unwrap());
            let source_anm_file = {
                crate::AnmFile::read_from_stream(reader, game, true)
                    .with_context(|| format!("in file: {}", image_source_path.display()))?
            };
            compiled.apply_image_source(source_anm_file)?;
        }

        let out = fs::File::create(outpath).with_context(|| format!("creating file '{}'", outpath.display()))?;
        compiled.write_to_stream(&mut io::BufWriter::new(out), game)?;
        Ok(())
    }
}

pub mod anm_redump {
    use super::*;

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

        let args_pat![input, output, game] = cli::cli(
            "FILE -g GAME -o OUTPUT [OPTIONS...]",
            args![cli::input(), cli::required_output(), cli::game()],
        );

        if !run(game, &input, output) {
            std::process::exit(1);
        }
        std::process::exit(0);
    }

    fn run(
        game: Game,
        path: impl AsRef<Path>,
        outpath: impl AsRef<Path>,
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
        game: Game,
        path: impl AsRef<Path>,
        outpath: impl AsRef<Path>,
    ) -> Result<(), CompileError> {
        let reader = io::BufReader::new(fs::File::open(&path).unwrap());
        let anm_file = {
            crate::AnmFile::read_from_stream(reader, game, true)
                .with_context(|| format!("in file: {}", path.as_ref().display()))?
        };

        let mut buf = io::Cursor::new(vec![]);
        anm_file.write_to_stream(&mut buf, game)?;

        fs::write(outpath, buf.into_inner())?;
        Ok(())
    }
}

pub mod anm_benchmark {
    use super::*;

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

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
        std::process::exit(0);
    }

    fn run(
        game: crate::Game,
        anm_path: &Path,
        script_path: &Path,
        outpath: &Path,
        map_path: Option<&Path>,
    ) -> bool {
        let mut files = crate::Files::new();
        match _run(&mut files, game, anm_path, script_path, outpath, map_path) {
            Ok(()) => true,
            Err(mut e) => { let _ = e.emit(&files); false }
        }
    }

    fn _run(
        files: &mut crate::Files,
        game: crate::Game,
        anm_path: &Path,
        script_path: &Path,
        outpath: &Path,
        map_path: Option<&Path>,
    ) -> Result<(), CompileError> {
        let image_source_paths = [anm_path.to_owned()];
        loop {
            let script_out = fs::File::create(script_path).with_context(|| format!("creating file '{}'", script_path.display()))?;
            let mut f = crate::Formatter::new(io::BufWriter::new(script_out)).with_max_columns(100);
            super::anm_decompile::_run(&mut f, game, anm_path, map_path);
            drop(f);

            super::anm_compile::_run(files, game, script_path, outpath, &image_source_paths, map_path)?;
        }
    }
}

pub mod std_compile {
    use super::*;

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

        let args_pat![input, output, mapfile, game] = cli::cli(
            "FILE -g GAME -o OUTPUT [OPTIONS...]",
            args![cli::input(), cli::required_output(), cli::mapfile(), cli::game()],
        );

        if !run(game, &input, &output, mapfile.as_ref().map(AsRef::as_ref)) {
            std::process::exit(1);
        }
        std::process::exit(0);
    }

    fn run(
        game: crate::Game,
        path: &Path,
        outpath: &Path,
        map_path: Option<&Path>,
    ) -> bool {
        let mut files = crate::Files::new();
        match _run(&mut files, game, path, outpath, map_path) {
            Ok(()) => true,
            Err(mut e) => { let _ = e.emit(&files); false }
        }
    }

    fn _run(
        files: &mut crate::Files,
        game: crate::Game,
        path: &Path,
        outpath: &Path,
        map_path: Option<&Path>,
    ) -> Result<(), CompileError> {
        let mut ty_ctx = crate::type_system::TypeSystem::new();

        ty_ctx.extend_from_eclmap(None, &crate::Eclmap::parse(&crate::std::game_core_mapfile(game)).unwrap());

        if let Some(map_path) = map_path {
            let eclmap = crate::Eclmap::load(&map_path, Some(game)).unwrap();
            ty_ctx.extend_from_eclmap(Some(map_path.as_ref()), &eclmap);
        }

        let script = files.read_file::<crate::ast::Script>(&path)?;
        script.expect_no_image_sources()?;

        for path_literal in &script.mapfiles {
            let path = path_literal.as_path()?;
            match crate::Eclmap::load(&path, Some(game)) {
                Ok(eclmap) => ty_ctx.extend_from_eclmap(Some(path), &eclmap),
                Err(e) => return Err(crate::error!(
                    message("{}", e), primary(path_literal, "error loading file"),
                )),
            }
        }
        let std = crate::StdFile::compile_from_ast(game, &script, &mut ty_ctx)?;

        let out = fs::File::create(outpath).with_context(|| format!("creating file '{}'", outpath.display()))?;
        std.write_to_stream(&mut io::BufWriter::new(out), game).unwrap();
        Ok(())
    }
}

pub mod std_decompile {
    use super::*;
    use crate::{Format};

    pub fn main() -> ! {
        use crate::{cli_helper as cli, args, args_pat};

        let args_pat![input, max_columns, mapfile, game] = cli::cli(
            "FILE -g GAME [OPTIONS...]",
            args![cli::input(), cli::max_columns(), cli::mapfile(), cli::game()],
        );
        run(game, &input, max_columns, mapfile);
        std::process::exit(0);
    }

    fn run(
        game: Game,
        path: impl AsRef<Path>,
        ncol: usize,
        map_path: Option<impl AsRef<Path>>,
    ) {
        let ty_ctx = {
            use crate::Eclmap;

            let mut ty_ctx = crate::type_system::TypeSystem::new();

            ty_ctx.extend_from_eclmap(None, &Eclmap::parse(&crate::std::game_core_mapfile(game)).unwrap());

            let map_path = map_path.map(|p| p.as_ref().to_owned());
            if let Some(map_path) = map_path.or_else(|| Eclmap::decomp_map_file_from_env(".stdm")) {
                let eclmap = Eclmap::load(&map_path, Some(game)).unwrap();
                ty_ctx.extend_from_eclmap(Some(&map_path), &eclmap);
            }
            ty_ctx
        };

        let script = {
            let reader = io::Cursor::new(fs::read(&path).unwrap());
            let parsed = {
                crate::StdFile::read_from_stream(reader, game)
                    .and_then(|parsed| parsed.decompile_to_ast(game, &ty_ctx, crate::DecompileKind::Fancy))
                    .with_context(|| format!("in file: {}", path.as_ref().display()))
            };
            match parsed {
                Ok(x) => x,
                Err(e) => {
                    CompileError::from(e).emit_nospans();
                    std::process::exit(1); // FIXME skips RAII
                },
            }
        };

        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock())).with_max_columns(ncol);
        script.fmt(&mut f).unwrap();
    }
}
