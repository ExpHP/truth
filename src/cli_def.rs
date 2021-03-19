use std::path::{Path, PathBuf};
use std::fs;
use std::io;
use crate::ast;
use crate::game::Game;
use crate::io::{BinReader, BinWriter};
use crate::diagnostic::DiagnosticEmitter;
use crate::context::BinContext;
use crate::error::{CompileError, SimpleError};
use crate::pos::Files;

pub fn main(version: &str) -> ! {
    let mut args = std::env::args();
    let _ = args.next();
    truth_main(version, &args.collect::<Vec<_>>());
}


type EntryPoint = fn(version: &str, args: &[String]) -> !;


pub fn truth_main(version: &str, args: &[String]) -> ! {
    cli::parse_subcommand(version, &args, Subcommands {
        abbreviations: cli::Abbreviations::Forbid,
        program: "truth-core",
        choices: &[
            SubcommandSpec { name: "truanm", entry: truanm_main, public: true },
            SubcommandSpec { name: "trustd", entry: trustd_main, public: true },
            SubcommandSpec { name: "trumsg", entry: trumsg_main, public: true },
            SubcommandSpec { name: "anm-benchmark", entry: anm_benchmark::main, public: false },
            SubcommandSpec { name: "ecl-reformat", entry: ecl_reformat::main, public: false },
            SubcommandSpec { name: "msg-redump", entry: msg_redump::main, public: false },
        ],
    })
}


pub fn truanm_main(version: &str, args: &[String]) -> ! {
    cli::parse_subcommand(version, &args, Subcommands {
        abbreviations: cli::Abbreviations::Allow,
        program: "truanm",
        choices: &[
            SubcommandSpec { name: "decompile", entry: anm_decompile::main, public: true },
            SubcommandSpec { name: "compile", entry: anm_compile::main, public: true },
        ],
    })
}


pub fn trustd_main(version: &str, args: &[String]) -> ! {
    cli::parse_subcommand(version, &args, Subcommands {
        abbreviations: cli::Abbreviations::Allow,
        program: "trustd",
        choices: &[
            SubcommandSpec { name: "decompile", entry: std_decompile::main, public: true },
            SubcommandSpec { name: "compile", entry: std_compile::main, public: true },
        ],
    })
}


pub fn trumsg_main(version: &str, args: &[String]) -> ! {
    cli::parse_subcommand(version, &args, Subcommands {
        abbreviations: cli::Abbreviations::Allow,
        program: "trumsg",
        choices: &[
            SubcommandSpec { name: "decompile", entry: msg_decompile::main, public: true },
            SubcommandSpec { name: "compile", entry: msg_compile::main, public: true },
        ],
    })
}


pub mod ecl_reformat {
    use super::*;

    pub fn main(version: &str, argv: &[String]) -> ! {
        let (input,) = cli::parse_args(version, argv, CmdSpec {
            program: "truth-core ecl-reformat",
            usage_args: "FILE [OPTIONS...]",
            options: (cli::input(),),
        });

        wrap_fancy_errors(|files| run(files, input));
    }

    fn run(files: &mut Files, path: impl AsRef<Path>) -> Result<(), CompileError> {
        let script = files.read_file::<ast::Script>(path.as_ref())?;

        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock()));
        f.fmt(&script)?;
        Ok(())
    }
}

pub mod anm_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, max_columns, mapfile, game) = cli::parse_args(version, args, CmdSpec {
            program: "truanm decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::max_columns(), cli::mapfile(), cli::game()),
        });

        let stdout = io::stdout();
        wrap_fancy_errors(|_files| {
            let fmt_config = crate::fmt::Config::new().max_columns(max_columns);
            let mut f = crate::Formatter::with_config(io::BufWriter::new(stdout.lock()), fmt_config);
            run(&mut f, game, input.as_ref(), mapfile)
        });
    }

    pub(super) fn run(
        out: &mut crate::Formatter<impl io::Write>,
        game: Game,
        path: &Path,
        map_path: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let map_path = maybe_use_default_mapfile_for_decomp(map_path, ".anmm");
        let ctx = init_context(game, map_path, crate::anm::game_core_mapfile(game))?;
        let bcx = ctx.to_bin_context();

        let script = {
            // Here we don't read the whole thing because seeking can skip costly reads of megabytes of image data.
            //
            // Seeking drops the buffer though, so use a tiny buffer.
            let mut reader = BinReader::open(&bcx, path)?.map_reader(|r| io::BufReader::with_capacity(64, r));
            crate::AnmFile::read_from_stream(&mut reader, game, false)
                .and_then(|anm| anm.decompile_to_ast(game, &ctx, crate::DecompileKind::Fancy))?
        };

        out.fmt(&script)?;
        Ok(())
    }
}

pub mod anm_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (script_path, game, output, mapfile, image_sources, output_thecl_defs) = cli::parse_args(version, args, CmdSpec {
            program: "truanm compile",
            usage_args: "SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfile(), cli::image_sources(),
                cli::output_thecl_defs(),
            ),
        });

        wrap_fancy_errors(|files| run(files, game, &script_path, &output, &image_sources, mapfile, output_thecl_defs));
    }

    pub(super) fn run(
        files: &mut Files,
        game: Game,
        script_path: &Path,
        outpath: &Path,
        cli_image_source_paths: &[PathBuf],
        map_path: Option<PathBuf>,
        output_thecl_defs: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let mut ctx = init_context(game, map_path, crate::anm::game_core_mapfile(game))?;
        let bcx = ctx.to_bin_context();

        let ast = files.read_file::<ast::Script>(&script_path)?;

        load_mapfiles_from_pragmas(game, &mut ctx, &ast)?;

        let mut compiled = crate::AnmFile::compile_from_ast(game, &ast, &mut ctx)?;

        // image sources referenced in file take precedence
        let mut image_source_paths = vec![];
        for path_literal in &ast.image_sources {
            image_source_paths.push(PathBuf::from(path_literal.string.clone()));
        }
        image_source_paths.extend(cli_image_source_paths.iter().cloned());

        for image_source_path in image_source_paths.iter() {
            let source_anm_file = {
                crate::AnmFile::read_from_stream(&mut BinReader::read(&bcx, image_source_path)?, game, true)?
            };
            compiled.apply_image_source(source_anm_file)?;
        }

        compiled.write_to_stream(&mut BinWriter::create_buffered(&bcx, outpath)?, game)?;

        if let Some(outpath) = output_thecl_defs {
            use anyhow::Context; // FIXME remove

            compiled.write_thecl_defs(io::BufWriter::new(fs_create(&outpath)?))
                .with_context(|| format!("while writing '{}'", outpath.display()))
                .map_err(|e| ctx.diagnostics.emit(error!("{:#}", e)))?;
        }

        Ok(())
    }
}

pub mod anm_redump {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, game) = cli::parse_args(version, args, CmdSpec {
            program: "truth-core anm-redump",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::game()),
        });

        wrap_fancy_errors(|_| run(game, input.as_ref(), output.as_ref()))
    }

    fn run(
        game: Game,
        path: &Path,
        outpath: &Path,
    ) -> Result<(), CompileError> {
        let bcx = BinContext::from_diagnostic_emitter(DiagnosticEmitter::new_stderr());
        let anm_file = crate::AnmFile::read_from_stream(&mut BinReader::read(&bcx, path)?, game, true)?;

        anm_file.write_to_stream(&mut BinWriter::create_buffered(&bcx, outpath)?, game)?;
        Ok(())
    }
}

pub mod anm_benchmark {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (anm_path, script_path, game, output, mapfile) = cli::parse_args(version, args, CmdSpec {
            program: "truth-core anm-benchmark",
            usage_args: "ANMFILE SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("ANMFILE"), cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfile(),
            ),
        });

        wrap_fancy_errors(|files| run(files, game, &anm_path, &script_path, &output, mapfile))
    }

    fn run(
        files: &mut Files,
        game: Game,
        anm_path: &Path,
        script_path: &Path,
        outpath: &Path,
        map_path: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let image_source_paths = [anm_path.to_owned()];
        loop {
            use anyhow::Context; // FIXME remove

            let fmt_config = crate::fmt::Config::new().max_columns(100);
            let script_out = fs::File::create(script_path).with_context(|| format!("creating file '{}'", script_path.display()))?;
            let mut f = crate::Formatter::with_config(io::BufWriter::new(script_out), fmt_config);
            super::anm_decompile::run(&mut f, game, anm_path, map_path.clone())?;
            drop(f);

            super::anm_compile::run(files, game, script_path, outpath, &image_source_paths, map_path.clone(), None)?;
        }
    }
}

pub mod std_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, mapfile, game) = cli::parse_args(version, args, CmdSpec {
            program: "trustd compile",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::mapfile(), cli::game()),
        });

        wrap_fancy_errors(|files| run(files, game, &input, &output, mapfile));
    }

    fn run(
        files: &mut Files,
        game: Game,
        path: &Path,
        outpath: &Path,
        map_path: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let mut ctx = init_context(game, map_path, crate::std::game_core_mapfile(game))?;
        let bcx = ctx.to_bin_context();

        let script = files.read_file::<ast::Script>(&path)?;
        load_mapfiles_from_pragmas(game, &mut ctx, &script)?;
        script.expect_no_image_sources()?;

        let std = crate::StdFile::compile_from_ast(game, &script, &mut ctx)?;

        std.write_to_stream(&mut BinWriter::create_buffered(&bcx, outpath)?, game)?;
        Ok(())
    }
}

pub mod std_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, max_columns, mapfile, game) = cli::parse_args(version, args, CmdSpec {
            program: "trustd decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::max_columns(), cli::mapfile(), cli::game()),
        });
        wrap_fancy_errors(|_files| run(game, &input, max_columns, mapfile))
    }

    fn run(
        game: Game,
        path: &Path,
        ncol: usize,
        map_path: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let map_path = maybe_use_default_mapfile_for_decomp(map_path, ".stdm");
        let ctx = init_context(game, map_path, crate::std::game_core_mapfile(game))?;
        let bcx = ctx.to_bin_context();

        let script = {
            crate::StdFile::read_from_stream(&mut BinReader::read(&bcx, path)?, game)
                .and_then(|parsed| parsed.decompile_to_ast(game, &ctx, crate::DecompileKind::Fancy))?
        };

        let stdout = io::stdout();
        let fmt_config = crate::fmt::Config::new().max_columns(ncol);
        let mut f = crate::Formatter::with_config(io::BufWriter::new(stdout.lock()), fmt_config);
        f.fmt(&script)?;
        Ok(())
    }
}

pub mod msg_redump {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, game) = cli::parse_args(version, args, CmdSpec {
            program: "truth-core msg-redump",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::game()),
        });

        wrap_fancy_errors(|_| run(game, input.as_ref(), output.as_ref()))
    }

    fn run(
        game: Game,
        path: &Path,
        outpath: &Path,
    ) -> Result<(), CompileError> {
        let bcx = BinContext::from_diagnostic_emitter(DiagnosticEmitter::new_stderr());
        let msg_file = crate::MsgFile::read_from_stream(&mut BinReader::read(&bcx, &path)?, game)?;

        msg_file.write_to_stream(&mut BinWriter::create_buffered(&bcx, outpath)?, game)?;
        Ok(())
    }
}

pub mod msg_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, mapfile, game) = cli::parse_args(version, args, CmdSpec {
            program: "trumsg compile",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::mapfile(), cli::game()),
        });

        wrap_fancy_errors(|files| run(files, game, &input, &output, mapfile));
    }

    fn run(
        files: &mut Files,
        game: Game,
        path: &Path,
        outpath: &Path,
        map_path: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let mut ctx = init_context(game, map_path, crate::msg::game_core_mapfile(game))?;
        let bcx = ctx.to_bin_context();

        let script = files.read_file::<ast::Script>(&path)?;
        load_mapfiles_from_pragmas(game, &mut ctx, &script)?;
        script.expect_no_image_sources()?;

        let std = crate::MsgFile::compile_from_ast(game, &script, &mut ctx)?;

        std.write_to_stream(&mut BinWriter::create_buffered(&bcx, outpath)?, game)?;
        Ok(())
    }
}

pub mod msg_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, max_columns, mapfile, game) = cli::parse_args(version, args, CmdSpec {
            program: "trumsg decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::max_columns(), cli::mapfile(), cli::game()),
        });
        wrap_fancy_errors(|_files| run(game, &input, max_columns, mapfile))
    }

    fn run(
        game: Game,
        path: &Path,
        ncol: usize,
        map_path: Option<PathBuf>,
    ) -> Result<(), CompileError> {
        let map_path = maybe_use_default_mapfile_for_decomp(map_path, ".msgm");
        let ctx = init_context(game, map_path, crate::msg::game_core_mapfile(game))?;
        let bcx = ctx.to_bin_context();

        let script = {
            crate::MsgFile::read_from_stream(&mut BinReader::read(&bcx, path)?, game)
                .and_then(|parsed| parsed.decompile_to_ast(game, &ctx, crate::DecompileKind::Fancy))?
        };

        let stdout = io::stdout();
        let fmt_config = crate::fmt::Config::new().max_columns(ncol);
        let mut f = crate::Formatter::with_config(io::BufWriter::new(stdout.lock()), fmt_config);
        f.fmt(&script)?;
        Ok(())
    }
}

// =============================================================================

/// Implements the automatic searching of the environment during decompilation when there's no `-m`.
fn maybe_use_default_mapfile_for_decomp(
    mapfile_arg: Option<PathBuf>,
    mapfile_extension: &'static str,
) -> Option<PathBuf> {
    mapfile_arg.or_else(|| crate::Eclmap::decomp_map_file_from_env(mapfile_extension))
}

/// Loads the user's mapfile and the core mapfile.
fn init_context(
    game: Game,
    mapfile_arg: Option<PathBuf>,
    core_mapfile_source: &str,
) -> Result<crate::CompilerContext, CompileError> {
    use crate::Eclmap;

    let mut ctx = crate::CompilerContext::new_stderr();
    ctx.extend_from_eclmap(None, &Eclmap::parse(core_mapfile_source, &ctx.diagnostics)?).expect("failed to parse core mapfile!?");

    if let Some(mapfile_arg) = mapfile_arg {
        use anyhow::Context; // FIXME remove

        let eclmap = Eclmap::load(&mapfile_arg, Some(game), &ctx.diagnostics)?;
        ctx.extend_from_eclmap(Some(&mapfile_arg), &eclmap)
            .with_context(|| format!("while applying '{}'", mapfile_arg.display()))?;
    }
    Ok(ctx)
}

/// Loads mapfiles from a parsed script.
fn load_mapfiles_from_pragmas(game: Game, ctx: &mut crate::CompilerContext, script: &ast::Script) -> Result<(), CompileError> {
    for path_literal in &script.mapfiles {
        let path: &Path = path_literal.string.as_ref();

        crate::error::group_anyhow(|| {
            let eclmap = crate::Eclmap::load(&path, Some(game), &ctx.diagnostics)?;
            ctx.extend_from_eclmap(Some(path), &eclmap)?;
            Ok(())
        }).map_err(|e| crate::error!(
            message("{:#}", e), primary(path_literal, "error loading mapfile"),
        ))?
    }
    Ok(())
}

// =============================================================================

fn fs_create(path: impl AsRef<Path>) -> Result<fs::File, SimpleError> {
    use anyhow::Context; // FIXME remove

    fs::File::create(path.as_ref()).with_context(|| format!("creating file '{}'", path.as_ref().display()))
}

fn wrap_fancy_errors(func: impl FnOnce(&mut Files) -> Result<(), CompileError>) -> ! {
    let mut files = Files::new();
    match func(&mut files) {
        Ok(()) => std::process::exit(0),
        Err(mut e) => {
            let _ = e.emit(&files);
            std::process::exit(1);
        }
    }
}

// =============================================================================

use cli::{CmdSpec, Subcommands, SubcommandSpec};

mod cli {
    use super::*;
    use anyhow::anyhow;
    use getopts::{Options, Matches};

    pub fn mapfile() -> impl CliArg<Value=Option<PathBuf>> {
        opts::Opt {
            short: "m", long: "map", metavar: "MAPFILE",
            help: "use a mapfile to translate instruction names and argument types",
        }.map(|opt| opt.map(Into::into))
    }

    pub fn required_output() -> impl CliArg<Value=PathBuf> {
        opts::ReqOpt(opts::Opt {
            short: "o", long: "output", metavar: "OUTPUT",
            help: "output file",
        }).map(Into::into)
    }

    pub fn game() -> impl CliArg<Value=Game> {
        opts::ReqOpt(opts::Opt {
            short: "g", long: "game", metavar: "GAME",
            help: "game number, e.g. 'th095' or '8'. Don't include a point in point titles. Also supports 'alcostg'.",
        }).and_then(|s| s.parse().map_err(Into::into))
    }

    pub fn max_columns() -> impl CliArg<Value=usize> {
        opts::Opt {
            short: "", long: "max-columns", metavar: "NUM",
            help: "where possible, will attempt to break lines for < NUM columns",
        }.and_then(|s| s.unwrap_or_else(|| "100".to_string()).parse().map_err(Into::into))
    }

    pub fn path_arg(s: &'static str) -> impl CliArg<Value=PathBuf> {
        opts::Positional { metavar: s }.map(Into::into)
    }

    pub fn input() -> impl CliArg<Value=PathBuf> { path_arg("INPUT") }

    pub fn image_sources() -> impl CliArg<Value=Vec<PathBuf>> {
        opts::MultiOpt(opts::Opt {
            short: "i", long: "image-source", metavar: "ANMFILE",
            help: "supply an existing ANM file to copy any missing embedded images and header data from",
        }).map(|strs| strs.into_iter().map(Into::into).collect())
    }

    pub fn output_thecl_defs() -> impl CliArg<Value=Option<PathBuf>> {
        opts::Opt {
            short: "", long: "output-thecl-defs", metavar: "FILE",
            help: "write a file defining globals for anm scripts for use in thecl",
        }.map(|opt| opt.map(Into::into))
    }

    pub enum Abbreviations { Allow, Forbid }

    pub struct CmdSpec<A> {
        pub program: &'static str,
        pub usage_args: &'static str,
        pub options: A,
    }

    pub fn parse_args<A: CliArg>(
        version: &str,
        args: &[String],
        CmdSpec { program, usage_args, options }: CmdSpec<A>,
    ) -> A::Value {
        match _parse_args(args, options) {
            Ok(arg_values) => arg_values,

            Err(ParseError::PrintHelp(opts)) => {
                print_help(&program, usage_args, &opts);
                std::process::exit(0);
            },

            Err(ParseError::PrintVersion) => {
                print_version(version);
                std::process::exit(0);
            },

            Err(ParseError::Error(e)) => {
                print_usage(&program, usage_args);
                eprintln!();

                let _: &anyhow::Error = &e;  // just showing that 'e' is a type with no spans
                CompileError::from(e).emit_nospans();
                std::process::exit(1);
            },
        }
    }

    pub struct Subcommands {
        pub program: &'static str,
        pub abbreviations: Abbreviations,
        pub choices: &'static [SubcommandSpec],
    }

    pub struct SubcommandSpec {
        pub name: &'static str,
        pub entry: EntryPoint,

        /// Whether to show in usage.
        pub public: bool,
    }

    pub fn parse_subcommand(
        version: &str,
        args: &[String],
        subcommands: Subcommands,
    ) -> ! {
        match _parse_args(&args, &subcommands) {
            // parsing will automatically call the subcommand so this is unreachable...
            Ok((entry_point, remaining_args)) => entry_point(version, &remaining_args),

            Err(ParseError::PrintHelp(_)) => {
                subcommands.show_usage();
                std::process::exit(0);
            },

            Err(ParseError::PrintVersion) => {
                print_version(version);
                std::process::exit(0);
            },

            Err(ParseError::Error(e)) => {
                subcommands.show_usage();
                eprintln!();

                let _: &anyhow::Error = &e;  // just showing that 'e' is a type with no spans
                CompileError::from(e).emit_nospans();
                std::process::exit(1);
            },
        }
    }

    fn print_usage(program: &str, usage_args: &str) {
        eprintln!("Usage: {} {}", program, usage_args);
    }
    fn print_help(program: &str, usage_args: &str, opts: &getopts::Options) {
        eprint!("{}", opts.usage(&format!("Usage: {} {}", program, usage_args)));
    }
    fn print_version(version: &str) {
        eprintln!("truth {}", version);
    }

    pub type ArgError = SimpleError;
    pub trait CliArg {
        type Value;
        fn add_to_options(&self, opts: &mut getopts::Options);
        /// NOTE: `matches.free` is in reverse order, so you can call `Vec::pop` to extract them.
        fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError>;

        fn map<B, F: Fn(Self::Value) -> B>(self, func: F) -> Map<Self, F>
        where
            Self: Sized,
            F: Fn(Self::Value) -> B,
        { Map(self, func) }

        fn and_then<B, F>(self, func: F) -> AndThen<Self, F>
        where
            Self: Sized,
            F: Fn(Self::Value) -> Result<B, ArgError>,
        { AndThen(self, func) }
    }

    pub struct Map<A, F>(A, F);
    impl<A: CliArg, B, F: Fn(A::Value) -> B> CliArg for Map<A, F> {
        type Value = B;

        fn add_to_options(&self, opts: &mut Options) {
            self.0.add_to_options(opts)
        }
        fn extract_value(&self, matches: &mut Matches) -> Result<Self::Value, ArgError> {
            self.0.extract_value(matches).map(&self.1)
        }
    }

    pub struct AndThen<A, F>(A, F);
    impl<A: CliArg, B, F: Fn(A::Value) -> Result<B, ArgError>> CliArg for AndThen<A, F> {
        type Value = B;

        fn add_to_options(&self, opts: &mut Options) {
            self.0.add_to_options(opts)
        }
        fn extract_value(&self, matches: &mut Matches) -> Result<Self::Value, ArgError> {
            self.0.extract_value(matches).and_then(&self.1)
        }
    }

    impl<A: CliArg> CliArg for &A {
        type Value = A::Value;

        fn add_to_options(&self, opts: &mut Options) {
            (**self).add_to_options(opts)
        }
        fn extract_value(&self, matches: &mut Matches) -> Result<Self::Value, ArgError> {
            (**self).extract_value(matches)
        }
    }

    enum ParseError { Error(ArgError), PrintHelp(getopts::Options), PrintVersion }

    // factors out the parts where we want usage with errors
    fn _parse_args<A: CliArg>(args: &[String], arg_parsers: A) -> Result<A::Value, ParseError> {
        let mut opts = getopts::Options::new();
        opts.optflag("h", "help", "print this help menu");
        opts.optflag("", "version", "print version info");
        arg_parsers.add_to_options(&mut opts);

        let mut matches = opts.parse(args).map_err(|e| ParseError::Error(anyhow!("{}", e)))?;
        if matches.opt_present("h") {
            return Err(ParseError::PrintHelp(opts));
        }
        if matches.opt_present("version") {
            return Err(ParseError::PrintVersion);
        }

        matches.free.reverse();

        let out = arg_parsers.extract_value(&mut matches).map_err(ParseError::Error)?;

        if let Some(unexpected_pos) = matches.free.pop() {
            return Err(ParseError::Error(anyhow!("unexpected positional: {:?}", unexpected_pos)));
        }

        Ok(out)
    }

    macro_rules! impl_args_tuple {
        () => {};
        ($a0:ident : $A0:ident $(, $a:ident : $A:ident)*) => {
            impl_args_tuple!(@one $a0: $A0 $(, $a: $A)*);
            impl_args_tuple!($($a: $A),*);
        };
        (@one $($a:ident : $A:ident),+) => {
            impl<$($A: CliArg),+> CliArg for ( $($A,)+ ) {
                type Value = ( $($A::Value,)+ );

                fn add_to_options(&self, options: &mut getopts::Options) {
                    let ( $($a,)+ ) = self;
                    $( $a.add_to_options(options); )+
                }

                fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                    let ( $($a,)+ ) = self;
                    $( let $a = $a.extract_value(matches)?; )+
                    Ok(( $($a,)+ ))
                }
            }
        }
    }
    impl_args_tuple!(a:A, b:B, c:C, d:D, e:E, f:F, g:G, h:H, i:I, j:J);

    impl CliArg for Subcommands {
        type Value = (EntryPoint, Vec<String>);

        fn add_to_options(&self, opts: &mut getopts::Options) {
            opts.parsing_style(getopts::ParsingStyle::StopAtFirstFree);
        }

        fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
            let selection = matches.free.pop().ok_or_else(|| anyhow!("please choose a subcommand"))?;
            matches.free.reverse();  // back into forwards order
            let remaining_args = matches.free.drain(..).collect();

            let is_applicable: Box<dyn Fn(&str) -> bool> = match self.abbreviations {
                Abbreviations::Allow => Box::new(|name| name.starts_with(&selection)),
                Abbreviations::Forbid => Box::new(|name| name == &selection),
            };

            let choices = self.choices.iter().filter(|choice| is_applicable(choice.name)).collect::<Vec<_>>();
            match choices.len() {
                0 => anyhow::bail!("invalid subcommand '{}'", selection),
                1 => {},
                _ => anyhow::bail!("ambiguous subcommand '{}'", selection),
            };

            let entry_point = choices.into_iter().next().unwrap().entry;
            Ok((entry_point, remaining_args))
        }
    }

    impl Subcommands {
        pub fn show_usage(&self) {
            let mut usage_or_align = "usage: ";
            for choice in self.choices {
                if choice.public {
                    eprintln!("{} {} {} ARGS...", usage_or_align, self.program, choice.name);
                    usage_or_align = "       ";
                }
            }
        }
    }

    pub mod opts {
        pub use super::*;

        pub struct Opt {
            pub short: &'static str,
            pub long: &'static str,
            pub metavar: &'static str,
            pub help: &'static str
        }
        impl CliArg for Opt {
            type Value = Option<String>;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                opts.optopt(self.short, self.long, self.help, self.metavar);
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                matches.opt_get(self.long).map_err(|e| anyhow!("{}", e))
            }
        }

        pub struct ReqOpt(pub Opt);
        impl CliArg for ReqOpt {
            type Value = String;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                // NOTE: Don't use reqopt because it will trigger error messages even if `--help` and `--version` are provided.
                //       (seriously, why aren't those two options built into getopts?!)
                opts.optopt(self.0.short, self.0.long, self.0.help, self.0.metavar);
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                self.0.extract_value(matches).and_then(|opt| opt.ok_or_else(|| anyhow!("missing required option '--{}'", self.0.long)))
            }
        }

        pub struct MultiOpt(pub Opt);
        impl CliArg for MultiOpt {
            type Value = Vec<String>;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                opts.optmulti(self.0.short, self.0.long, self.0.help, self.0.metavar);
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                Ok(matches.opt_strs(self.0.long))
            }
        }

        pub struct Positional {
            pub metavar: &'static str,
        }
        impl CliArg for Positional {
            type Value = String;
            fn add_to_options(&self, _: &mut getopts::Options) {}
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                matches.free.pop().ok_or_else(|| anyhow!("missing required positional arg {}", self.metavar))
            }
        }
    }
}
