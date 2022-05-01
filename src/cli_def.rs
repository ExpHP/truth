use std::path::{Path, PathBuf};
use std::io;
use crate::ast::ScriptFile;
use crate::api::Truth;
use crate::game::{Game, LanguageKey};
use crate::error::ErrorReported;
use crate::llir::DecompileOptions;

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
            SubcommandSpec { name: "truecl", entry: truecl_main, public: false },
            // undocumented commands used for testing purposes;
            // these are not easily discoverable, and may be removed any time
            SubcommandSpec { name: "anm-benchmark", entry: anm_benchmark::main, public: false },
            SubcommandSpec { name: "ecl-benchmark", entry: ecl_benchmark::main, public: false },
            SubcommandSpec { name: "text-reformat", entry: text_reformat::main, public: false },
            SubcommandSpec { name: "msg-redump", entry: msg_redump::main, public: false },
            SubcommandSpec { name: "ecl-redump", entry: ecl_redump::main, public: false },
        ],
    })
}


pub fn truecl_main(version: &str, args: &[String]) -> ! {
    cli::parse_subcommand(version, &args, Subcommands {
        abbreviations: cli::Abbreviations::Allow,
        program: "truecl",
        choices: &[
            SubcommandSpec { name: "decompile", entry: ecl_decompile::main, public: true },
            SubcommandSpec { name: "compile", entry: ecl_compile::main, public: true },
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
            SubcommandSpec { name: "extract", entry: anm_extract::main, public: true },
            SubcommandSpec { name: "xtract", entry: anm_extract::main, public: false }, // let 'x' work
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


pub mod text_reformat {
    use super::*;

    pub fn main(version: &str, argv: &[String]) -> ! {
        let (input,) = cli::parse_args(version, argv, CmdSpec {
            program: "truth-core text-reformat",
            usage_args: "FILE [OPTIONS...]",
            options: (cli::input(),),
        });

        wrap_exit_code(|truth| run(truth, input));
    }

    fn run(truth: &mut Truth, path: impl AsRef<Path>) -> Result<(), ErrorReported> {
        let ast = truth.read_script(path.as_ref())?;

        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock()));
        f.fmt(&ast).map_err(|e| truth.emit(error!("{:#}", e)))?;
        Ok(())
    }
}

pub mod anm_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, fmt_config, mapfiles, game, decompile_options) = cli::parse_args(version, args, CmdSpec {
            program: "truanm decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::fmt_config(), cli::mapfiles(), cli::game(), cli::decompile_options()),
        });

        wrap_decompile_to_stdout(fmt_config, |truth| {
            decompile(truth, game, input.as_ref(), mapfiles, &decompile_options)
        });
    }

    pub(super) fn decompile(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        mapfile_args: Vec<PathBuf>,
        decompile_options: &DecompileOptions,
    ) -> Result<ScriptFile, ErrorReported> {
        let mapfile_args = add_env_mapfile_for_decomp(mapfile_args, ".anmm");
        load_mapfiles(truth, game, &[LanguageKey::Anm], mapfile_args)?;

        let mut truth = truth.validate_defs()?;
        let anm = truth.read_anm(game, path, false)?;
        truth.decompile_anm(game, &anm, decompile_options)
    }
}

pub mod anm_extract {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, outdir, game) = cli::parse_args(version, args, CmdSpec {
            program: "truanm extract",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::extract_outdir(), cli::game()),
        });

        wrap_exit_code(|truth| {
            run(truth, game, input.as_ref(), &outdir)
        });
    }

    pub(super) fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outdir: &Path,
    ) -> Result<(), ErrorReported> {
        let mut truth = truth.validate_defs()?;
        let anm = truth.read_anm(game, path, true)?;
        anm.extract_images(outdir, &truth.fs())
    }
}

pub mod anm_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (script_path, game, output, mapfiles, image_sources, output_thecl_defs) = cli::parse_args(version, args, CmdSpec {
            program: "truanm compile",
            usage_args: "SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfiles(), cli::image_sources(),
                cli::output_thecl_defs(),
            ),
        });

        wrap_exit_code(|truth| run(truth, game, &script_path, &output, &image_sources, mapfiles, output_thecl_defs));
    }

    pub(super) fn run(
        truth: &mut Truth,
        game: Game,
        script_path: &Path,
        outpath: &Path,
        cli_image_source_paths: &[PathBuf],
        mapfile_args: Vec<PathBuf>,
        output_thecl_defs: Option<PathBuf>,
    ) -> Result<(), ErrorReported> {
        load_mapfiles(truth, game, &[LanguageKey::Anm], mapfile_args)?;

        let ast = truth.read_script(&script_path)?;
        truth.load_mapfiles_from_pragmas(game, &ast)?;
        let mut truth = truth.validate_defs()?;
        let mut compiled = truth.compile_anm(game, &ast)?;

        // image sources referenced in file take precedence
        let mut image_source_paths = vec![];
        image_source_paths.extend(ast.image_sources.iter().map(|lit| PathBuf::from(&lit.string)));
        image_source_paths.extend(cli_image_source_paths.iter().cloned());

        for image_source_path in &image_source_paths {
            let source_anm = truth.read_image_source(game, image_source_path)?;
            compiled.apply_image_source(source_anm, &truth.fs())?;
        }

        let compiled = truth.finalize_anm(game, compiled)?;
        truth.write_anm(game, &outpath, &compiled)?;

        if let Some(outpath) = output_thecl_defs {
            truth.fs().write(&outpath, compiled.generate_thecl_defs()?)?
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

        wrap_exit_code(|truth| run(truth, game, input.as_ref(), output.as_ref()))
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outpath: &Path,
    ) -> Result<(), ErrorReported> {
        let mut truth = truth.validate_defs()?;
        let anm = truth.read_anm(game, path, true)?;
        truth.write_anm(game, outpath, &anm)
    }
}

pub mod ecl_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, mapfiles, game) = cli::parse_args(version, args, CmdSpec {
            program: "truecl compile",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::mapfiles(), cli::game()),
        });

        wrap_exit_code(|truth| run(truth, game, &input, &output, mapfiles));
    }

    pub fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outpath: &Path,
        mapfile_args: Vec<PathBuf>,
    ) -> Result<(), ErrorReported> {
        load_mapfiles(truth, game, &[LanguageKey::Ecl, LanguageKey::Timeline], mapfile_args)?;

        let ast = truth.read_script(&path)?;
        truth.load_mapfiles_from_pragmas(game, &ast)?;
        truth.expect_no_image_sources(&ast)?;

        let mut truth = truth.validate_defs()?;
        let ecl = truth.compile_ecl(game, &ast)?;
        truth.write_ecl(game, outpath, &ecl)?;
        Ok(())
    }
}

pub mod ecl_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, fmt_config, mapfiles, game, decompile_options) = cli::parse_args(version, args, CmdSpec {
            program: "truecl decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::fmt_config(), cli::mapfiles(), cli::game(), cli::decompile_options()),
        });

        wrap_decompile_to_stdout(fmt_config, |truth| {
            decompile(truth, game, input.as_ref(), mapfiles, &decompile_options)
        });
    }

    pub(super) fn decompile(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        mapfile_args: Vec<PathBuf>,
        decompile_options: &DecompileOptions,
    ) -> Result<ScriptFile, ErrorReported> {
        let mapfile_args = add_env_mapfile_for_decomp(mapfile_args, ".eclm");
        load_mapfiles(truth, game, &[LanguageKey::Ecl, LanguageKey::Timeline], mapfile_args)?;

        let mut truth = truth.validate_defs()?;
        let anm = truth.read_ecl(game, path)?;
        truth.decompile_ecl(game, &anm, decompile_options)
    }
}

pub mod ecl_redump {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, game) = cli::parse_args(version, args, CmdSpec {
            program: "truth-core ecl-redump",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::game()),
        });

        wrap_exit_code(|truth| run(truth, game, input.as_ref(), output.as_ref()))
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outpath: &Path,
    ) -> Result<(), ErrorReported> {
        let mut truth = truth.validate_defs()?;
        let ecl = truth.read_ecl(game, path)?;
        truth.write_ecl(game, outpath, &ecl)
    }
}

pub mod anm_benchmark {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (anm_path, script_path, game, output, mapfiles, decompile_options) = cli::parse_args(version, args, CmdSpec {
            program: "truth-core anm-benchmark",
            usage_args: "ANMFILE SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("ANMFILE"), cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfiles(), cli::decompile_options(),
            ),
        });

        wrap_exit_code(|truth| run(truth, game, &anm_path, &script_path, &output, mapfiles, &decompile_options))
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        anm_path: &Path,
        script_path: &Path,
        outpath: &Path,
        mapfile_args: Vec<PathBuf>,
        decompile_options: &DecompileOptions,
    ) -> Result<(), ErrorReported> {
        let image_source_paths = [anm_path.to_owned()];
        loop {
            let ast = super::anm_decompile::decompile(truth, game, anm_path, mapfile_args.clone(), &decompile_options)?;

            let fmt_config = crate::fmt::Config::new().max_columns(100);
            let mut script_out_utf8 = vec![];
            let mut f = crate::Formatter::with_config(&mut script_out_utf8, fmt_config);
            f.fmt(&ast).map_err(|e| truth.emit(error!("{:#}", e)))?;
            drop(f); // flush

            truth.fs().write(script_path, &script_out_utf8)?;

            super::anm_compile::run(truth, game, script_path, outpath, &image_source_paths, mapfile_args.clone(), None)?;
        }
    }
}

pub mod ecl_benchmark {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (ecl_path, script_path, game, output, mapfiles, decompile_options) = cli::parse_args(version, args, CmdSpec {
            program: "truth-core anm-benchmark",
            usage_args: "ECLFILE SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("ECLFILE"), cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfiles(), cli::decompile_options(),
            ),
        });

        wrap_exit_code(|truth| run(truth, game, &ecl_path, &script_path, &output, mapfiles, &decompile_options))
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        ecl_path: &Path,
        script_path: &Path,
        outpath: &Path,
        mapfile_args: Vec<PathBuf>,
        decompile_options: &DecompileOptions,
    ) -> Result<(), ErrorReported> {
        loop {
            let ast = super::ecl_decompile::decompile(truth, game, ecl_path, mapfile_args.clone(), &decompile_options)?;

            let fmt_config = crate::fmt::Config::new().max_columns(100);
            let mut script_out_utf8 = vec![];
            let mut f = crate::Formatter::with_config(&mut script_out_utf8, fmt_config);
            f.fmt(&ast).map_err(|e| truth.emit(error!("{:#}", e)))?;
            drop(f); // flush

            truth.fs().write(script_path, &script_out_utf8)?;

            super::ecl_compile::run(truth, game, script_path, outpath, mapfile_args.clone())?;
        }
    }
}

pub mod std_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, mapfiles, game) = cli::parse_args(version, args, CmdSpec {
            program: "trustd compile",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::mapfiles(), cli::game()),
        });

        wrap_exit_code(|truth| run(truth, game, &input, &output, mapfiles));
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outpath: &Path,
        mapfile_args: Vec<PathBuf>,
    ) -> Result<(), ErrorReported> {
        load_mapfiles(truth, game, &[LanguageKey::Std], mapfile_args)?;

        let ast = truth.read_script(&path)?;
        truth.load_mapfiles_from_pragmas(game, &ast)?;
        truth.expect_no_image_sources(&ast)?;

        let mut truth = truth.validate_defs()?;
        let std = truth.compile_std(game, &ast)?;
        truth.write_std(game, outpath, &std)?;
        Ok(())
    }
}

pub mod std_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, fmt_config, mapfiles, game, decompile_options) = cli::parse_args(version, args, CmdSpec {
            program: "trustd decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::fmt_config(), cli::mapfiles(), cli::game(), cli::decompile_options()),
        });
        wrap_decompile_to_stdout(fmt_config, |truth| decompile(truth, game, &input, mapfiles, &decompile_options))
    }

    fn decompile(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        mapfile_args: Vec<PathBuf>,
        decompile_options: &DecompileOptions,
    ) -> Result<ScriptFile, ErrorReported> {
        let mapfile_args = add_env_mapfile_for_decomp(mapfile_args, ".stdm");
        load_mapfiles(truth, game, &[LanguageKey::Std], mapfile_args)?;

        let mut truth = truth.validate_defs()?;
        let std = truth.read_std(game, path)?;
        truth.decompile_std(game, &std, decompile_options)
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

        wrap_exit_code(|truth| run(truth, game, input.as_ref(), output.as_ref()))
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outpath: &Path,
    ) -> Result<(), ErrorReported> {
        let mut truth = truth.validate_defs()?;
        let msg = truth.read_msg(game, LanguageKey::Msg, path)?;
        truth.write_msg(game, LanguageKey::Msg, outpath, &msg)?;
        Ok(())
    }
}

pub mod msg_compile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, output, mapfiles, game, msg_mode) = cli::parse_args(version, args, CmdSpec {
            program: "trumsg compile",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::mapfiles(), cli::game(), cli::msg_mode()),
        });

        wrap_exit_code(|truth| run(truth, game, &input, &output, mapfiles, msg_mode));
    }

    fn run(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        outpath: &Path,
        mapfile_args: Vec<PathBuf>,
        msg_mode: MsgMode,
    ) -> Result<(), ErrorReported> {
        let ast = truth.read_script(&path)?;
        truth.expect_no_image_sources(&ast)?;

        match msg_mode {
            MsgMode::Stage => {
                load_mapfiles(truth, game, &[LanguageKey::Msg], mapfile_args)?;
                truth.load_mapfiles_from_pragmas(game, &ast)?;

                let mut truth = truth.validate_defs()?;
                let msg = truth.compile_msg(game, LanguageKey::Msg, &ast)?;
                truth.write_msg(game, LanguageKey::Msg, outpath, &msg)?;
            },
            MsgMode::Mission => {
                let mut truth = truth.validate_defs()?;
                let msg = truth.compile_mission(game, &ast)?;
                truth.write_mission(game, outpath, &msg)?;
            },
            MsgMode::Ending => return Err(truth.emit(error!("--ending is not yet implemented"))),
        }
        Ok(())
    }
}

pub mod msg_decompile {
    use super::*;

    pub fn main(version: &str, args: &[String]) -> ! {
        let (input, fmt_config, mapfiles, game, msg_mode, decompile_options) = cli::parse_args(version, args, CmdSpec {
            program: "trumsg decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::fmt_config(), cli::mapfiles(), cli::game(), cli::msg_mode(), cli::decompile_options()),
        });
        wrap_decompile_to_stdout(fmt_config, |truth| decompile(truth, game, &input, mapfiles, msg_mode, &decompile_options))
    }

    fn decompile(
        truth: &mut Truth,
        game: Game,
        path: &Path,
        mapfile_args: Vec<PathBuf>,
        msg_mode: MsgMode,
        decompile_options: &DecompileOptions,
    ) -> Result<ScriptFile, ErrorReported> {
        match msg_mode {
            MsgMode::Stage => {
                let mapfile_args = add_env_mapfile_for_decomp(mapfile_args, ".msgm");
                load_mapfiles(truth, game, &[LanguageKey::Msg], mapfile_args)?;

                let mut truth = truth.validate_defs()?;
                let msg = truth.read_msg(game, LanguageKey::Msg, path)?;
                truth.decompile_msg(game, LanguageKey::Msg, &msg, decompile_options)
            },
            MsgMode::Mission => {
                let mut truth = truth.validate_defs()?;
                let msg = truth.read_mission(game, path)?;
                truth.decompile_mission(game, &msg)
            },
            MsgMode::Ending => return Err(truth.emit(error!("--ending is not yet implemented"))),
        }
    }
}

// =============================================================================

/// Implements the automatic searching of the environment during decompilation.
fn add_env_mapfile_for_decomp(
    mut mapfile_args: Vec<PathBuf>,
    mapfile_extension: &'static str,
) -> Vec<PathBuf> {
    if let Some(env_mapfile) = crate::Mapfile::decomp_map_file_from_env(mapfile_extension) {
        mapfile_args.insert(0, env_mapfile);
    }
    mapfile_args
}

/// Loads the user's mapfile and the core mapfile.
fn load_mapfiles(
    truth: &mut Truth,
    game: Game,
    // this takes multiple languages (rather than expecting multiple calls) so that all core
    // mapfiles can be loaded before any CLI args
    core_mapfile_languages: &[LanguageKey],
    mapfile_args: Vec<PathBuf>,
) -> Result<(), ErrorReported> {
    for &language in core_mapfile_languages {
        let core_mapfile = crate::core_mapfiles::core_mapfile(game, language);
        truth.apply_mapfile(&core_mapfile, game).expect("failed to apply core mapfile!?");
    }

    for path in mapfile_args {
        truth.load_mapfile(&path, game)?;
    }
    Ok(())
}

// =============================================================================

/// Basic wrapper for entry points that constructs an instance of the compiler API and converts Result into exit codes.
fn wrap_exit_code(func: impl FnOnce(&mut Truth) -> Result<(), ErrorReported>) -> ! {
    let mut scope = crate::Builder::new().build();
    let mut truth = scope.truth();

    match func(&mut truth) {
        Ok(()) => std::process::exit(0),
        Err(ErrorReported) => std::process::exit(1),
    }
}

/// Wraps a function that decompiles into one that writes to STDOUT and uses exit codes.
fn wrap_decompile_to_stdout(
    fmt_config: crate::fmt::Config,
    func: impl FnOnce(&mut Truth) -> Result<ScriptFile, ErrorReported>,
) -> ! {
    let stdout = io::stdout();
    let stdout = io::BufWriter::new(stdout.lock());
    wrap_exit_code(|truth| {
        let ast = func(truth)?;

        crate::Formatter::with_config(stdout, fmt_config)
            .fmt(&ast).map_err(|e| truth.emit(error!("{:#}", e)))
    })
}

// =============================================================================

use cli::{CmdSpec, Subcommands, SubcommandSpec, MsgMode};

mod cli {
    use super::*;
    use getopts::{Options, Matches};

    pub fn mapfiles() -> impl CliArg<Value=Vec<PathBuf>> {
        opts::MultiOpt(opts::Opt {
            short: "m", long: "map", metavar: "MAPFILE",
            help: "use a mapfile to translate instruction names and argument types",
        }).map(|opts| opts.into_iter().map(Into::into).collect())
    }

    pub fn required_output() -> impl CliArg<Value=PathBuf> {
        opts::ReqOpt(opts::Opt {
            short: "o", long: "output", metavar: "OUTPUT",
            help: "output file",
        }).map(Into::into)
    }

    pub fn extract_outdir() -> impl CliArg<Value=PathBuf> {
        opts::Opt {
            short: "o", long: "output", metavar: "DIR",
            help: "a directory to write images, which will be created if it does not exist. \
            Defaults to the current directory.",
        }.map(|opt| opt.map(Into::into).unwrap_or_else(|| std::env::current_dir().unwrap()))
    }

    pub fn game() -> impl CliArg<Value=Game> {
        opts::ReqOpt(opts::Opt {
            short: "g", long: "game", metavar: "GAME",
            help: "game number, e.g. 'th095' or '8'. Don't include a point in point titles. Also supports 'alcostg'.",
        }).and_then(|s| s.parse())
    }

    pub fn fmt_config() -> impl CliArg<Value=crate::fmt::Config> {
        fmt_max_columns().map(|ncol| crate::fmt::Config::new().max_columns(ncol))
    }

    fn fmt_max_columns() -> impl CliArg<Value=usize> {
        opts::Opt {
            short: "", long: "max-columns", metavar: "NUM",
            help: "where possible, will attempt to break lines for < NUM columns",
        }.and_then(|s| s.unwrap_or_else(|| "80".to_string()).parse().map_err(|e| error!("{}", e)))
    }

    pub fn path_arg(s: &'static str) -> impl CliArg<Value=PathBuf> {
        opts::Positional { metavar: s }.map(Into::into)
    }

    pub fn input() -> impl CliArg<Value=PathBuf> { path_arg("INPUT") }

    pub fn image_sources() -> impl CliArg<Value=Vec<PathBuf>> {
        opts::MultiOpt(opts::Opt {
            short: "i", long: "image-source", metavar: "SOURCE",
            help: "supply images from the provided ANM file or directory.  This can be supplied multiple times.  Later sources override earlier ones.",
        }).map(|strs| strs.into_iter().map(Into::into).collect())
    }

    pub fn output_thecl_defs() -> impl CliArg<Value=Option<PathBuf>> {
        opts::Opt {
            short: "", long: "output-thecl-defs", metavar: "FILE",
            help: "write a file defining globals for anm scripts for use in thecl",
        }.map(|opt| opt.map(Into::into))
    }

    pub fn decompile_options() -> impl CliArg<Value=DecompileOptions> {
        let no_blocks = opts::Flag {
            short: "", long: "no-blocks",
            help: "prevent decompilation of loops and other control flow",
        };
        let no_intrinsics = opts::Flag {
            short: "", long: "no-intrinsics",
            help: "prevent recognition of special opcodes, so that every instruction decompiles uniformly into a simple function call",
        };
        let no_arguments = opts::Flag {
            short: "", long: "no-arguments",
            help: "prevent decompilation of arguments, leaving all instructions in their most raw format possible. A last resort for troublesome files",
        };
        let no_diff_switches = opts::Flag {
            short: "", long: "no-diff-switches",
            help: "prevent decompilation of diff switches, forcing direct usage of difficulty flags",
        };
        let zipped = no_intrinsics.zip(no_blocks).zip(no_arguments).zip(no_diff_switches);
        zipped.map(|(((no_intrinsics, no_blocks), no_arguments), no_diff_switches)| DecompileOptions {
            intrinsics: !no_intrinsics, blocks: !no_blocks, arguments: !no_arguments,
            diff_switches: !no_diff_switches
        })
    }

    pub enum MsgMode { Stage, Mission, Ending }
    pub fn msg_mode() -> impl CliArg<Value=MsgMode> {
        let mission_opt = opts::Flag { short: "", long: "mission", help: "parse mission.msg or titlemsg.txt" };
        let ending_opt = opts::Flag { short: "", long: "ending", help: "parse an ending MSG" };
        mission_opt.zip(ending_opt).and_then(|(mission, ending)| match (mission, ending) {
            (true, true) => Err(error!("--mission and --ending are incompatible")),
            (true, false) => Ok(MsgMode::Mission),
            (false, true) => Ok(MsgMode::Ending),
            (false, false) => Ok(MsgMode::Stage),
        })
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

                // the error can't possibly have any spans if it occurred during argument parsing,
                // so any instance of RootEmitter should be able to format it.
                crate::diagnostic::RootEmitter::new_stderr().emit(e).ignore();
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

                // the error can't possibly have any spans if it occurred during argument parsing,
                // so any instance of RootEmitter should be able to format it.
                crate::diagnostic::RootEmitter::new_stderr().emit(e).ignore();
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

    pub type ArgError = crate::diagnostic::Diagnostic;
    pub trait CliArg {
        type Value;
        fn add_to_options(&self, opts: &mut getopts::Options);
        /// NOTE: `matches.free` is in reverse order, so you can call `Vec::pop` to extract them.
        fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError>;

        fn zip<BArg: CliArg>(self, other: BArg) -> Zip<Self, BArg>
        where
            Self: Sized,
        { Zip(self, other) }

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

    pub struct Zip<A, B>(A, B);
    impl<A: CliArg, B: CliArg> CliArg for Zip<A, B> {
        type Value = (A::Value, B::Value);

        fn add_to_options(&self, opts: &mut Options) {
            self.0.add_to_options(opts);
            self.1.add_to_options(opts);
        }
        fn extract_value(&self, matches: &mut Matches) -> Result<Self::Value, ArgError> {
            let a = self.0.extract_value(matches)?;
            let b = self.1.extract_value(matches)?;
            Ok((a, b))
        }
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

        let mut matches = opts.parse(args).map_err(|e| ParseError::Error(error!("{}", e)))?;
        if matches.opt_present("h") {
            return Err(ParseError::PrintHelp(opts));
        }
        if matches.opt_present("version") {
            return Err(ParseError::PrintVersion);
        }

        matches.free.reverse();

        let out = arg_parsers.extract_value(&mut matches).map_err(ParseError::Error)?;

        if let Some(unexpected_pos) = matches.free.pop() {
            return Err(ParseError::Error(error!("unexpected positional: {:?}", unexpected_pos)));
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
            let selection = matches.free.pop().ok_or_else(|| error!("please choose a subcommand"))?;
            matches.free.reverse();  // back into forwards order
            let remaining_args = matches.free.drain(..).collect();

            let is_applicable: Box<dyn Fn(&str) -> bool> = match self.abbreviations {
                Abbreviations::Allow => Box::new(|name| name.starts_with(&selection)),
                Abbreviations::Forbid => Box::new(|name| name == &selection),
            };

            let choices = self.choices.iter().filter(|choice| is_applicable(choice.name)).collect::<Vec<_>>();
            match choices.len() {
                0 => return Err(error!("invalid subcommand '{}'", selection)),
                1 => {},
                _ => return Err(error!("ambiguous subcommand '{}'", selection)),
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

        pub struct Flag {
            pub short: &'static str,
            pub long: &'static str,
            pub help: &'static str
        }
        impl CliArg for Flag {
            type Value = bool;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                opts.optflag(self.short, self.long, self.help);
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                Ok(matches.opt_present(self.long))
            }
        }

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
                matches.opt_get(self.long).map_err(|e| error!("{}", e))
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
                self.0.extract_value(matches).and_then(|opt| opt.ok_or_else(|| error!("missing required option '--{}'", self.0.long)))
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
                matches.free.pop().ok_or_else(|| error!("missing required positional arg {}", self.metavar))
            }
        }
    }
}
