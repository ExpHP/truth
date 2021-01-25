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
use crate::error::{CompileError, SimpleError};
use crate::pos::Files;

pub fn main() -> ! {
    let mut args = std::env::args();
    let _ = args.next();
    truth_main(&args.collect::<Vec<_>>());
}


pub fn truth_main(args: &[String]) -> ! {
    cli::parse_subcommand(&args, Subcommands {
        abbreviations: cli::Abbreviations::Forbid,
        program: "truth-core",
        choices: &[
            SubcommandSpec { name: "truanm", entry: truanm_main, public: true },
            SubcommandSpec { name: "trustd", entry: trustd_main, public: true },
            SubcommandSpec { name: "anm-benchmark", entry: anm_benchmark::main, public: false },
            SubcommandSpec { name: "ecl-reformat", entry: ecl_reformat::main, public: false },
        ],
    })
}


pub fn truanm_main(args: &[String]) -> ! {
    cli::parse_subcommand(&args, Subcommands {
        abbreviations: cli::Abbreviations::Allow,
        program: "truanm",
        choices: &[
            SubcommandSpec { name: "decompile", entry: anm_decompile::main, public: true },
            SubcommandSpec { name: "compile", entry: anm_compile::main, public: true },
        ],
    })
}


pub fn trustd_main(args: &[String]) -> ! {
    cli::parse_subcommand(&args, Subcommands {
        abbreviations: cli::Abbreviations::Allow,
        program: "trustdd",
        choices: &[
            SubcommandSpec { name: "decompile", entry: std_decompile::main, public: true },
            SubcommandSpec { name: "compile", entry: std_compile::main, public: true },
        ],
    })
}


pub mod ecl_reformat {
    use super::*;

    pub fn main(argv: &[String]) -> ! {
        let (input,) = cli::parse_args(argv, CmdSpec {
            program: "truth-core ecl-reformat",
            usage_args: "FILE [OPTIONS...]",
            options: (cli::input(),),
        });

        wrap_fancy_errors(|files| run(files, input));
    }

    fn run(files: &mut Files, path: impl AsRef<Path>) -> Result<(), CompileError> {
        let script = files.read_file::<crate::ast::Script>(path.as_ref())?;

        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock()));
        f.fmt(&script)?;
        Ok(())
    }
}

pub mod anm_decompile {
    use super::*;

    pub fn main(args: &[String]) -> ! {
        let (input, max_columns, mapfile, game) = cli::parse_args(args, CmdSpec {
            program: "truanm decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::max_columns(), cli::mapfile(), cli::game()),
        });

        let stdout = io::stdout();
        wrap_fancy_errors(|_files| {
            let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock())).with_max_columns(max_columns);
            run(&mut f, game, &input, mapfile)
        });
    }

    pub(super) fn run(
        out: &mut crate::Formatter<impl io::Write>,
        game: Game,
        path: impl AsRef<Path>,
        map_path: Option<impl AsRef<Path>>,
    ) -> Result<(), CompileError> {
        let ty_ctx = {
            use crate::Eclmap;

            let mut ty_ctx = crate::type_system::TypeSystem::new();

            ty_ctx.extend_from_eclmap(None, &Eclmap::parse(&crate::anm::game_core_mapfile(game))?);

            let map_path = map_path.map(|p| p.as_ref().to_owned());
            if let Some(map_path) = map_path.or_else(|| Eclmap::decomp_map_file_from_env(".anmm")) {
                let eclmap = Eclmap::load(&map_path, Some(game))?;
                ty_ctx.extend_from_eclmap(Some(&map_path), &eclmap);
            }
            ty_ctx
        };

        let script = {
            // tiny buffer due to seeking
            let reader = io::BufReader::with_capacity(64, fs_open(&path)?);
            crate::AnmFile::read_from_stream(reader, game, false)
                .and_then(|anm| anm.decompile_to_ast(game, &ty_ctx, crate::DecompileKind::Fancy))
                .with_context(|| format!("in file: {}", path.as_ref().display()))?
        };

        out.fmt(&script)?;
        Ok(())
    }
}

pub mod anm_compile {
    use super::*;

    pub fn main(args: &[String]) -> ! {
        let (script_path, game, output, mapfile, image_sources) = cli::parse_args(args, CmdSpec {
            program: "truanm compile",
            usage_args: "SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfile(), cli::image_sources(),
            ),
        });

        wrap_fancy_errors(|files| run(files, game, &script_path, &output, &image_sources, mapfile.as_ref().map(AsRef::as_ref)));
    }

    pub(super) fn run(
        files: &mut Files,
        game: Game,
        script_path: &Path,
        outpath: &Path,
        cli_image_source_paths: &[PathBuf],
        map_path: Option<&Path>,
    ) -> Result<(), CompileError> {
        let mut ty_ctx = crate::type_system::TypeSystem::new();

        ty_ctx.extend_from_eclmap(None, &crate::Eclmap::parse(&crate::anm::game_core_mapfile(game))?);

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
            let reader = io::Cursor::new(fs_read(image_source_path)?);
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

    pub fn main(args: &[String]) -> ! {
        let (input, output, game) = cli::parse_args(args, CmdSpec {
            program: "truth-core anm-redump",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::game()),
        });

        wrap_fancy_errors(|_| run(game, &input, output))
    }

    fn run(
        game: Game,
        path: impl AsRef<Path>,
        outpath: impl AsRef<Path>,
    ) -> Result<(), CompileError> {
        let reader = io::BufReader::new(fs_open(&path)?);
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

    pub fn main(args: &[String]) -> ! {
        let (anm_path, script_path, game, output, mapfile) = cli::parse_args(args, CmdSpec {
            program: "truth-core anm-benchmark",
            usage_args: "ANMFILE SCRIPT -g GAME -o OUTPUT [OPTIONS...]",
            options: (
                cli::path_arg("ANMFILE"), cli::path_arg("SCRIPT"),
                cli::game(), cli::required_output(), cli::mapfile(),
            ),
        });

        wrap_fancy_errors(|files| run(files, game, &anm_path, &script_path, &output, mapfile.as_ref().map(AsRef::as_ref)))
    }

    fn run(
        files: &mut Files,
        game: Game,
        anm_path: &Path,
        script_path: &Path,
        outpath: &Path,
        map_path: Option<&Path>,
    ) -> Result<(), CompileError> {
        let image_source_paths = [anm_path.to_owned()];
        loop {
            let script_out = fs::File::create(script_path).with_context(|| format!("creating file '{}'", script_path.display()))?;
            let mut f = crate::Formatter::new(io::BufWriter::new(script_out)).with_max_columns(100);
            super::anm_decompile::run(&mut f, game, anm_path, map_path)?;
            drop(f);

            super::anm_compile::run(files, game, script_path, outpath, &image_source_paths, map_path)?;
        }
    }
}

pub mod std_compile {
    use super::*;

    pub fn main(args: &[String]) -> ! {
        let (input, output, mapfile, game) = cli::parse_args(args, CmdSpec {
            program: "trustd compile",
            usage_args: "FILE -g GAME -o OUTPUT [OPTIONS...]",
            options: (cli::input(), cli::required_output(), cli::mapfile(), cli::game()),
        });

        wrap_fancy_errors(|files| run(files, game, &input, &output, mapfile.as_ref().map(AsRef::as_ref)));
    }

    fn run(
        files: &mut Files,
        game: Game,
        path: &Path,
        outpath: &Path,
        map_path: Option<&Path>,
    ) -> Result<(), CompileError> {
        let mut ty_ctx = crate::type_system::TypeSystem::new();

        ty_ctx.extend_from_eclmap(None, &crate::Eclmap::parse(&crate::std::game_core_mapfile(game))?);

        if let Some(map_path) = map_path {
            let eclmap = crate::Eclmap::load(&map_path, Some(game))?;
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

        let out = fs_create(outpath)?;
        std.write_to_stream(&mut io::BufWriter::new(out), game)?;
        Ok(())
    }
}

pub mod std_decompile {
    use super::*;

    pub fn main(args: &[String]) -> ! {
        let (input, max_columns, mapfile, game) = cli::parse_args(args, CmdSpec {
            program: "trustd decompile",
            usage_args: "FILE -g GAME [OPTIONS...]",
            options: (cli::input(), cli::max_columns(), cli::mapfile(), cli::game()),
        });
        wrap_fancy_errors(|_files| run(game, &input, max_columns, mapfile))
    }

    fn run(
        game: Game,
        path: impl AsRef<Path>,
        ncol: usize,
        map_path: Option<impl AsRef<Path>>,
    ) -> Result<(), CompileError> {
        let ty_ctx = {
            use crate::Eclmap;

            let mut ty_ctx = crate::type_system::TypeSystem::new();

            ty_ctx.extend_from_eclmap(None, &Eclmap::parse(&crate::std::game_core_mapfile(game))?);

            let map_path = map_path.map(|p| p.as_ref().to_owned());
            if let Some(map_path) = map_path.or_else(|| Eclmap::decomp_map_file_from_env(".stdm")) {
                let eclmap = Eclmap::load(&map_path, Some(game))?;
                ty_ctx.extend_from_eclmap(Some(&map_path), &eclmap);
            }
            ty_ctx
        };

        let script = {
            let reader = io::Cursor::new(fs_read(path.as_ref())?);
            crate::StdFile::read_from_stream(reader, game)
                .and_then(|parsed| parsed.decompile_to_ast(game, &ty_ctx, crate::DecompileKind::Fancy))
                .with_context(|| format!("in file: {}", path.as_ref().display()))?
        };

        let stdout = io::stdout();
        let mut f = crate::Formatter::new(io::BufWriter::new(stdout.lock())).with_max_columns(ncol);
        f.fmt(&script)?;
        Ok(())
    }
}

// =============================================================================

fn fs_open(path: impl AsRef<Path>) -> Result<fs::File, SimpleError> {
    fs::File::open(path.as_ref()).with_context(|| format!("while opening file: {}", path.as_ref().display()))
}
fn fs_read(path: impl AsRef<Path>) -> Result<Vec<u8>, SimpleError> {
    fs::read(path.as_ref()).with_context(|| format!("while reading file: {}", path.as_ref().display()))
}
fn fs_create(path: impl AsRef<Path>) -> Result<fs::File, SimpleError> {
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

// FIXME: This stuff is still disgustingly overengineered and I hate it.
mod cli {
    use super::*;
    use anyhow::anyhow;
    use getopts::{Options, Matches};

    pub fn mapfile() -> impl CliArg<Value=Option<PathBuf>> { opts::PathOpt(opts::Opt {
        short: "m", long: "map", metavar: "MAPFILE",
        help: "use a mapfile to translate instruction names and argument types",
    })}
    pub fn required_output() -> impl CliArg<Value=PathBuf> { opts::ReqPathOpt(opts::ReqOpt(opts::Opt {
        short: "o", long: "output", metavar: "OUTPUT",
        help: "output file",
    }))}
    pub fn max_columns() -> impl CliArg<Value=usize> { opts::MaxColumnsOpt }
    pub fn game() -> impl CliArg<Value=Game> { opts::GameOpt }
    pub fn path_arg(s: &'static str) -> impl CliArg<Value=PathBuf> { opts::ReqPathOpt(opts::Positional { metavar: s }) }
    pub fn input() -> impl CliArg<Value=PathBuf> { path_arg("INPUT") }
    pub fn image_sources() -> impl CliArg<Value=Vec<PathBuf>> { opts::ImageSrcOpt }

    pub enum Abbreviations { Allow, Forbid }

    pub struct CmdSpec<A> {
        pub program: &'static str,
        pub usage_args: &'static str,
        pub options: A,
    }

    pub fn parse_args<A: CliArg>(
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
                print_version();
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
        pub entry: fn(&[String]) -> !,

        /// Whether to show in usage.
        pub public: bool,
    }

    pub fn parse_subcommand(
        args: &[String],
        subcommands: Subcommands,
    ) -> ! {
        match _parse_args(&args, &subcommands) {
            // parsing will automatically call the subcommand so this is unreachable...
            Ok(never) => match never {},

            Err(ParseError::PrintHelp(_)) => {
                subcommands.show_usage();
                std::process::exit(0);
            },

            Err(ParseError::PrintVersion) => {
                print_version();
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
    fn print_version() {
        eprintln!("truth {}", git_version::git_version!());
    }

    pub type ArgError = SimpleError;
    pub trait CliArg {
        type Value;
        fn add_to_options(&self, opts: &mut getopts::Options);
        /// NOTE: `matches.free` is in reverse order, so you can call `Vec::pop` to extract them.
        fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError>;
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

    pub enum Never {}

    impl CliArg for Subcommands {
        type Value = Never;

        fn add_to_options(&self, opts: &mut getopts::Options) {
            opts.parsing_style(getopts::ParsingStyle::StopAtFirstFree);
        }

        fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
            let selection = matches.free.pop().ok_or_else(|| anyhow!("please choose a subcommand"))?;
            matches.free.reverse();  // back into forwards order
            let remaining_args = &matches.free;

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

            (choices.into_iter().next().unwrap().entry)(remaining_args)
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
                opts.reqopt(self.0.short, self.0.long, self.0.help, self.0.metavar);
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                self.0.extract_value(matches).map(Option::unwrap)
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

        pub struct PathOpt<Inner>(pub Inner);
        impl<Inner: CliArg<Value=Option<String>>> CliArg for PathOpt<Inner> {
            type Value = Option<PathBuf>;
            fn add_to_options(&self, opts: &mut getopts::Options) { self.0.add_to_options(opts) }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                self.0.extract_value(matches).map(|opt| opt.map(Into::into))
            }
        }

        pub struct ReqPathOpt<Inner>(pub Inner);
        impl<Inner: CliArg<Value=String>> CliArg for ReqPathOpt<Inner> {
            type Value = PathBuf;
            fn add_to_options(&self, opts: &mut getopts::Options) { self.0.add_to_options(opts) }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                self.0.extract_value(matches).map(Into::into)
            }
        }

        pub struct ImageSrcOpt;
        impl CliArg for ImageSrcOpt {
            type Value = Vec<PathBuf>;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                opts.optmulti("i", "image-source", "", "GAME");
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                Ok(matches.opt_strs("image-source").into_iter().map(Into::into).collect())
            }
        }

        pub struct GameOpt;
        impl CliArg for GameOpt {
            type Value = Game;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                opts.reqopt("g", "game", "game number, e.g. 'th095' or '8'. Don't include a point in point titles. Also supports 'alcostg'.", "GAME");
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                matches.opt_get("game").map(Option::unwrap).map_err(|e| anyhow!("{}", e))
            }
        }

        pub struct MaxColumnsOpt;
        impl CliArg for MaxColumnsOpt {
            type Value = usize;
            fn add_to_options(&self, opts: &mut getopts::Options) {
                opts.optopt("", "max-columns", "where possible, will attempt to break lines for < NUM columns", "NUM");
            }
            fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
                matches.opt_get("max-columns").map_err(|e| anyhow!("{}", e))
                    .map(|opt| opt.unwrap_or(100))
            }
        }
    }
}
