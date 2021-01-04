use std::path::PathBuf;
use anyhow::anyhow;
use crate::game::Game;
use crate::error::{CompileError, SimpleError};

pub fn cli<A: CliArg>(
    usage_args: &str,
    arg_parsers: A,
) -> A::Value {
    let args: Vec<String> = std::env::args().collect();
    let program = args[0].clone();
    match parse_args(&args[1..], arg_parsers) {
        Ok(arg_values) => arg_values,
        Err(ParseError::PrintHelp(opts)) => {
            print_help(&program, usage_args, &opts);
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

fn print_usage(program: &str, usage_args: &str) {
    eprintln!("Usage: {} {}", program, usage_args);
}
fn print_help(program: &str, usage_args: &str, opts: &getopts::Options) {
    eprint!("{}", opts.usage(&format!("Usage: {} {}", program, usage_args)));
}

pub type ArgError = SimpleError;

enum ParseError { Error(ArgError), PrintHelp(getopts::Options) }
// factors out the parts where we want usage with errors
fn parse_args<A: CliArg>(args: &[String], arg_parsers: A) -> Result<A::Value, ParseError> {
    let mut opts = getopts::Options::new();
    opts.optflag("h", "help", "print this help menu");
    arg_parsers.add_to_options(&mut opts);

    let mut matches = opts.parse(args).map_err(|e| ParseError::Error(anyhow!("{}", e)))?;
    if matches.opt_present("h") {
        return Err(ParseError::PrintHelp(opts));
    }

    matches.free.reverse();

    let out = arg_parsers.extract_value(&mut matches).map_err(ParseError::Error)?;

    if let Some(unexpected_pos) = matches.free.pop() {
        return Err(ParseError::Error(anyhow!("unexpected positional: {:?}", unexpected_pos)));
    }

    Ok(out)
}

// ------------------------------------------------

pub trait CliArg {
    type Value;
    fn add_to_options(&self, opts: &mut getopts::Options);
    /// NOTE: `matches.free` is in reverse order, so you can call `Vec::pop` to extract them.
    fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError>;
}

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


/// A simple HList type for CliArg.
#[doc(hidden)]
pub struct Args<H, T>(pub H, pub T);
#[macro_export]
macro_rules! args {
    () => { () };
    ($a:expr $(, $more:expr)* $(,)?) => { $crate::cli_helper::Args($a, $crate::args!( $($more),* )) }
}
#[macro_export]
macro_rules! args_pat {
    () => { () };
    ($a:pat $(, $more:pat)* $(,)?) => { $crate::cli_helper::Args($a, $crate::args_pat!( $($more),* )) }
}


impl CliArg for () {
    type Value = ();
    fn add_to_options(&self, _: &mut getopts::Options) {}
    fn extract_value(&self, _: &mut getopts::Matches) -> Result<Self::Value, ArgError> { Ok(()) }
}

impl<H: CliArg, T: CliArg> CliArg for Args<H, T> {
    type Value = Args<H::Value, T::Value>;
    fn add_to_options(&self, options: &mut getopts::Options) {
        self.0.add_to_options(options);
        self.1.add_to_options(options);
    }
    fn extract_value(&self, matches: &mut getopts::Matches) -> Result<Self::Value, ArgError> {
        let head = self.0.extract_value(matches)?;
        let tail = self.1.extract_value(matches)?;
        Ok(Args(head, tail))
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
