use ecl_parser;
use ecl_parser::Parse;

fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![input, ] = cli::cli(
        "FILE [OPTIONS...]", args![cli::input()],
    );

    run(input);
}


fn run(path: impl AsRef<std::path::Path>) {
    let text = std::fs::read(path).unwrap();

    let script = match ecl_parser::Script::parse(&text) {
        Ok(x) => x,
        Err(e) => panic!("{}", e),
    };
    let stdout = std::io::stdout();
    let mut f = ecl_parser::fmt::Formatter::new(stdout.lock());
    f.fmt(&script).unwrap();
}
