use ecl_parser;

fn main() {
    use ecl_parser::{cli_helper as cli, args, args_pat};

    let args_pat![input, ] = cli::cli(
        "FILE [OPTIONS...]", args![cli::input()],
    );

    run(input);
}


fn run(path: impl AsRef<std::path::Path>) {
    let mut files = ecl_parser::Files::new();
    let script = match files.read_file::<ecl_parser::ast::Script>(path.as_ref()) {
        Ok(x) => x,
        Err(mut e) => {
            let _ = e.emit(&files);
            std::process::exit(1);
        },
    };
    let stdout = std::io::stdout();
    let mut f = ecl_parser::Formatter::new(std::io::BufWriter::new(stdout.lock()));
    f.fmt(&script).unwrap();
}
