mod gen_macros;
use lalrpop;

fn main() {
    lalrpop::Configuration::new()
        .emit_rerun_directives(true)
        .process_current_dir().unwrap();

    let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    std::fs::write(out_dir.join("generated_macros.rs"), gen_macros::gen_ast_macros()).unwrap();
}
