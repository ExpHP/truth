// IMPORTANT: DO NOT USE ANYTHING FROM THE LIB CRATE HERE!
//
//            If you do, you'll cause linking to occur and full package builds using --all-targets
//            or --tests will take quite measurably longer!

pub fn run_truth_subcommand(subcommand: &str) {
    let exe_path = std::env::current_exe().unwrap_or_else(|e| {
        eprintln!("ERROR: could not get current exe path: {}", e);
        std::process::exit(1);
    });

    let exe_dir = exe_path.parent().unwrap_or_else(|| {
        eprintln!("ERROR: exe path has no parent?! What sorcery is this?!");
        std::process::exit(1);
    });

    // find a binary named 'truth' in the same dir with the same extension as us
    let mut truth_path = exe_dir.join("truth-core");
    if let Some(ext) = exe_path.extension() {
        truth_path = truth_path.with_extension(ext);
    }
    if !truth_path.exists() {
        eprintln!("ERROR: cannot find 'truth-core' in '{}'. Exiting.", exe_dir.display());
        std::process::exit(1);
    }

    let status = {
        std::process::Command::new(truth_path)
            .arg(subcommand)
            .args(std::env::args_os().skip(1))
            .status()
            .unwrap_or_else(|e| {
                eprintln!("ERROR: unable to start 'truth-core': {}", e);
                std::process::exit(1);
            })
    };

    if !status.success() {
        std::process::exit(1);
    }
}
