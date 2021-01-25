fn main() -> ! {
    // note: this call to git_version!() is placed as high up the dependency tree as we possibly
    //       can, because it triggers rebuilds on pretty much anything you touch. (even files
    //       outside of `src/`...)
    let version = git_version::git_version!();

    truth::cli_def::main(version);
}
