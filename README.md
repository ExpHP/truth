# truth

Multipass [THTK](https://github.com/thpatch/thtk/) alternative.

![Sexy error message example](./doc/img/sexy-error.png)

truth stands for "**t**htk **ru**st **th**ing".  Or maybe it stands for "**t**htk **ru**st **th**tk". I dunno, I mostly just picked it because `trustd` and `truecl` sound pretty dope.

## Development status

* `trustd`: in beta; **feature complete, please give it a try!**
* `truanm`: in alpha

Supports **all danmaku titles TH06–TH17.**  That is:

> TH06 (EoSD), TH07 (PCB), TH08 (IN), TH09 (PoFV), TH09.5 (StB), TH10 (MoF), TH11 (SA), TH12 (UFO), TH12.3 (GFW), TH12.5 (DS), TH13 (TD), TH14 (DDC), TH14.3 (ISC), TH15 (LoLK), TH16 (HSiFS), TH16.5 (VD), TH17 (WBaWC)
> 
> Uwabami Breakers is also supported (use `-g alcostg` or `-g 103`)

## Downloading

Get the latest Windows releases [right here on GitHub](https://github.com/ExpHP/truth/tags)!

Development builds may also be posted occationally on the `#tools-dev` channel on the [ZUNcode discord server](https://discord.gg/fvPJvHJ).

For even more bleeding edge, see [Building from source](#building-and-installing-from-source) below.

## Using

### STD files — `trustd`, and some general notes for all tools

Usage of `trustd` is pretty straightforward, so we'll take this opportunity to describe some features common to all of the tools.

Here's how you primarily use it:

```shell
trustd decompile -g13 -m map/any.stdm in.std > out.stdspec

trustd compile -g13 in.stdspec -o out.std
```

The subcommands can be abbreviated to any unambiguous prefix, e.g. `trustd decomp` or even `trustd d`.

Similar to thtk, the `-m` flag imports an ECLMAP-style file. Generally speaking this is only needed during decompilation, because when you are compiling a script, it can contain a reference to its own mapfile:

```C
#pragma mapfile "./map/any.anmm"
```

If you frequently decompile files for experimental purposes, you can also set the environment variable `TRUTH_MAP_PATH` to automatically locate mapfiles during decompilation.  Each directory listed in this `PATH`-like variable will be checked for a file named `any.stdm` if you are compiling STD, `any.anmm` if you are compiling ANM, and etc.

### ANM files — `truanm`

You can decompile an ANM file into a script, similar to `thanm -l`.

```sh
truanm decompile -g12 -m map/any.anmm in.anm > out.spec
```

#### Recompilation of a decompiled ANM file

To recompile an ANM file, you will likely need to supply the original ANM file as a source to copy image data from.  This can be done using the `-i`/`--image-source` flag:

```sh
truanm compile -g12 edited.spec -i original.anm -o out.anm
```

Alternatively, you can also put the following line in your script file, which is equivalent to `-i path/to/original.anm`:

```C
#pragma image_source "path/to/original.anm"
```

Note that there is no feature to extract images into PNG files, and it is doubtful that there ever will need to be, since `thanm -x` remains perfectly fine for this purpose.  There is also no way to embed new images from `.png` files, as thcrap's image hotloading is far superior anyways.

#### Compilation of brand new ANM files

 To compile a brand new ANM file that isn't based on any original ANM file, simply make sure to supply all necessary header data in the `entry` objects along with `has_data: false`; in this case, you do NOT require the `-i` flag.

An example of such a script be found at [th12-no-source-required.anm.spec](./tests/anm_compile/th12-no-source-required.anm.spec).

To use the compiled file, make a thcrap patch which contains images in all of the right locations.  (for instance, if the script has a `has_data: false` entry with `path: "subdir/file.png"`, the thcrap patch should have an image at e.g. `<patch_root>/th17/subdir/file.png`)

## Why use truth over thtk


Some concrete benefits afforded by truth today are:

* **Nice error messages.**  The compiler is on your side! Using the amazing [`codespan-reporting` crate](https://github.com/brendanzab/codespan), error messages display labeled snippets of the problematic code, providing useful context.

* **No segfaults.**  Even if you encounter a bug in the program, it will always produce some sort of error message and optional stacktrace.

* **[gamemaps](./map/any.stdm)** so you don't need to memorize the right mapfiles for each game.

* **Tested.** Ever downloaded a new dev build of thecl to find that inline functions were accidentally broken again for the third time?  truth has a large suite of unit tests and integration tests to help prevent such mistakes before they ever happen.

And specific to some of the binaries:

#### Why use trustd over thstd?

* trustd has thstd's most important missing features:
  * Labels and `goto`!
  * `stdmap`s for naming instructions!
* Nicer formatting of metadata. (more like ANM)
* Decompilation of loops.
* Constant expression evaluation.  `(1 < 3) ? 4.0f : 2.0 + 0.5`
* Correct treatment of "strip" quads in TH08, TH09.

#### Why use truanm over thanm?

**truanm** already has a number of features that are currently only available in thtk's experimental [`thanm-new-spec-format` branch](https://github.com/thpatch/thtk/tree/thanm-new-spec-format):

* C-like syntax like thecl.  (in fact, `truanm` and `trustd` use *the same parser*)
* Automatic allocation of temporary registers for complex expressions

there are some new things as well:

* Decompilation of loops and `if ... else ...`.

#### On the roadmap for truanm

truanm still needs these features before it can be considered "feature complete":

* [ ] **compiling expressions that involve jumps.**  (e.g. `a == b` and `a || b` in arbitrary expressions; currently these are only supported inside `if (...)`)
* [ ] **named sprite/script arguments,** e.g. `sprite(sprite30);` instead of `sprite(30);`.
* [ ] **word-sized (2-byte) arguments,** for the `anchor` instruction.  (this will also help later with some MSG and ECL formats...)

## Building and installing from source

[Install rust](https://rustup.rs/), and then:

```sh
git clone https://github.com/ExpHP/truth
cd truth

# Debug builds  (for optimized builds, change it to `cargo run --release`)
cargo run -- trustd d -g10 -m map/any.stdm in.std > out.stdspec
cargo run -- trustd c -g10 out.stdspec -o out.std

# If you want optimized binaries installed globally:
cargo install --path=.
```

**Important:** Notice that development builds use `cargo run -- trustd` instead of `cargo run --bin=trustd`.  This is because most binaries in this project are actually shims around the main binary (`truth-core`), and if you do `--bin=trustd` then that main binary won't be rebuilt.
