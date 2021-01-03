# truth

Multipass [THTK](https://github.com/thpatch/thtk/) alternative.

Currently it handles STD files fairly well (much better than thstd) and is beginning to support ANM.

truth stands for "**t**htk **ru**st **th**ing".  Or maybe it stands for "**t**htk **ru**st **th**tk". I dunno, I mostly just picked it because `trustd` and `truecl` sound pretty dope

### Advantages over thstd

I mean, this isn't really a fair comparison given how far `thstd` is behind its brothers is, but:

* Nicer formatting of metadata. (more like ANM)
* `stdmap`s for naming instructions.
* [`gamemap`s](./map/any.stdm) so you don't need to memorize the right maps for each game
* Constant expression evaluation.  `(1 < 3) ? 4.0f : 2.0 + 0.5`
* Correct treatment of "strip" quads in TH08, TH09.
* Labels and `goto`.
* Round trip decompilation and compilation is tested to produce bit-for-bit identical output.
* No possibility of segfaults!
* Cool-ass error messages, sometimes:

![Sexy error message example](./doc/img/sexy-error.png)

### Disadvantages compared to thanm and thecl

* Everything

## Downloading

Everything is still so alpha at this point that I can't even fathom labeling releases with version numbers yet. For now I just post Windows builds occassionally on the #scripting channel on the [ZUNcode discord server](https://discord.gg/fvPJvHJ).

## Using

**truth is EXTREMELY alpha at this stage**:

* The tools currently available are mostly just things I shat out for testing purposes and do not resemble any vision of the final CLI at all.
* Some bad error messages still remain.

With that in mind:

### STD

```sh
std-decomp -g13 -m map/any.stdm in.std > out.stdspec
std-compile -g13 -m map/any.stdm in.stdspec -o out.std
```

These work on all games in the series.

You can set the environment variable `TRUTH_MAP_PATH` to automatically locate mapfiles during decompilation.  Each directory listed in this `PATH`-like variable will be checked for a file named `any.stdm` if you are compiling STD, `any.anmm` if you are compiling ANM, and etc.  

### ANM

You can decompile an ANM file into a script, similar to `thanm -l`.
```sh
anm-decomp -g12 -m map/any.anmm in.anm > out.spec
```

There is no image extraction from ANM files (and it is doubtful that there ever will need to be, since thtk remains perfectly fine for this purpose).

Compilation currently requires the use of an existing ANM file as a base, to use as a source of embedded images.  The scripts and sprites in your script file will replace the ones in the ANM file.  This is just a concept I am playing around with, and some more experimentation is needed to see what sort of design will work well.

```sh
anm-modify -g12 -m map/any.anmm in.anm text.spec -o out.anm
```

More specifically, each `entry` in the text file will be matched to the corresponding one in the anm file by order of appearance, and the list of sprites and scripts under that entry in the text file will replace the lists in the original entry.  Brand new entries can also be added to the end.

## Building and installing from source

[Install rust](https://rustup.rs/), and then:

```sh
git clone https://github.com/ExpHP/truth
cd truth

# Debug builds  (for optimized builds, change it to `cargo run --release`)
cargo run --bin=std-decomp -- -g10 -m map/any.stdm in.std > out.stdspec
cargo run --bin=std-compile -- -g10 -m map/any.stdm out.stdspec > in.std

# If you want optimized binaries installed globally:
cargo install --path=.
```

