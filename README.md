# truth

[THTK](https://github.com/thpatch/thtk/) alternative.

Currently it can only handle STD files because (a) STD is the easiest format to handle since it has no variables, and (b) the current `thstd` is garbage and I wanted to fill that hole.

truth stands for "**t**htk **ru**st **th**ing".  Or maybe it stands for "**t**htk **ru**st **th**tk". I dunno, I mostly just picked it because `trustd` and `truecl` sound pretty dope

### Advantages over thstd

I mean, this isn't really a fair comparison given how far `thstd` is behind its brothers is, but:

* Nicer formatting of metadata. (more like ANM)
* `stdmap`s for naming instructions.
* [`gamemap`s](./map/any.stdm) so you don't need to memorize the right maps for each game
* Constant expression evaluation.  `(1 < 3) ? 4.0f : 2.0 + 0.5`
* Correct treatment of "strip" quads in TH08, TH09.
* Labels and `goto`.
* No possibility of segfaults!
* Cool-ass error messages, sometimes:

![Sexy error message example](./doc/img/sexy-error.png)

### Disadvantages compared to thanm and thecl

* Everything

## Downloading

Uhhmmmm........ I'm gonna see if I can get GitHub Actions to build rust binaries on Windows.  Until then, see the "Building and running from source" section.

## Using

**truth is EXTREMELY alpha at this stage**:

* The tools currently available are mostly just things I shat out for testing purposes and do not resemble any vision of the final CLI at all.
* Lots of bad error messages.  Many placeholders.

With that in mind:

```sh
std-decomp -m map/any.stdm in.std > out.stdspec
std-compile -m map/any.stdm in.stdspec -o out.std

# Any other binaries included in the distribution are entirely worthless testing tools,
# don't even bother with them.
```

These should work on all games in the series, though I am still ironing out a small number of kinks at present.

You can set the environment variable `TRUTH_MAP_PATH` to automatically locate mapfiles during decompilation.  Each directory listed in this `PATH`-like variable will be checked for a file named `any.stdm` if you are compiling STD, `any.anmm` if you are compiling ANM, and etc.  

## Building and installing from source

[Install rust](https://rustup.rs/), and then:

```sh
git clone https://github.com/ExpHP/truth
cd truth
cargo build --release

cargo run --release --bin=std-decomp -- -g10 -m std-14.stdm in.std > out.stdspec
cargo run --release --bin=std-compile -- -g10 -m std-14.stdm out.stdspec > in.std
```

