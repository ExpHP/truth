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
    * Note: This is just *tested*, not *guaranteed*.  Some files don't recompile back because the original files are... unusual in some way.
* No possibility of segfaults!
* Cool-ass error messages, sometimes:

![Sexy error message example](./doc/img/sexy-error.png)

### Advantages over thanm

* No segfaults again
* Decompilation of loops and `if ... else ...`

### Disadvantages compared to thanm

* Can't embed/extract images

## Downloading

Everything is still so alpha at this point that I can't even fathom labeling releases with version numbers yet. For now I just post Windows builds occassionally on the #scripting channel on the [ZUNcode discord server](https://discord.gg/fvPJvHJ).

## Using

**truth is fairly alpha at this stage**:

* Lots of testing is still needed.
* The CLI and binary names still do not quite resemble the final product.  (eventually it will look like `trustd decompile` or `trustd d` for short but this is fairly low on the list of priorities)

With that in mind:

### STD

```shell
std-decompile -g13 -m map/any.stdm in.std > out.stdspec
std-compile -g13 in.stdspec -o out.std
```

These work on all games in the series.

Any mapfiles used during decompilation are recorded in the output script and automatically used during recompilation, which is why the `-m` argument is not used during compilation in the example above (though you *can* supply it if you want to).

You can set the environment variable `TRUTH_MAP_PATH` to automatically locate mapfiles during decompilation.  Each directory listed in this `PATH`-like variable will be checked for a file named `any.stdm` if you are compiling STD, `any.anmm` if you are compiling ANM, and etc.  

### ANM

You can decompile an ANM file into a script, similar to `thanm -l`.
```sh
anm-decompile -g12 -m map/any.anmm in.anm > out.spec
```

To recompile an ANM file, you will likely need to supply the original ANM file as a source to copy image data from.  This can be done using the `-i`/`--image-source` flag:

```sh
anm-compile -g12 -m map/any.anmm edited.spec -i original.anm -o out.anm
```

There is no image extraction from ANM files (and it is doubtful that there ever will need to be, since thtk remains perfectly fine for this purpose).

There is also no way to embed new images from `.png` files, as thcrap's image hotloading works just fine for this purpose.  To compile a brand new ANM file that isn't based on any original ANM file, simply make sure to supply all necessary header data in the `entry` objects along with `has_data: false`; in this case, you do NOT require the `-i` flag.  An example of such a script be found at [./tests/anm_compile/th12-no-source-required.anm.spec].  To use the compiled file, make a thcrap patch which contains images in all of the right locations.  (for instance, if the script has a `has_data: false` entry with `path: "subdir/file.png"`, the thcrap patch should have an image at e.g. `<patch_root>/th17/subdir/file.png`)

## Building and installing from source

[Install rust](https://rustup.rs/), and then:

```sh
git clone https://github.com/ExpHP/truth
cd truth

# Debug builds  (for optimized builds, change it to `cargo run --release`)
cargo run -- std-decompile -g10 -m map/any.stdm in.std > out.stdspec
cargo run -- std-compile -g10 out.stdspec -o out.std

# If you want optimized binaries installed globally:
cargo install --path=.
```

**Important:** Notice that development builds use `cargo run -- std-decompile` instead of `cargo run --bin=std-decompile`.  This is because most binaries in this project are actually shims around the main binary (`truth`), and if you do `--bin=std-decompile` then that main binary won't be rebuilt.
