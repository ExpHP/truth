# truth

[![Build Status](https://travis-ci.org/ExpHP/truth.svg?branch=main)](https://travis-ci.org/ExpHP/truth)

Multipass compiler for touhou binary script files.

![Sexy error message example](./doc/img/sexy-error.png)

truth stands for "**t**ouhou **ru**st **th**ing".  Or maybe it stands for "**t**ouhou **ru**st **th**tk". I dunno, I mostly just picked it because `trustd` and `truecl` sound pretty dope.

Tools provided:

* `trustd` for `.std` files
* `truanm` for `.anm` files
* `trumsg` for most msg files
* `trumsg --mission` for `mission.msg`

Supports **all danmaku titles TH06–TH18.**  That is:

> TH06 (EoSD), TH07 (PCB), TH08 (IN), TH09 (PoFV), TH09.5 (StB), TH10 (MoF), TH11 (SA), TH12 (UFO), TH12.3 (GFW), TH12.5 (DS), TH13 (TD), TH14 (DDC), TH14.3 (ISC), TH15 (LoLK), TH16 (HSiFS), TH16.5 (VD), TH17 (WBaWC), TH18 (UM)
> 
> Uwabami Breakers is also supported (use `-g alcostg` or `-g 103`)

# Downloading

Get the latest Windows releases [right here on GitHub](https://github.com/ExpHP/truth/tags)!

Development builds may also be posted occationally on the `#tools-dev` channel on the [ZUNcode discord server](https://discord.gg/fvPJvHJ).

For even more bleeding edge, see [Building from source](#building-and-installing-from-source) below.

## Docs

See these doc pages:

* A primer on [script syntax](./doc/syntax.md).
* A [comparison to thtk](./doc/comparison-to-thtk.md).

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

#### Compilation of brand new ANM files

Directories containing image files are also valid image sources:

```C
#pragma image_source "path/to/directory"
```

In this case, an entry with the path `"subdir/image.png"` will try to load `path/to/directory/subdir/image.png` if it exists (unless the entry has `has_data: false`).  As long as an image can be found, all fields on an `entry` will be automatically filled with reasonable defaults.

```C
// this is all you need for a valid entry,
// so long as the image can be located
entry {
    path: "subdir/image.png",
    scripts: {
        sprite0: {id: 0, x: 0.0, y: 0.0, w: 50.0, h: 50.0},
    },
}
```

If you're using thcrap and something bothers you about the fact that both your ANM file and your thcrap patch contain copies of the same images, you can put `has_data: "generate"` on an entry (the default is `has_data: true`).  This will cause it to generate magenta dummy data in the ANM file, to be hot-swapped out by thcrap.  Note that such an entry can still automatically grab the image dimensions from an image source.

### MSG files — `trumsg`

MSG files are nothing special; just follow the same instructions for STD files, but using `trumsg`.

Well.  **Some** MSG files are special:

* `mission.msg` in TH095 and TH125 is a *completely different format* from other MSG files.  To work with it you must **supply the `--mission` flag.**
* Ending (e.g. `e01.msg`) and Staff Roll (e.g. `staff1.msg`) files use a different instruction set.  It is possible to work with them but you'll need to create a special mapfile.  Ping me on Discord and I'll see if I can throw one together.

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
