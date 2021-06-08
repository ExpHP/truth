# truth

[![Build Status](https://travis-ci.org/ExpHP/truth.svg?branch=main)](https://travis-ci.org/ExpHP/truth)

Multipass compiler for touhou binary script files.

![Sexy error message example](./doc/img/sexy-error.png)

truth stands for "**t**ouhou **ru**st **th**ing".  Or maybe it stands for "**t**ouhou **ru**st **th**tk". I dunno, I mostly just picked it because `trustd` and `truecl` sound pretty dope.

## Development status

* `trustd`: in beta; **feature complete, please give it a try!**
* `truanm`: in beta
* `trumsg`: in beta

Supports **all danmaku titles TH06–TH17.**  That is:

> TH06 (EoSD), TH07 (PCB), TH08 (IN), TH09 (PoFV), TH09.5 (StB), TH10 (MoF), TH11 (SA), TH12 (UFO), TH12.3 (GFW), TH12.5 (DS), TH13 (TD), TH14 (DDC), TH14.3 (ISC), TH15 (LoLK), TH16 (HSiFS), TH16.5 (VD), TH17 (WBaWC)
> 
> Uwabami Breakers is also supported (use `-g alcostg` or `-g 103`)

## Docs

See these doc pages:

* A primer on [script syntax](./doc/syntax.md).
* A [comparison to thtk](./doc/comparison-to-thtk.md).

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

ANM files also contain images.  You can extract these using `truanm extract`:

```sh
truanm extract -g12 in.anm -o images/

# shorthand
truanm x -g12 in.anm -o images/
```

At this time, **image extraction is not thoroughly tested and may have some bugs.**

#### Compilation and image sources

ANM scripts contain `entry` blocks that each declare an image contained in the ANM file.

```C
// there are other fields, but most will use reasonable defaults
entry {
    path: "subdir/image.png",
    scripts: {
        sprite0: {id: 0, x: 0.0, y: 0.0, w: 50.0, h: 50.0},
    },
}
```

To compile an ANM file, you will likely need to supply some source of these images.  There are two types of image sources: ANM files and image directories.

##### Recompiling existing ANM files

If you are recompiling a script obtained from an ANM file, the original ANM file will serve as a suitable image source:

```sh
truanm compile -g12 edited.spec -i original.anm -o out.anm
```

When using an ANM file as an image source, each `entry` in the current script will pull the image from the entry with the same filepath inside the image source.  This mechanism can also be used to copy over any missing metadata from an `entry`.  In cases where multiple entries have the same path (which can happen for virtual files like `"@"` and `"@R"`), the duplicates are matched in order of appearance.

##### Creating brand new ANM files

If you have a thcrap patch or a directory containing the output of `truanm extract`, that can also be used as an image source:

```sh
truanm compile -g12 cool.spec -i path/to/images -o out.anm
```

In this case, the example entry above (with the path `"subdir/image.png"`) would try to load `path/to/images/subdir/image.png` if it exists.  As long as an image can be found, all fields on an `entry` will be automatically filled with reasonable defaults.

##### Mix and match

You can supply multiple image sources!  For instance, if you are recompiling an ANM file *and* adding additional images, you could supply:

```
truanm compile -g12 edited.spec -i original.anm -i my/extra/images -o out.anm
```

Note that, similar to mapfiles, image sources can alternatively be defined inside the script using `#pragma image_source`:

```C
// equivalent to '-i original.anm -i my/extra/images'
#pragma image_source "original.anm"
#pragma image_source "my/extra/images"
```

##### Supplying dummy data

If you're using thcrap and something bothers you about the fact that both your ANM file and your thcrap patch contain copies of the same images, you can put `has_data: "dummy"` on an entry (the default is `has_data: true`).  This will cause it to generate magenta dummy data in the ANM file, to be hot-swapped out by thcrap.  Note that such an entry can still automatically grab the image dimensions from an image source.

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
