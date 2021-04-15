
# Comparison to thtk

Some concrete benefits afforded today by truth over thtk are:

* **Nice error messages.**  Using the [`codespan-reporting` crate](https://github.com/brendanzab/codespan), error messages display labeled snippets of the problematic code, providing useful context.

* **No segfaults.**  Even if you encounter a bug in the program, it will always produce some sort of error message and optional stacktrace.

* **[gamemaps](./map/any.stdm)** so you don't need to memorize the right mapfiles for each game.

* **Tested.** thecl is a complicated program, which is troublesome because it also has no automated tests! truth has a large suite of unit tests and integration tests to help prevent bugs before they ever happen.

* **Consistency.**  Each program in thtk is fundamentally a separate tool from all of the others, leading to inconsistencies between them. In `truth`, a significant portion of the code is shared between all tools.

That said, there are also a number of downsides at present:

* **No unpacking/repacking of container formats.**  The focus of truth is specifically on compilation and decompilation, not on dealing with archives.  That means that truth has no equivalent for any of the following commands (you are expected to use thtk for these):
    * `thdat -x` for dat file extraction
    * `thdat -c` for dat file creation
    * `thanm -x` for image extraction
    * Automatic embedding of `.png` files during `thanm -c`.
* **Incomplete.** Not all languages are implemented (most notably ECL!).  Many of thecl's features are planned but not yet implemented.
* **Not yet stable.** `truth` is in an experimental stage and language syntax may change at any point.
* **Fewer maintainers.** The [bus factor](https://en.wikipedia.org/wiki/Bus_factor) of this project is not very good, so there's always that chance that it might just suddenly stop receiving updates forever. (if you'd like to see this project succeed, please consider contributing!)

And specific to some of the binaries:

## Comparison of trustd to thstd

* trustd has thstd's most important missing features:
    * Labels and `goto`!
    * `stdmap`s for naming instructions!
* Nicer formatting of metadata. (more like ANM)
* Decompilation of loops.
* Constant expression evaluation.  `(1 < 3) ? 4.0f : 2.0 + 0.5`
* Correct treatment of "strip" quads in TH08, TH09.

## Comparison of truanm to thanm

**truanm** already has a number of features that are currently only available in thtk's experimental [`thanm-new-spec-format` branch](https://github.com/thpatch/thtk/tree/thanm-new-spec-format):

* C-like syntax like thecl.  (in fact, `truanm` and `trustd` use *the same parser*)
* Automatic allocation of temporary registers for complex expressions

there are some new things as well:

* Decompilation of loops and `if ... else ...`.

## Features currently missing from truth

truanm still needs these features before it can be considered "feature complete":

* [ ] **compiling expressions that involve jumps.**  (e.g. `a == b` and `a || b` in arbitrary expressions; currently these are only supported inside `if (...)`)
