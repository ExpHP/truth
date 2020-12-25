# truth

[THTK](https://github.com/thpatch/thtk/) alternative.

Currently it can only handle STD files because (a) the current `thstd` is garbage and (b) STD is also the easiest format to handle since it has no variables.

truth stands for "**t**htk **ru**st **th**ing".  Or maybe it stands for "**t**htk **ru**st **th**tk". I dunno, I mostly just picked it because `trustd` and `truecl` sound pretty dope

### Advantages over thstd

I mean, the current thstd is so ridiculously basic that this isn't even a fair comparison, but:

* Nicer formatting of metadata. (more like ANM)
* Constant expression evaluation.  `(1 < 3) ? 4.0f : 2.0 + 0.5`
* Labels.
* No segfaults.

### Disadvantages compared to thanm and thecl

* Everything.

## Downloading

Uhhmmmm........ I'm gonna see if I can get GitHub Actions to build rust binaries on Windows.  Until then, see the "Building and running from source" section.

## Using

**truth is EXTREMELY alpha at this stage**:

* The tools currently available are mostly just things I shat out for testing purposes and do not resemble any vision of the final CLI at all.
* Lots of bad error messages.  Many placeholders.

With that in mind:

```sh
std-decomp -m std-14.stdm in.std > out.stdspec
std-compile -m std-14.stdm in.stdspec -o out.std

# The other two binaries are entirely worthless, don't even bother with them.
```

These should work on TH095-TH17.  *Probably*.  They **definitely absolutely will not work on TH06-TH08 yet** because there's a thing I haven't added yet so just chill out okay

## Building and installing from source

[Install rust](https://rustup.rs/), and then:

```sh
git clone https://github.com/ExpHP/truth
cd truth
cargo install --path .
```

