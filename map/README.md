# pre-packaged mapfiles

These mapfiles are available for your personal use.  They are mostly based on [priw8's eclfiles repo](https://github.com/Priw8/eclmap).

The recommended files to use are:

* `any.anmm` for ANM
* `any.stdm` for STD

If you mess around a lot with decompilation and hate writing the path to this directory, you can tell `truth` to use these files by default during decompilation by pointing `TRUTH_MAPFILE_PATH` to this directory.  (the resulting scripts will contain an absolute path reference to this directory, so don't do this for things you're checking into VCS!)
