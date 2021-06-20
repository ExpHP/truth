#!/usr/bin/env python3

import argparse
import os
import sys
import subprocess
import shutil
import glob

PRODUCT_NAME = 'truth'
TARGETS = ['x86_64-pc-windows-msvc']
PROG = os.path.basename(sys.argv[0])


def main():
    parser = argparse.ArgumentParser(
        description='creates a windows release zip',
    )
    args = parser.parse_args()

    if os.name != 'nt':
        die('Please run this from windows!')

    git_describe = subprocess.run(['git', 'describe'], check=True, stdout=subprocess.PIPE)
    version, = git_describe.stdout.split()
    version = version.decode('ascii')

    for target in TARGETS:
        rebuild_binaries(target)
        make_release(version, target)


def rebuild_binaries(target):
    for src_path in glob.glob(f'target/{target}/release/*.exe'):
        os.unlink(src_path)

    subprocess.run(['cargo', 'build', '--release', '--target', target], check=True)


def make_release(version, target):
    release_dir = f'release/{PRODUCT_NAME}-{version}'
    release_zip = f'release/{PRODUCT_NAME}-{version}-{target}.zip'

    shutil.rmtree(release_dir, ignore_errors=True)
    shutil.rmtree(release_zip, ignore_errors=True)
    os.makedirs(release_dir)
    print('copying map/')
    shutil.copytree('map', os.path.join(release_dir, 'map'))

    did_something = False
    for src_path in glob.glob(f'target/{target}/release/*.exe'):
        filename = os.path.basename(src_path)
        if not exe_is_public(os.path.splitext(filename)[0]):
            print(f'skipping {src_path} (private)')
            continue
        print(f'copying {src_path}')
        shutil.copyfile(src_path, os.path.join(release_dir, filename))
        did_something = True

    if not did_something:
        die("no executables copied!")

    subprocess.run(['powershell', 'Compress-Archive', '-Force', release_dir, release_zip], check=True)

def exe_is_public(name):
    import re
    fail = lambda: die("unable to determine whether '{}' is public!")

    if name == 'truth-core':
        return True

    # Find a line like:   SubcommandSpec { name: "trumsg", entry: trumsg_main, public: true },
    subcommand_lines = [line for line in open('src/cli_def.rs') if 'SubcommandSpec' in line]
    matching_lines = [line for line in subcommand_lines if f'"{name}"' in line]
    for line in matching_lines:
        matches = re.findall('public: (true|false)', line)
        if len(matches) != 1:
            fail()
        assert matches[0] in ('true', 'false'), matches[0]
        return matches[0] == 'true'
    else:
        fail()

# ------------------------------------------------------

def warn(*args, **kw):
    print(f'{PROG}:', *args, file=sys.stderr, **kw)

def die(*args, code=1):
    warn('Fatal:', *args)
    sys.exit(code)

# ------------------------------------------------------

if __name__ == '__main__':
    main()
