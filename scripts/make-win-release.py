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
    shutil.rmtree(os.path.join(release_dir, 'map', 'core'))

    for src_path in glob.glob(f'target/{target}/release/*.exe'):
        print(f'copying {src_path}')
        filename = os.path.basename(src_path)
        shutil.copyfile(src_path, os.path.join(release_dir, filename))

    if not len(list(glob.glob(f'{release_dir}/*.exe'))):
        die("no executables copied!")

    subprocess.run(['powershell', 'Compress-Archive', '-Force', release_dir, release_zip], check=True)


# ------------------------------------------------------

def warn(*args, **kw):
    print(f'{PROG}:', *args, file=sys.stderr, **kw)

def die(*args, code=1):
    warn('Fatal:', *args)
    sys.exit(code)

# ------------------------------------------------------

if __name__ == '__main__':
    main()
