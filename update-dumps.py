#!/usr/bin/env python3

from multiprocessing.pool import ThreadPool
import shlex
import subprocess
import argparse
import os
import sys
import time

PROG = os.path.basename(sys.argv[0])

# FIXME: Absolute paths in VCS   :shock: :horror:
SSD_INPUT_DIR = '/home/exp/win/truth-bench/decomp'
SSD_DUMP_DIR = '/home/exp/win/truth-bench/all-dumps'

INPUT_DIR = '/home/exp/thcrap/decomp'
INPUT_SUBDIR_PREFIX = 'bleh'
DUMP_DIR = 'all-dumps'
DUMP_SUBDIR_PREFIX = 'th'

def main():
    global INPUT_DIR
    global DUMP_DIR

    parser = argparse.ArgumentParser(
        description='Script used to test recompilation of all files in all games.',
    )
    parser.set_defaults(what='all', game=[])
    parser.add_argument('-g', '--game', action='append', type=parse_game)
    parser.add_argument('--anm', action='store_const', dest='what', const='anm')
    parser.add_argument('--std', action='store_const', dest='what', const='std')
    parser.add_argument('--msg', action='store_const', dest='what', const='msg')
    parser.add_argument('--ssd', action='store_true')
    parser.add_argument('--nobuild', action='store_false', dest='build')
    parser.add_argument('--noverify', action='store_false', dest='verify')
    parser.add_argument('-j', type=int, default=1)
    args = parser.parse_args()

    if not args.game:
        args.game = [('06', '99')]

    if args.ssd:
        INPUT_DIR = SSD_INPUT_DIR
        DUMP_DIR = SSD_DUMP_DIR

    games = [x[len(INPUT_SUBDIR_PREFIX):] for x in os.listdir(INPUT_DIR) if x.startswith(INPUT_SUBDIR_PREFIX)]
    all_files = []
    badfiles = [] if args.verify else None
    timelog = {
        'anm-compile': 0.0,
        'anm-decompile': 0.0,
        'std-compile': 0.0,
        'std-decompile': 0.0,
        'msg-compile': 0.0,
        'msg-decompile': 0.0,
    }
    for game in games:
        if not any(lo <= game <= hi for (lo, hi) in args.game):
            continue
        for filename in os.listdir(f'{INPUT_DIR}/{INPUT_SUBDIR_PREFIX}{game}'):
            do_it = any([
                filename.endswith('.anm') and args.what in ['anm', 'all'],
                filename.endswith('.std') and args.what in ['std', 'all'],
                (filename.startswith('msg') or filename.endswith('.msg')) and args.what in ['msg', 'all'],
            ])
            if do_it:
                all_files.append((game, filename, timelog, badfiles))

    if args.build:
        subprocess.run(['cargo', 'build', '--release'], check=True)
    with ThreadPool(args.j) as p:
        p.starmap(process_file, all_files)

    known_bad = set(x.strip() for x in open(f'{DUMP_DIR}/known-bad'))

    if badfiles:
        print()
        print("BAD FILES:")
        regressions = 0
        for fname in sorted(badfiles):
            regressions += fname not in known_bad
            print(' ', fname, '' if fname in known_bad else '  (!!!!)')
        print('count:', len(badfiles))
        if regressions:
            print('regressions:', regressions)

        badfiles_set = set(badfiles)
        fixedfiles = sorted(set(known_bad) - badfiles_set)
        if fixedfiles:
            print()
            print("FIXED FILES:")
            for fname in fixedfiles:
                print(' ', fname)
            print('fixed count:', len(fixedfiles))

    print()
    print('TIMINGS:')
    for key in sorted(timelog):
        print(f'{key:14} {timelog[key]:>7.3f}')


# ABORT = 0
def process_file(game, file, timelog, badfiles):
    # global ABORT

    input = f'{INPUT_DIR}/{INPUT_SUBDIR_PREFIX}{game}/{file}'
    outspec = f'{DUMP_DIR}/{DUMP_SUBDIR_PREFIX}{game}/{file}.spec'
    outfile = f'{DUMP_DIR}/{DUMP_SUBDIR_PREFIX}{game}/{file}'

    if file.endswith('.std'):
        format = 'std'
        decompile_args = ['target/release/trustd', 'decompile', '-g', game, input]
        compile_args = ['target/release/trustd', 'compile', '-g', game, outspec, '-o', outfile]
    elif file.endswith('.anm'):
        format = 'anm'
        decompile_args = ['target/release/truanm', 'decompile', '-g', game, input]
        compile_args = ['target/release/truanm', 'compile', '-g', game, outspec, '-i', input, '-o', outfile]
    elif file.startswith('msg') or file.endswith('.msg'):
        format = 'msg'
        decompile_args = ['target/release/trumsg', 'decompile', '-g', game, input]
        compile_args = ['target/release/trumsg', 'compile', '-g', game, outspec, '-o', outfile]
    else:
        assert False, file

    # FIXME
    if game >= '10' and format == 'msg':
        return

    os.makedirs(os.path.dirname(outspec), exist_ok=True)

    # try:
    with open(outspec, 'w') as f:
        print(' '.join(map(shlex.quote, decompile_args)))
        start_time = time.time()
        subprocess.run(decompile_args, stdout=f, check=True)
        decompile_time = time.time() - start_time

    print(' '.join(map(shlex.quote, compile_args)))
    start_time = time.time()
    subprocess.run(compile_args, check=True)
    compile_time = time.time() - start_time

    if badfiles is not None and open(input, 'rb').read() != open(outfile, 'rb').read():
        print('!!!', outspec)
        badfiles.append(outspec)

    timelog[f'{format}-decompile'] += decompile_time
    timelog[f'{format}-compile'] += compile_time
    # except subprocess.CalledProcessError:
    #     ABORT = 1
    #     raise


def parse_game(s):
    if ':' in s:
        a, b = s.split(':', 2)
        return a, b
    else:
        return s, s


# ------------------------------------------------------

def warn(*args, **kw):
    print(f'{PROG}:', *args, file=sys.stderr, **kw)


def die(*args, code=1):
    warn('Fatal:', *args)
    sys.exit(code)


# ------------------------------------------------------

if __name__ == '__main__':
    main()
