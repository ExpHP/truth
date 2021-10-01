#!/usr/bin/env python3

from multiprocessing.pool import ThreadPool
import shlex
import subprocess
import argparse
import os
import sys
import time
import fnmatch

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

    ALL_FORMATS = ['anm', 'std', 'msg', 'mission', 'ecl']
    DEFAULT_FORMATS = ['anm', 'std', 'msg', 'mission']  # ECL not ready
    ALL_MODES = ['decompile', 'compile']
    parser = argparse.ArgumentParser(
        description='Script used to test recompilation of all files in all games.',
    )
    parser.set_defaults(formats=[], modes=[], game=[])
    parser.add_argument('-g', '--game', action='append', type=parse_game)
    parser.add_argument('--compile', action='append_const', dest='modes', const='compile')
    parser.add_argument('--decompile', action='append_const', dest='modes', const='decompile')
    parser.add_argument('--anm', action='append_const', dest='formats', const='anm')
    parser.add_argument('--std', action='append_const', dest='formats', const='std')
    parser.add_argument('--msg', action='append_const', dest='formats', const='msg')
    parser.add_argument('--ecl', action='append_const', dest='formats', const='ecl')
    parser.add_argument('--mission', action='append_const', dest='formats', const='mission')
    parser.add_argument('--ssd', action='store_true')
    parser.add_argument('--nobuild', action='store_false', dest='build')
    parser.add_argument('--noverify', action='store_false', dest='verify')
    parser.add_argument('--update-known-bad', action='store_true')
    parser.add_argument('-j', type=int, default=1)
    args = parser.parse_args()

    # if custom filters were given then we won't end up iterating over all files
    badfiles_is_comprehensive = args.verify and not any([args.game, args.formats, args.modes])

    if not args.game:
        args.game = [('06', '99')]

    if not args.formats:
        args.formats = list(DEFAULT_FORMATS)
    if not args.modes:
        args.modes = list(ALL_MODES)

    if args.ssd:
        INPUT_DIR = SSD_INPUT_DIR
        DUMP_DIR = SSD_DUMP_DIR

    games = [x[len(INPUT_SUBDIR_PREFIX):] for x in os.listdir(INPUT_DIR) if x.startswith(INPUT_SUBDIR_PREFIX)]
    all_files = []
    badfiles = [] if args.verify else None
    timelog = {
        f'{fmt}-{mode}': 0.0
        for fmt in ALL_FORMATS
        for mode in ['compile', 'decompile']
    }
    for game in games:
        if not any(lo <= game <= hi for (lo, hi) in args.game):
            continue
        for filename in os.listdir(f'{INPUT_DIR}/{INPUT_SUBDIR_PREFIX}{game}'):
            if get_format(game, filename) in args.formats:
                all_files.append((game, filename, timelog, badfiles, args.modes))

    if args.build:
        subprocess.run(['cargo', 'build', '--release'], check=True)
    with ThreadPool(args.j) as p:
        p.starmap(process_file, all_files)

    known_bad_path = f'{DUMP_DIR}/known-bad'
    update_known_bad = args.update_known_bad
    if os.path.exists(known_bad_path):
        known_bad = set(x.strip() for x in open(known_bad_path))
    else:
        update_known_bad = True
        known_bad = set()

    # Report files that did not roundtrip properly.
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

    # Report files that were fixed.
    if badfiles_is_comprehensive:  # (custom filters would cause badfiles to be incomplete)
        assert badfiles is not None
        fixedfiles = sorted(set(known_bad) - set(badfiles))
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

    if update_known_bad and badfiles_is_comprehensive:
        print()
        print(f'Updating {known_bad_path}')
        with open(known_bad_path, 'w') as f:
            f.writelines([line + '\n' for line in badfiles])
    elif update_known_bad:
        print()
        print(f'Refusing to update {known_bad_path} due to custom filters')

MSG_GLOBS = {
    '06': 'msg*',
    '07': 'msg*',
    '08': 'msg*',
    '09': '*.msg',
    '095': 'XXXXX',
    '10': 'st0*.msg',  # don't want to hit e*.msg or staff.msg
    '11': 'st0*.msg',
    '12': 'st0*.msg',
    '125': 'XXXXX',
    '128': 'st_*.msg',
    '13': 'st0*.msg',
    '14': 'st0*.msg',
    '143': 'msg*.msg',
    '15': 'st0*.msg',
    '16': 'st0*.msg',
    '165': 'msg*.msg',
    '17': 'st0*.msg',
    '18': 'st0*.msg',
}

def get_format(game, path):
    name = os.path.basename(path)

    if path.endswith('.std'):
        return 'std'
    elif path.endswith('.anm'):
        return 'anm'
    elif path.endswith('.ecl'):
        return 'ecl'
    elif fnmatch.fnmatch(name, MSG_GLOBS[game]):
        return 'msg'
    elif name == 'mission.msg':
        return 'mission'
    return None

# ABORT = 0
def process_file(game, file, timelog, badfiles, modes):
    # global ABORT

    input = f'{INPUT_DIR}/{INPUT_SUBDIR_PREFIX}{game}/{file}'
    outspec = f'{DUMP_DIR}/{DUMP_SUBDIR_PREFIX}{game}/{file}.spec'
    outfile = f'{DUMP_DIR}/{DUMP_SUBDIR_PREFIX}{game}/{file}'

    format = get_format(game, file)
    if format == 'std':
        decompile_args = ['target/release/trustd', 'decompile', '-g', game, input]
        compile_args = ['target/release/trustd', 'compile', '-g', game, outspec, '-o', outfile]
    elif format == 'anm':
        decompile_args = ['target/release/truanm', 'decompile', '-g', game, input]
        compile_args = ['target/release/truanm', 'compile', '-g', game, outspec, '-i', input, '-o', outfile]
    elif format == 'msg':
        decompile_args = ['target/release/trumsg', 'decompile', '-g', game, input]
        compile_args = ['target/release/trumsg', 'compile', '-g', game, outspec, '-o', outfile]
    elif format == 'mission':
        decompile_args = ['target/release/trumsg', 'decompile', '--mission', '-g', game, input]
        compile_args = ['target/release/trumsg', 'compile', '--mission', '-g', game, outspec, '-o', outfile]
    elif format == 'ecl':
        decompile_args = ['target/release/truecl', 'decompile', '-g', game, input]
        compile_args = ['target/release/truecl', 'compile', '-g', game, outspec, '-o', outfile]
    else:
        assert False, file

    os.makedirs(os.path.dirname(outspec), exist_ok=True)

    # try:
    if 'decompile' in modes:
        with open(outspec, 'w') as f:
            print(' '.join(map(shlex.quote, decompile_args)))
            start_time = time.time()
            subprocess.run(decompile_args, stdout=f, check=True)
            timelog[f'{format}-decompile'] += time.time() - start_time

    if 'compile' in modes:
        print(' '.join(map(shlex.quote, compile_args)))
        start_time = time.time()
        subprocess.run(compile_args, check=True)
        timelog[f'{format}-compile'] += time.time() - start_time

        if badfiles is not None and open(input, 'rb').read() != open(outfile, 'rb').read():
            print('!!!', outspec)
            badfiles.append(outspec)

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
