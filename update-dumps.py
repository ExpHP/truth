#!/usr/bin/env python3

from multiprocessing.pool import ThreadPool
import shlex
import subprocess
import argparse
import os
import re
import sys
import time
import fnmatch
import warnings
try:
    from ruamel.yaml import YAML
except ImportError:
    print('Please install ruamel.yaml:', file=sys.stderr)
    print('    python3 -m pip install ruamel.yaml', file=sys.stderr)
    sys.exit(1)
yaml = YAML(typ='safe')

PROG = os.path.basename(sys.argv[0])
PROG_DIR = os.path.dirname(os.path.realpath(__file__))

DEFAULT_CONFIG_FILENAME = 'update-dumps.yaml'
EXAMPLE_CONFIG_FILENAME = 'update-dumps-example.yaml'

def main():
    global INPUT_DIR
    global DUMP_DIR

    ALL_FORMATS = ['anm', 'std', 'msg', 'mission', 'ecl']
    DEFAULT_FORMATS = ['anm', 'std', 'msg', 'mission']  # ECL not ready
    ALL_MODES = ['decompile', 'compile']
    parser = argparse.ArgumentParser(
        description='Script used to test recompilation of all files in all games.',
    )
    parser.set_defaults(formats=[], modes=[], game=[], decompile_args=[])
    parser.add_argument('-c', '--config', type=str, default=None, help=
        'path to config file. If not provided, will default to reading '
        f'{DEFAULT_CONFIG_FILENAME} from the directory with this script.'
    )
    parser.add_argument('-g', '--game', action='append', type=parse_game)
    parser.add_argument('--compile', action='append_const', dest='modes', const='compile', help='restrict to the recompilation step')
    parser.add_argument('--decompile', action='append_const', dest='modes', const='decompile', help='restrict to the decompilation step')
    parser.add_argument('--anm', action='append_const', dest='formats', const='anm', help='restrict to anm files. (and any other language flags used)')
    parser.add_argument('--std', action='append_const', dest='formats', const='std', help='restrict to std files. (and any other language flags used)')
    parser.add_argument('--msg', action='append_const', dest='formats', const='msg', help='restrict to msg files. (and any other language flags used)')
    parser.add_argument('--ecl', action='append_const', dest='formats', const='ecl', help='restrict to ecl files. (and any other language flags used)')
    parser.add_argument('--mission', action='append_const', dest='formats', const='mission', help='restrict to mission files. (and any other language flags used)')
    parser.add_argument('--debug', action='store_false', dest='optimized', help='use unoptimized builds')
    parser.add_argument('--decompile-arg', dest='decompile_args', action='append', help='supply an argument during decompile commands')
    parser.add_argument('--nobuild', action='store_false', dest='build', help='do not build truth')
    parser.add_argument('--noverify', action='store_false', dest='verify', help='do not verify round-tripping (expensive)')
    parser.add_argument('--update-known-bad', action='store_true', help='bless the new list of bad files')
    parser.add_argument('-k', '--search-pattern', type=str, help='filter the filenames tested to contain a regular expression')
    parser.add_argument('-j', type=int, default=1, help='run this many jobs in parallel')
    args = parser.parse_args()

    if args.config is None:
        default_config_path = os.path.join(PROG_DIR, DEFAULT_CONFIG_FILENAME)
        if os.path.exists(default_config_path):
            args.config = default_config_path
        else:
            die(
                f'no config file! Please create {DEFAULT_CONFIG_FILENAME}. '
                f'See {EXAMPLE_CONFIG_FILENAME} for an example.'
            )

    config = Config.from_path(args.config)

    # if custom filters were given then we won't end up iterating over all files
    badfiles_is_comprehensive = args.verify and not any([args.game, args.formats, args.modes])

    if not args.game:
        args.game = [('06', '99')]

    if not args.formats:
        args.formats = list(DEFAULT_FORMATS)
    if not args.modes:
        args.modes = list(ALL_MODES)

    if args.search_pattern:
        file_filter_re = re.compile(args.search_pattern)
        file_filter_func = lambda filename: file_filter_re.search(filename) is not None
    else:
        file_filter_func = lambda filename: True

    games = find_all_games(config)
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
        for filename in os.listdir(config.directories.input.for_game(game)):
            if not file_filter_func(filename):
                continue
            if get_format(game, filename) not in args.formats:
                continue
            all_files.append((game, filename, timelog, badfiles, args.modes, args.optimized, args.decompile_args, config))

    if args.build:
        subprocess.run(['cargo', 'build'] + (['--release'] if args.optimized else []), check=True)
    with ThreadPool(args.j) as p:
        p.starmap(process_file, all_files)

    known_bad_path = f'{config.directories.binary_dump.root}/known-bad'
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
def process_file(game, file, timelog, badfiles, modes, optimized, extra_decompile_args, config):
    # global ABORT

    input = config.directories.input.for_game(game) + f'/{file}'
    outspec = config.directories.text_dump.for_game(game) + f'/{file}.spec'
    outfile = config.directories.binary_dump.for_game(game) + f'/{file}'

    bindir = f'target/' + ('release' if optimized else 'debug')

    format = get_format(game, file)
    if format == 'std':
        decompile_args = [f'{bindir}/trustd', 'decompile', '-g', game, input, '-o', outspec] + extra_decompile_args
        compile_args = [f'{bindir}/trustd', 'compile', '-g', game, outspec, '-o', outfile]
    elif format == 'anm':
        decompile_args = [f'{bindir}/truanm', 'decompile', '-g', game, input, '-o', outspec] + extra_decompile_args
        compile_args = [f'{bindir}/truanm', 'compile', '-g', game, outspec, '-i', input, '-o', outfile]
    elif format == 'msg':
        decompile_args = [f'{bindir}/trumsg', 'decompile', '-g', game, input, '-o', outspec] + extra_decompile_args
        compile_args = [f'{bindir}/trumsg', 'compile', '-g', game, outspec, '-o', outfile]
    elif format == 'mission':
        decompile_args = [f'{bindir}/trumsg', 'decompile', '--mission', '-g', game, input, '-o', outspec] + extra_decompile_args
        compile_args = [f'{bindir}/trumsg', 'compile', '--mission', '-g', game, outspec, '-o', outfile]
    elif format == 'ecl':
        decompile_args = [f'{bindir}/truecl', 'decompile', '-g', game, input, '-o', outspec] + extra_decompile_args
        compile_args = [f'{bindir}/truecl', 'compile', '-g', game, outspec, '-o', outfile]
    else:
        assert False, file

    os.makedirs(os.path.dirname(outspec), exist_ok=True)
    os.makedirs(os.path.dirname(outfile), exist_ok=True)

    # try:
    if 'decompile' in modes:
        print(' '.join(map(shlex.quote, decompile_args)))
        start_time = time.time()
        subprocess.run(decompile_args, check=True)
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

def find_all_games(config):
    input_dirs = config.directories.input
    games = [
        x[len(input_dirs.subdir_prefix):]
        for x in os.listdir(input_dirs.root)
        if x.startswith(input_dirs.subdir_prefix)
    ]

    suspicious_games = [g for g in games if g not in MSG_GLOBS]
    if suspicious_games:
        supicious_str = ', '.join(f'{input_dirs.subdir_prefix}')
        warnings.warn(
            f'unrecognized game numbers: {suspicious_str}\n'
            'Maybe support hasn\'t been added. Make sure all game numbers < 10 are zero-padded!'
        )

    return sorted(set(games) - set(suspicious_games))

def parse_game(s):
    if ':' in s:
        a, b = s.split(':', 2)
        return a, b
    else:
        return s, s


# ------------------------------------------------------

class Config:
    def __init__(self, d):
        if not isinstance(d, dict):
            die(f'at config root: expected dict, got {type(d)}')

        d = dict(d)
        self.directories = ConfigDirectories(d.pop('directories'), self_key='directories')

        for key in d:
            warnings.warn(f'unrecognized key {repr(key)} in config')

    @classmethod
    def from_path(cls, path):
        with open(path) as f:
            d = yaml.load(f)
        return cls(d)

class ConfigDirectories(dict):
    def __init__(self, d, self_key):
        if not isinstance(d, dict):
            die(f'at config key {repr(self_key)}: expected dict, got {type(d)}')

        d = dict(d)
        self.input = ConfigDirectory(d.pop('input'), self_key=f'{self_key}.input')
        self.text_dump = ConfigDirectory(d.pop('text-dump'), self_key=f'{self_key}.text-dump')
        self.binary_dump = ConfigDirectory(d.pop('binary-dump'), self_key=f'{self_key}.binary-dump')

        for key in d:
            full_key = f'{self_key}.{key}'
            warnings.warn(f'unrecognized key {repr(full_key)} in config')

class ConfigDirectory:
    def __init__(self, d, self_key):
        if not isinstance(d, dict):
            die(f'at config key {repr(self_key)}: expected dict, got {type(d)}')

        d = dict(d)
        self.root = d.pop('root')
        self.subdir_prefix = d.pop('subdir-prefix')

        for key in d:
            full_key = f'{self_key}.{key}'
            warnings.warn(f'unrecognized key {repr(full_key)} in config')

    def for_game(self, game):
        return f'{self.root}/{self.subdir_prefix}{game}'

# ------------------------------------------------------

def warn(*args, **kw):
    print(f'{PROG}:', *args, file=sys.stderr, **kw)


def die(*args, code=1):
    warn('Fatal:', *args)
    sys.exit(code)


# ------------------------------------------------------

if __name__ == '__main__':
    main()
