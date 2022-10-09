#!/usr/bin/env python3

from multiprocessing.pool import ThreadPool
from collections import Counter, defaultdict
import shlex
import subprocess
import argparse
import os
import re
import sys
import time
import fnmatch
import warnings
import tempfile
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
    parser.set_defaults(formats=[], modes=[], game=[], decompile_args=[], image_sources=['anm'])
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

    g = parser.add_mutually_exclusive_group()
    g.add_argument('--images', dest='image_sources', action='store_const', const=['dir'], help="test image extraction and recompilation with '-i image-dir'")
    g.add_argument('--images-plus-anm', dest='image_sources', action='store_const', const=['dir', 'anm'], help="test image extraction and recompilation with '-i thing.anm -i image-dir'")

    parser.add_argument('--debug', action='store_false', dest='optimized', help='use unoptimized builds')
    parser.add_argument('--decompile-arg', dest='decompile_args', action='append', help='supply an argument during decompile commands')
    parser.add_argument('--nobuild', action='store_false', dest='build', help='do not build truth')
    parser.add_argument('--noextract', action='store_false', dest='extract', help='do not extract images, even if --images is supplied')
    parser.add_argument('--noverify', action='store_false', dest='verify', help='do not verify round-tripping (expensive)')
    parser.add_argument('--diff', action='store_true', help='display diffs where recompiled files differ')
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

    badfiles_is_comprehensive = bool(all([
        # we won't find any bad files if we don't check!
        args.verify,
        # if custom filters were given then we won't end up iterating over all files
        not args.game,
        not args.formats,
        not args.modes,
        not args.search_pattern,
        not args.decompile_args,
    ]))

    if not args.game:
        args.game = [('06', '99')]
    if not args.formats:
        args.formats = list(DEFAULT_FORMATS)
    if not args.modes:
        args.modes = list(ALL_MODES)

    timelog, badfiles = run_all_jobs(args, config)

    if args.build:
        subprocess.run(['cargo', 'build'] + (['--release'] if args.optimized else []), check=True)

    known_bad_path = f'{config.directories.binary_dump.root}/known-bad'
    update_known_bad = args.update_known_bad
    if os.path.exists(known_bad_path):
        known_bad = set(x.strip() for x in open(known_bad_path))
    else:
        known_bad = set()

    report(badfiles_is_comprehensive, badfiles, timelog, known_bad_path, update_known_bad, known_bad)

def report(
    badfiles_is_comprehensive,
    badfiles,
    timelog,
    known_bad_path,
    update_known_bad,
    known_bad,
):
    bad_filenames = None
    if badfiles is not None:
        bad_filenames = [fname for (fname, _) in badfiles]

    # Report files that did not roundtrip properly.
    if badfiles:  # falsy results are None (--noverify) or [] (no bad files)
        print()
        print("BAD FILES:")
        regressions = 0
        for fname, diff in sorted(badfiles):
            regressions += fname not in known_bad
            print(' ', fname, '' if fname in known_bad else '  (!!!!)')
            if diff:
                print(diff)
                print()
        print('count:', len(badfiles))
        if regressions:
            print('regressions:', regressions)

    # Report files that were fixed.
    if badfiles_is_comprehensive:  # (custom filters would cause badfiles to be incomplete)
        assert bad_filenames is not None
        fixedfiles = sorted(set(known_bad) - set(bad_filenames))
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
    '185': '*.msg',
    # NEWHU: 185
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


def run_all_jobs(args, config):
    badfiles = [] if args.verify else None
    timelog = Counter()

    games_to_process = [
        game for game in find_all_games(config)
        if any(lo <= game <= hi for (lo, hi) in args.game)
    ]

    if args.search_pattern:
        file_filter_re = re.compile(args.search_pattern)
        file_filter_func = lambda filename: file_filter_re.search(filename) is not None
    else:
        file_filter_func = lambda filename: True

    files_by_game_and_format = defaultdict(lambda: defaultdict(list))
    for game in games_to_process:
        for filename in os.listdir(config.directories.input.for_game(game)):
            if not file_filter_func(filename):
                continue
            format = get_format(game, filename)
            if format not in args.formats:
                continue
            files_by_game_and_format[game][format].append(filename)

    # Begin with one 'truanm extract' task per game.
    if args.extract and 'anm' in args.formats and 'dir' in args.image_sources:
        all_extract_inputs = []
        for game in games_to_process:
            game_anm_files = files_by_game_and_format[game]['anm']
            if game_anm_files:
                all_extract_inputs.append((game, game_anm_files, timelog, args, config))
        with ThreadPool(args.j) as p:
            p.starmap(run_image_extraction_task, all_extract_inputs)

    # Standard tasks for every file.
    all_files = []
    for game in games_to_process:
        for format in args.formats:
            for filename in files_by_game_and_format[game][format]:
                all_files.append((game, filename, timelog, badfiles, args, config))
    with ThreadPool(args.j) as p:
        p.starmap(run_task_for_file, all_files)

    return timelog, badfiles


def run_task_for_file(game, file, timelog, badfiles, args, config):
    input = config.directories.input.for_game(game) + f'/{file}'
    outspec = config.directories.text_dump.for_game(game) + f'/{file}.spec'
    outfile = config.directories.binary_dump.for_game(game) + f'/{file}'
    outimgdir = config.directories.image_dump.for_game(game)

    bindir = cargo_bin_dir(args)
    format = get_format(game, file)
    if format == 'std':
        decompile_args = [f'{bindir}/trustd', 'decompile', '-g', game] + args.decompile_args
        compile_args = [f'{bindir}/trustd', 'compile', '-g', game]
    elif format == 'anm':
        decompile_args = [f'{bindir}/truanm', 'decompile', '-g', game] + args.decompile_args
        compile_args = [f'{bindir}/truanm', 'compile', '-g', game]
        if 'anm' in args.image_sources:
            compile_args += ['-i', input]
        if 'dir' in args.image_sources:
            compile_args += ['-i', outimgdir]
    elif format == 'msg':
        decompile_args = [f'{bindir}/trumsg', 'decompile', '-g', game] + args.decompile_args
        compile_args = [f'{bindir}/trumsg', 'compile', '-g', game]
    elif format == 'mission':
        decompile_args = [f'{bindir}/trumsg', 'decompile', '--mission', '-g', game] + args.decompile_args
        compile_args = [f'{bindir}/trumsg', 'compile', '--mission', '-g', game]
    elif format == 'ecl':
        decompile_args = [f'{bindir}/truecl', 'decompile', '-g', game] + args.decompile_args
        compile_args = [f'{bindir}/truecl', 'compile', '-g', game]
    else:
        assert False, file

    os.makedirs(os.path.dirname(outspec), exist_ok=True)
    os.makedirs(os.path.dirname(outfile), exist_ok=True)

    if 'decompile' in args.modes:
        start_time = time.time()
        echo_run(decompile_args + [input, '-o', outspec], check=True)
        timelog[f'{format}-decompile'] += time.time() - start_time

    if 'compile' in args.modes:
        start_time = time.time()
        echo_run(compile_args + [outspec, '-o', outfile], check=True)
        timelog[f'{format}-compile'] += time.time() - start_time

        if badfiles is not None and open(input, 'rb').read() != open(outfile, 'rb').read():
            diff = None
            if args.diff:
                diff = get_diff(decompile_args, compile_args, input, outspec, outfile)
            print('!!!', outspec)
            badfiles.append((outspec, diff))

def run_image_extraction_task(game, files, timelog, args, config):
    inputs = [
        config.directories.input.for_game(game) + f'/{file}'
        for file in files
    ]
    outimgdir = config.directories.image_dump.for_game(game)
    bindir = cargo_bin_dir(args)

    os.makedirs(os.path.dirname(outimgdir), exist_ok=True)

    start_time = time.time()
    echo_run([f'{bindir}/truanm', 'extract', '-g', game, '-o', outimgdir] + inputs, check=True, stdout=subprocess.DEVNULL)
    timelog[f'{format}-extract'] += time.time() - start_time


def cargo_bin_dir(args):
    return 'target/' + ('release' if args.optimized else 'debug')

def echo_run(args, **kw):
    print(' '.join(map(shlex.quote, args)))
    subprocess.run(args, **kw)


def get_diff(decompile_args, compile_args, input, outspec, outfile):
    with tempfile.TemporaryDirectory() as tmpdir:
        # decompile again
        diff_respec = f'{tmpdir}/recompiled'
        subprocess.run(decompile_args + [outfile, '-o', diff_respec], check=True)

        diff = get_git_diff_output(outspec, diff_respec)
        if diff:
            return diff

        # if decompiling again produced the same result, maybe the bug is in intrinsics or argument decoding.
        # start over from scratch, with progressively conservative decompilation flags.
        diff_outspec = f'{tmpdir}/decompiled'
        diff_outfile = f'{tmpdir}/compiled'
        for arg_to_add in ['--no-blocks', '--no-intrinsics', '--no-arguments']:
            if arg_to_add in decompile_args:
                continue  # pointless to try, and adding the same arg twice might be an error

            subprocess.run(decompile_args + [input, '-o', diff_outspec] + [arg_to_add], check=True)
            subprocess.run(compile_args + [diff_outspec, '-o', diff_outfile], check=True)
            subprocess.run(decompile_args + [diff_outfile, '-o', diff_respec] + [arg_to_add], check=True)

            diff = get_git_diff_output(diff_outspec, diff_respec)
            if diff:
                return diff

        # we give up, it's something weird in the header data probably, just get the "binary files differ" message
        diff = get_git_diff_output(input, outfile)
        assert diff
        return diff

def get_git_diff_output(a_path, b_path):
    result = subprocess.run(['git', 'diff', '--no-index', '--color=always', a_path, b_path], text=True, capture_output=True)
    if result.returncode:
        return result.stdout
    else:
        return None  # files are identical


def find_all_games(config):
    input_dirs = config.directories.input
    games = [
        x[len(input_dirs.subdir_prefix):]
        for x in os.listdir(input_dirs.root)
        if x.startswith(input_dirs.subdir_prefix)
    ]

    suspicious_games = [g for g in games if g not in MSG_GLOBS]
    if suspicious_games:
        suspicious_str = ', '.join(f'{input_dirs.subdir_prefix}')
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
        self.image_dump = ConfigDirectory(d.pop('image-dump'), self_key=f'{self_key}.image-dump')

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
        self.dir_inside = d.pop('dir-inside', None)

        if self.dir_inside == '':
            self.dir_inside = None

        for key in d:
            full_key = f'{self_key}.{key}'
            warnings.warn(f'unrecognized key {repr(full_key)} in config')

    def for_game(self, game):
        path = f'{self.root}/{self.subdir_prefix}{game}'
        if self.dir_inside is not None:
            path = f'{path}/{self.dir_inside}'
        return path

# ------------------------------------------------------

def warn(*args, **kw):
    print(f'{PROG}:', *args, file=sys.stderr, **kw)


def die(*args, code=1):
    warn('Fatal:', *args)
    sys.exit(code)


# ------------------------------------------------------

if __name__ == '__main__':
    main()
