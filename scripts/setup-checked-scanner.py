#!/usr/bin/env python3
"""Build or check the fixed checked-scanner overlay; never execute submitted Lean."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

REVISION = '047f63070309f436b66c61e276ab3b6d1169265a'
OVERLAY_SHA = 'b3c6fd1b1aea261f00fc7a6306581bc0bbcb922c87f09ced26e2eb219a6dd9d8'
LAKE_MANIFEST_SHA = '4cdbe461119e6ec8191f69c036ee774ec1f00948787334af98e86ce915b4b04d'
ORIGINAL_SHA = 'f2b1c28ddf273542a0ce2ae56be054f7a27c67918fc1cfaef172a5f647c5bc28'
REVISED_SHA = '3d94b61e0b1354a6b7d2992f17e8599a311ae5e5a9feb1d62596dfeadbd0a336'
MODULE = 'EvmYul.EVM.Semantics'
TIMEOUT = 45
ROOT = Path(__file__).resolve().parent.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    require(path.is_file() and not path.is_symlink(), f'Missing or symlinked file: {path}')
    return hashlib.sha256(path.read_bytes()).hexdigest()


def clean_env():
    env = os.environ.copy()
    for key in list(env):
        if key == 'LEAN' or key.startswith(('LEAN_', 'LAKE_', 'GIT_')):
            del env[key]
    return env


def command(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, env=clean_env(), text=True,
                                   stderr=subprocess.STDOUT, timeout=TIMEOUT).strip()


def git(path, *args):
    return command(['git', '--no-optional-locks', '-C', str(path), *args])


def checkout(path, revision):
    require(git(path, 'rev-parse', 'HEAD') == revision, f'Wrong pinned revision: {path}')
    require(not git(path, 'status', '--porcelain', '--untracked-files=no'),
            f'Tracked checkout changes: {path}')


def imports(text):
    result = []
    for line in re.findall(r'^import\s+([^\n]+)', text, re.M):
        for name in line.split('--', 1)[0].split():
            require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name), 'Unsupported pinned import')
            result.append(name)
    return result


def inventory(semantics, lean, out):
    """Recompute all paths and identities from fixed inputs, never a saved manifest."""
    overlay_path = ROOT / 'lean/checked-scanner/overlay.json'
    require(digest(overlay_path) == OVERLAY_SHA, 'Checked-scanner overlay identity mismatch')
    overlay = json.loads(overlay_path.read_text())
    require(overlay['base_revision'] == REVISION and overlay['original_sha256'] == ORIGINAL_SHA
            and overlay['revised_sha256'] == REVISED_SHA, 'Overlay metadata mismatch')
    checkout(semantics, REVISION)
    require((semantics / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.22.0',
            'Wrong upstream Lean toolchain')
    manifest_path = semantics / 'lake-manifest.json'
    require(digest(manifest_path) == LAKE_MANIFEST_SHA, 'Pinned dependency manifest mismatch')
    packages = json.loads(manifest_path.read_text())
    require(packages['packagesDir'] == '.lake/packages', 'Unexpected package directory')
    require(lean.name == 'lean' and lean.parent.name == 'bin', 'Expected explicit toolchain bin/lean')
    tool_hash = digest(lean)
    version = command([str(lean), '--version'])
    require(version.startswith('Lean (version 4.22.0,'), 'Expected Lean 4.22.0')
    toolchain = lean.parent.parent
    require(not out.is_relative_to(semantics) and not semantics.is_relative_to(out)
            and not out.is_relative_to(toolchain) and not toolchain.is_relative_to(out)
            and (not out.is_relative_to(ROOT) or out.is_relative_to(ROOT / '.tools'))
            and not ROOT.is_relative_to(out),
            'Output must be separate from source checkouts, toolchain and setup source')
    source_path = semantics / 'EvmYul/EVM/Semantics.lean'
    require(digest(source_path) == ORIGINAL_SHA, 'Original semantics source identity mismatch')
    original = source_path.read_text()
    require(original.count(overlay['before']) == 1, 'Overlay requires one exact replacement')
    revised = original.replace(overlay['before'], overlay['after'])
    require(hashlib.sha256(revised.encode()).hexdigest() == REVISED_SHA,
            'Revised semantics source identity mismatch')

    # Only tracked pinned modules can define the graph; untracked files cannot add imports.
    tracked = git(semantics, 'ls-tree', '-r', '--name-only', REVISION).splitlines()
    graph = {}
    source_files = {}
    for name in tracked:
        if not name.endswith('.lean') or not (name.startswith(('EvmYul/', 'Conform/'))
                                             or name == 'EvmYul.lean'):
            continue
        path = semantics / name
        require(path.resolve().is_relative_to(semantics), 'Upstream source escapes checkout')
        digest(path)
        module = name[:-5].replace('/', '.')
        graph[module] = imports(path.read_text())
        source_files[module] = path
    require(MODULE in graph, 'Missing tracked semantics module')
    ancestors = set()

    def visit(module):
        for dependency in graph[module]:
            if dependency in graph and dependency not in ancestors:
                ancestors.add(dependency)
                visit(dependency)
    visit(MODULE)
    reverse = {MODULE}
    while True:
        updated = reverse | {name for name, deps in graph.items() if reverse.intersection(deps)}
        if updated == reverse:
            break
        reverse = updated
    require(not ancestors.intersection(reverse), 'Cyclic semantics import graph')
    require(reverse == {MODULE, 'EvmYul', 'Conform.Main', 'Conform.TestParser', 'Conform.TestRunner'}
            and len(ancestors) == 52, 'Unexpected pinned semantics dependency closure')
    owned = sorted(ancestors | {MODULE})

    roots = []
    package_revisions = {}
    for package in packages['packages']:
        name, revision = package['name'], package['rev']
        require(package['type'] == 'git' and package.get('subDir') is None
                and re.fullmatch(r'[A-Za-z0-9_-]+', name)
                and re.fullmatch(r'[0-9a-f]{40}', revision), 'Unsupported dependency entry')
        path = semantics / '.lake/packages' / name
        require(path.resolve() == path, 'Symlinked package checkout')
        checkout(path, revision)
        cache = path / '.lake/build/lib/lean'
        if cache.exists():
            roots.append(cache)
        package_revisions[name] = revision
    roots.append(toolchain / 'lib/lean')
    require(len(set(roots)) == len(roots), 'Duplicate dependency roots')
    external = {}
    resolved = {}
    for root in roots:
        require(root.is_dir() and root.resolve() == root, f'Missing or symlinked dependency root: {root}')
        for path in sorted(root.rglob('*.olean')):
            require(path.resolve().is_relative_to(root), 'External object escapes dependency root')
            name = '.'.join(path.relative_to(root).with_suffix('').parts)
            require(name not in graph, f'Upstream module shadow in external root: {name}')
            require(name not in resolved, f'Ambiguous external module: {name}')
            resolved[name] = str(path)
            external[str(path)] = digest(path)
    reused = {}
    for name in sorted(ancestors):
        rel = Path(name.replace('.', '/') + '.olean')
        obj = semantics / '.lake/build/lib/lean' / rel
        require(obj.resolve().is_relative_to(semantics / '.lake/build/lib/lean'),
                'Ancestor object escapes original build root')
        reused[name] = {'source': str(source_files[name]), 'source_sha256': digest(source_files[name]),
                        'object': str(obj), 'object_sha256': digest(obj)}
    for name in owned:
        for dependency in graph[name]:
            require(dependency in owned or dependency in resolved,
                    f'Unresolved import {dependency} from {name}')
    paths = [out / 'lib', *roots]
    require(semantics / '.lake/build/lib/lean' not in paths, 'Original build path is forbidden')
    metadata = {'schema': 1, 'identity': 'evm-golf-checked-scanner', 'base_revision': REVISION,
                'original_source_sha256': ORIGINAL_SHA, 'revised_source_sha256': REVISED_SHA,
                'overlay_sha256': OVERLAY_SHA, 'setup_sha256': digest(Path(__file__).resolve()),
                'lake_manifest_sha256': LAKE_MANIFEST_SHA, 'semantics': str(semantics),
                'lean': str(lean), 'lean_sha256': tool_hash, 'lean_version': version,
                'lean_path': ':'.join(map(str, paths)), 'package_revisions': package_revisions,
                'graph': graph, 'excluded_reverse_closure': sorted(reverse),
                'reused_ancestors': reused, 'external_objects': external,
                'timeout_seconds': TIMEOUT}
    return metadata, revised


def expected_files(metadata):
    result = {'manifest.json', 'result.json', 'Semantics.log',
              'source/EvmYul/EVM/Semantics.lean', 'lib/EvmYul/EVM/Semantics.olean'}
    for name in metadata['reused_ancestors']:
        stem = name.replace('.', '/')
        result.update({'source/' + stem + '.lean', 'lib/' + stem + '.olean'})
    return result


def check_output(out, metadata, revised):
    manifest = json.loads((out / 'manifest.json').read_text())
    require(set(manifest) == {'inputs', 'build'}, 'Unexpected setup manifest fields')
    require(manifest['inputs'] == metadata, 'Setup inputs, identity or resolution changed')
    actual = set()
    for path in out.rglob('*'):
        require(not path.is_symlink(), f'Symlink in output: {path}')
        if path.is_file():
            actual.add(str(path.relative_to(out)))
    require(actual == expected_files(metadata), 'Missing or unexpected output files')
    require((out / 'source/EvmYul/EVM/Semantics.lean').read_text() == revised,
            'Revised source changed')
    for name, record in metadata['reused_ancestors'].items():
        stem = name.replace('.', '/')
        require(digest(out / ('source/' + stem + '.lean')) == record['source_sha256'],
                f'Copied source changed: {name}')
        require(digest(out / ('lib/' + stem + '.olean')) == record['object_sha256'],
                f'Copied object changed: {name}')
    result = json.loads((out / 'result.json').read_text())
    require(set(result) == {'module', 'command', 'exit', 'seconds'}, 'Unexpected result fields')
    require(result['module'] == MODULE and type(result['exit']) is int and result['exit'] == 0
            and isinstance(result['seconds'], (int, float)) and 0 <= result['seconds'] < TIMEOUT,
            'No successful bounded build recorded')
    require(result['command'] == build_command(out, Path(metadata['lean'])), 'Unexpected build command')
    expected = {'object_sha256': digest(out / 'lib/EvmYul/EVM/Semantics.olean'),
                'log_sha256': digest(out / 'Semantics.log'),
                'result_sha256': digest(out / 'result.json')}
    require(manifest['build'] == expected, 'Build object, result or log integrity mismatch')
    require(not re.search(r'(^|\n).*error:', (out / 'Semantics.log').read_text()),
            'Compiler errors in accepted log')


def build_command(out, lean):
    return [str(lean), '-o', str(out / 'lib/EvmYul/EVM/Semantics.olean'),
            str(out / 'source/EvmYul/EVM/Semantics.lean')]


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def build(out, metadata, revised):
    out.mkdir(parents=True, exist_ok=False)
    for name, record in metadata['reused_ancestors'].items():
        stem = name.replace('.', '/')
        for key, rel in [('source', 'source/' + stem + '.lean'), ('object', 'lib/' + stem + '.olean')]:
            target = out / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(record[key], target)
    source = out / 'source/EvmYul/EVM/Semantics.lean'
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(revised)
    (out / 'lib/EvmYul/EVM').mkdir(parents=True, exist_ok=True)
    write_json(out / 'manifest.json', {'inputs': metadata, 'build': None})
    env = clean_env()
    env['LEAN_PATH'] = metadata['lean_path']
    cmd = build_command(out, Path(metadata['lean']))
    start = time.monotonic()
    with (out / 'Semantics.log').open('x') as log:
        try:
            code = subprocess.run(cmd, cwd=out / 'source', env=env, stdout=log,
                                  stderr=subprocess.STDOUT, timeout=TIMEOUT).returncode
        except subprocess.TimeoutExpired:
            code = 'timeout45'
    write_json(out / 'result.json', {'module': MODULE, 'command': cmd, 'exit': code,
                                    'seconds': time.monotonic() - start})
    require(code == 0, f'Build failed ({code}); preserved evidence: {out}')
    record = {'object_sha256': digest(out / 'lib/EvmYul/EVM/Semantics.olean'),
              'log_sha256': digest(out / 'Semantics.log'), 'result_sha256': digest(out / 'result.json')}
    write_json(out / 'manifest.json', {'inputs': metadata, 'build': record})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--semantics', required=True, type=Path, help='Clean pinned EVMYulLean checkout')
    parser.add_argument('--lean', required=True, type=Path, help='Installed Lean 4.22.0 bin/lean')
    parser.add_argument('--out', required=True, type=Path, help='Separate fresh output directory')
    parser.add_argument('--check', action='store_true', help='Validate output without compiling')
    args = parser.parse_args()
    require(not args.out.is_symlink(), 'Output must not be a symlink')
    semantics, lean, out = args.semantics.resolve(), args.lean.resolve(), args.out.resolve()
    if args.check:
        require(out.is_dir(), 'Missing checked-scanner output')
    else:
        require(not out.exists(), 'Refusing to overwrite an existing output directory')
    metadata, revised = inventory(semantics, lean, out)
    if not args.check:
        build(out, metadata, revised)
        # Re-read all inputs after compilation to detect changed dependencies.
        fresh, revised = inventory(semantics, lean, out)
        require(fresh == metadata, 'Inputs changed during compilation')
    check_output(out, metadata, revised)
    print(f'Checked scanner {"verified" if args.check else "built and verified"}: {out}')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError,
            subprocess.SubprocessError) as error:
        print(f'checked-scanner: {error}', file=sys.stderr)
        sys.exit(1)
