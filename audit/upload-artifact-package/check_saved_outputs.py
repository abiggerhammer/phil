#!/usr/bin/env python3
"""Bounded checks of Phil's own package/emitter orchestration.

The real package script runs first, unchanged. This script compares its saved
bytes with independently rendered certified objects and with its regenerated
smoke inputs, then assembles/links/runs the saved bytes under the same explicit
smoke shim. LLVM is a trusted execution dependency, not an audit target.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Callable


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_record(command: list[str], cwd: Path, prefix: Path) -> subprocess.CompletedProcess[bytes]:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix('.command.json').write_text(json.dumps(command) + '\n')
    completed = subprocess.run(command, cwd=cwd, capture_output=True, timeout=120, check=False)
    prefix.with_suffix('.stdout').write_bytes(completed.stdout)
    prefix.with_suffix('.stderr').write_bytes(completed.stderr)
    prefix.with_suffix('.exit').write_text(str(completed.returncode) + '\n')
    return completed


def main() -> int:
    if len(sys.argv) != 3:
        raise ValueError('usage: check_saved_outputs.py SUBJECT EVIDENCE')
    subject, evidence = (Path(value).resolve() for value in sys.argv[1:])
    expected = evidence / 'expected'
    saved = subject / 'dist/int005-certified-release'
    smoke = Path(os.environ['RUNNER_TEMP']) / 'phil-int005-native-release'
    emitter = evidence / 'emitter'
    as_tool, link_tool, clang = (os.environ[name] for name in ('LLVM_AS', 'LLVM_LINK', 'CLANG'))
    results: list[dict[str, str]] = []
    identities: dict[str, object] = {}
    required = [emitter]
    for name in ('upload', 'steve'):
        required += [expected / f'{name}.ll', expected / f'{name}.release-package',
                     saved / f'{name}.ll', saved / f'{name}.release-package',
                     smoke / f'{name}.ll', smoke / f'{name}-runtime-shim.bc',
                     smoke / f'{name}-launcher.bc', smoke / f'{name}-launcher.ll']
    for path in required:
        if not path.is_file() or not path.stat().st_size:
            raise RuntimeError(f'missing/nonempty prerequisite: {path}')

    def check(key: str, label: str, action: Callable[[], None]) -> None:
        try:
            action()
        except AssertionError as error:
            results.append({'id': key, 'result': 'FAIL', 'label': label, 'detail': str(error)})
            print(f'FAIL {key} {label} -- {error}')
        else:
            results.append({'id': key, 'result': 'PASS', 'label': label})
            print(f'PASS {key} {label}')

    def exact_saved(name: str) -> None:
        for suffix in ('.ll', '.release-package'):
            wanted, actual = expected / (name + suffix), saved / (name + suffix)
            assert wanted.read_bytes() == actual.read_bytes(), f'{name}{suffix}: saved output changed'
        identities[name] = {'saved_llvm_sha256': sha256(saved / f'{name}.ll'),
                            'saved_sidecar_sha256': sha256(saved / f'{name}.release-package'),
                            'expected_llvm_sha256': sha256(expected / f'{name}.ll')}

    def same_smoke(name: str) -> None:
        assert (saved / f'{name}.ll').read_bytes() == (smoke / f'{name}.ll').read_bytes(), name
        identities[name]['regenerated_smoke_sha256'] = sha256(smoke / f'{name}.ll')  # type: ignore[index]

    def source_rejects() -> None:
        root = evidence / 'bad-source'
        target = root / 'examples/upload'
        target.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(subject / 'examples/upload/server.phil', target / 'server.phil')
        (target / 'client.phil').write_text('component {\n')
        result = run_record([str(emitter), 'upload'], root, evidence / 'commands/bad-source')
        assert result.returncode == 1, f'unexpected exit {result.returncode}'
        assert result.stdout == b'', 'source rejection emitted stdout artifact bytes'
        assert result.stderr.startswith(b'Upload real manifest fixture failed:'), result.stderr.decode(errors='replace')

    def usage_rejects() -> None:
        result = run_record([str(emitter), 'unsupported-audit-witness'], subject, evidence / 'commands/usage')
        assert result.returncode == 1 and result.stdout == b'', 'invalid selector emitted artifact bytes'
        assert result.stderr == b'usage: Phase1INT005EmitCertifiedReleaseMain.hs <upload|steve>\n'

    def execute_saved(name: str) -> None:
        output = evidence / 'saved-execution'
        output.mkdir(exist_ok=True)
        raw = saved / f'{name}.ll'
        before = sha256(raw)
        bc, linked, binary = (output / f'{name}{suffix}' for suffix in ('.bc', '-linked.bc', '-smoke'))
        commands = [
            [as_tool, str(raw), '-o', str(bc)],
            [link_tool, str(bc), str(smoke / f'{name}-runtime-shim.bc'),
             str(smoke / f'{name}-launcher.bc'), '-o', str(linked)],
            [clang, '--target=x86_64-unknown-linux-gnu', str(linked), '-o', str(binary)],
            ['timeout', '10s', str(binary)],
        ]
        for index, command in enumerate(commands):
            outcome = run_record(command, subject, evidence / f'commands/{name}-saved-{index}')
            assert outcome.returncode == 0, f'saved artifact step {index} failed: {outcome.returncode}'
        assert before == sha256(raw), 'saved input was modified during its check'
        launcher = (smoke / f'{name}-launcher.ll').read_text()
        functions = re.findall(r'^define i32 @([^ (]+)\(\) \{$', raw.read_text(), re.MULTILINE)
        calls = re.findall(r'^  %result\d+ = call i32 @([^ (]+)\(\)$', launcher, re.MULTILINE)
        assert functions and calls == functions, 'launcher did not invoke the exact supplied function list'
        identities[name]['saved_executable_sha256'] = sha256(binary)  # type: ignore[index]
        identities[name]['saved_input_sha256_at_execution'] = before  # type: ignore[index]
        identities[name]['function_count'] = len(functions)  # type: ignore[index]
        # The actual supplied smoke launcher discards function return statuses.
        # A successful process exit below receives invocation-smoke credit only.
        assert '  ret i32 0\n' in launcher, 'launcher contract changed; review it before interpreting output'

    check('B01', 'Upload saved text and sidecar match exact certified-object rendering', lambda: exact_saved('upload'))
    check('B02', 'Steve saved text and sidecar match exact certified-object rendering', lambda: exact_saved('steve'))
    check('B03', 'Upload saved and regenerated smoke inputs are byte-identical', lambda: same_smoke('upload'))
    check('B04', 'Steve saved and regenerated smoke inputs are byte-identical', lambda: same_smoke('steve'))
    check('B05', 'actual emitter source rejection produces no LLVM stdout', source_rejects)
    check('B06', 'actual emitter rejects an unsupported witness selector', usage_rejects)
    check('B07', 'exact saved Upload bytes assemble link and run under the smoke shim', lambda: execute_saved('upload'))
    check('B08', 'exact saved Steve bytes assemble link and run under the smoke shim', lambda: execute_saved('steve'))
    report = {'cases': results, 'identities': identities,
              'all_required_passed': all(row['result'] == 'PASS' for row in results),
              'native_invocation_smoke_only': True, 'witness_return_statuses_asserted': False,
              'general_source_to_stage_reflection_established': False, 'release_certified': False}
    (evidence / 'saved-output-protocol.json').write_text(json.dumps(report, indent=2) + '\n')
    print('COMPLETE saved_output_groups=8')
    return 0 if report['all_required_passed'] else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f'SETUP_ERROR {error}', file=sys.stderr)
        sys.exit(2)
