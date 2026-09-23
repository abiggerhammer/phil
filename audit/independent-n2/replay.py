#!/usr/bin/env python3
"""Independent CI wrapper. Executes the unchanged published N2 Haskell driver."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

DRIVER_SHA256 = '5a51b92fcc6ba43d4f124db709fe91437ed19ea6d527163c60035b8442ca5936'

def classify(text, code, prefix, count):
    expected = [f'{prefix}{i:02d}' for i in range(1, count + 1)]
    seen, done, unexpected = {}, [], []
    for line in text.splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r'N2_(PASS|FAIL|ERROR) ([CO]\d{2})(?: (.*))?', line)
        if match:
            status, key, detail = match.groups()
            if key in seen or key not in expected:
                unexpected.append(line)
            seen[key] = {'status': status, 'detail': detail}
        elif re.fullmatch(r'N2_DONE \d+', line):
            done.append(int(line.split()[1]))
        else:
            unexpected.append(line)
    valid = not unexpected and set(seen) == set(expected) and done == [count]
    passed = valid and code == 0 and all(x['status'] == 'PASS' for x in seen.values())
    return {'passed': passed, 'protocol_complete': valid, 'returncode': code,
            'groups': seen, 'unexpected': unexpected, 'completion': done}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--sha', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    driver = Path(__file__).resolve().with_name('IntegerN2Controls.hs')
    result = {'subject_requested': args.sha, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'stages': []}
    def invoke(command):
        return subprocess.run(command, cwd=repo, text=True, capture_output=True, timeout=600)
    try:
        if not re.fullmatch(r'[0-9a-f]{40}', args.sha):
            raise RuntimeError('full subject SHA required')
        result['head_before'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
        if result['head_before'] != args.sha or subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=repo, text=True).strip():
            raise RuntimeError('subject is not the requested clean checkout')
        result['driver_sha256'] = hashlib.sha256(driver.read_bytes()).hexdigest()
        if result['driver_sha256'] != DRIVER_SHA256:
            raise RuntimeError('published Haskell bytes changed')
        (out / 'IntegerN2Controls.hs').write_bytes(driver.read_bytes())
        result['versions'] = {tool: invoke([tool, '--version']).stdout for tool in ['ghc', 'cabal', 'git']}
        with tempfile.TemporaryDirectory(prefix='phil-independent-n2-') as temp:
            exe = str(Path(temp) / 'integer-n2')
            command = ['cabal', 'exec', '--', 'ghc', '-O0', '-Wall', '-Werror', '-isrc', '-outputdir', temp, '-o', exe, str(driver)]
            built = invoke(command)
            (out / 'compile.stdout').write_text(built.stdout)
            (out / 'compile.stderr').write_text(built.stderr)
            result['stages'].append({'name': 'compile', 'command': command, 'returncode': built.returncode})
            if built.returncode:
                result['status'] = 'compile_or_dependency_error'
                return 2
            for name, extra, prefix, count in [('controls', [], 'C', 38), ('observations', ['--observations'], 'O', 2)]:
                run = invoke([exe] + extra)
                (out / (name + '.stdout')).write_text(run.stdout)
                (out / (name + '.stderr')).write_text(run.stderr)
                print(run.stdout, end='')
                stage = classify(run.stdout, run.returncode, prefix, count)
                stage['name'] = name
                result['stages'].append(stage)
        result['head_after'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
        if result['head_after'] != args.sha or subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=repo, text=True).strip():
            raise RuntimeError('subject changed during replay')
        good = all(s.get('passed') for s in result['stages'][1:])
        result['status'] = 'replay_completed' if good else 'replay_requires_review'
        return 0 if good else 1
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        result['status'] = 'infrastructure_error'
        result['error'] = str(error)
        return 2
    finally:
        (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')

if __name__ == '__main__':
    sys.exit(main())
