#!/usr/bin/env python3
"""Exact-source replay. Preparing this runner does not execute Phil.

Requires an existing clean checkout and the project's GHC/Cabal toolchain.
Writes inputs/results outside the source checkout. Never changes source files.
"""
from __future__ import annotations
import argparse
import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

PIN = 'e47e31e47b33abd7c55242bad6b9c61cd104d9d0'
KEYS = [f'G{i:02}' for i in range(1,5)] + [f'D{i:02}' for i in range(1,5)] + [f'F{i:02}' for i in range(1,6)] + [f'N{i:02}' for i in range(1,6)] + ['A01','A02']
FIXTURES = {
    'CatalogFixture': ('test/Phase1CALL019CallableResolutionMain.hs', '0caf0051f09004e6bc5f7bb493ab18b365f564df'),
    'FunctionFixture': ('test/Phase1GrammarV1FunctionHeaderMain.hs', '89900e9e97315c31e7fd69dd12afc02e2446e971'),
    'GenericFixture': ('test/Phase1GrammarV1GenericRequirementElaborationMain.hs', 'afc2ddd8b0df881888c39603a7c33a6eafbad1bf'),
}
PERMANENT_LABEL_COUNTS = {'CatalogFixture': 17, 'FunctionFixture': 18, 'GenericFixture': 11}
SOURCES = [
    'src/Phil/Compiler/SourceBundle.hs', 'src/Phil/Compiler/CallableInvocation.hs',
    'src/Phil/Compiler/CallableSurfaceSemantics.hs', 'src/Phil/Compiler/CallableInvocationSemantics.hs',
    'src/Phil/Compiler/CallableInvocationContext.hs', 'src/Phil/Surface/Check.hs',
    'src/Phil/Surface/Check/Preflight.hs', 'src/Phil/Surface/Check/Engine.hs',
    'src/Phil/Surface/Check/Types.hs', 'src/Phil/Surface/GrammarV1/GenericBinderScope.hs',
    'src/Phil/Surface/GrammarV1/SpecializedStaticReference.hs', 'src/Phil/Surface/GrammarV1/GenericDischarge.hs',
    'src/Phil/Surface/GrammarV1/GenericRequirementCore.hs', 'src/Phil/Surface/GrammarV1/CallableSignature.hs',
    'src/Phil/Surface/GrammarV1/FunctionBodySurface.hs', 'src/Phil/Core/Generic.hs',
    'src/Phil/Core/Generic/StaticActual.hs', 'src/Phil/Core/EffectPolymorphism.hs',
    'src/Phil/IO/Console.hs', 'src/Phil/Examples/Steve/ApplicationShell.hs',
    'docs/phase-1/callable-invocation-proof-boundary-v1.md',
]

def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def protocol(text: str, exit_code: int) -> dict:
    rows = []
    for line in text.splitlines():
        if line.startswith('CASE '):
            match = re.fullmatch(r'CASE (\S+) (PASS|FAIL|HARNESS)(?: (.*))?', line)
            if match is None:
                raise ValueError(f'malformed case record: {line!r}')
            rows.append({'id': match[1], 'status': match[2], 'detail': match[3]})
    if [row['id'] for row in rows] != KEYS:
        raise ValueError('missing, duplicated, extra or out-of-order case IDs')
    if text.splitlines().count('COMPLETE source_connection_groups=20') != 1:
        raise ValueError('missing or repeated completion marker')
    predicted = 2 if any(r['status']=='HARNESS' for r in rows) else (1 if any(r['status']=='FAIL' for r in rows) else 0)
    if exit_code != predicted:
        raise ValueError(f'case/exit disagreement: {predicted} != {exit_code}')
    return {'cases': rows, 'exit': exit_code, 'all_required_pass': exit_code == 0,
            'source_to_signature_production_exporter_established': False,
            'dependent_generic_requirement_instantiation_established': False,
            'native_application_executed': False, 'release_certified': False}

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--subject', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--preflight-only', action='store_true')
    args = parser.parse_args()
    subject, output = args.subject.resolve(), args.output.resolve()
    if output == subject or subject in output.parents:
        parser.error('evidence output must be outside the subject checkout')
    if output.exists() and any(output.iterdir()):
        parser.error('output must be new or empty; preserve older attempts')
    output.mkdir(parents=True, exist_ok=True)
    missing = [name for name in ('git', 'ghc', 'cabal') if shutil.which(name) is None]
    preflight = {'requested_subject': str(subject), 'pin': PIN, 'missing_tools': missing,
                 'semantic_execution_started': False, 'preflight_only': args.preflight_only,
                 'workflow_commit': os.environ.get('GITHUB_SHA'),
                 'workflow_run_id': os.environ.get('GITHUB_RUN_ID'),
                 'workflow_run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT')}
    (output/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
    if missing:
        print('SETUP: missing tools: '+', '.join(missing), file=sys.stderr)
        return 2
    def capture(cmd: list[str], label: str, timeout: int=120, required: bool=True) -> subprocess.CompletedProcess:
        (output/(label+'.command.json')).write_text(json.dumps(cmd)+'\n')
        try:
            result = subprocess.run(cmd, cwd=subject, capture_output=True, timeout=timeout, check=False)
        except subprocess.TimeoutExpired as err:
            (output/(label+'.stdout')).write_bytes(err.stdout or b'')
            (output/(label+'.stderr')).write_bytes(err.stderr or b'')
            (output/(label+'.timeout')).write_text(str(timeout)+'\n')
            raise RuntimeError(f'{label} timed out; not semantic rejection') from err
        (output/(label+'.stdout')).write_bytes(result.stdout)
        (output/(label+'.stderr')).write_bytes(result.stderr)
        (output/(label+'.exit')).write_text(str(result.returncode)+'\n')
        if required and result.returncode:
            raise RuntimeError(f'{label} exited {result.returncode}; inspect retained log')
        return result
    def clean(label: str) -> None:
        head = capture(['git','rev-parse','HEAD'],label+'-head').stdout.decode().strip()
        status = capture(['git','status','--porcelain','--untracked-files=all'],label+'-status').stdout
        if head != PIN or status:
            raise RuntimeError(f'{label}: source HEAD differs or source is not clean')
    exit_code = 2
    try:
        clean('before')
        for tool, expected in [('ghc','9.6.7'), ('cabal','3.18.1.0')]:
            version = capture([tool,'--numeric-version'],tool+'-version').stdout.decode().strip()
            if version != expected:
                raise RuntimeError(f'{tool}: expected {expected}, got {version}')
        shutil.copyfile(Path(__file__), output/'replay-runner.py')
        drivers = output/'drivers'
        drivers.mkdir()
        original = Path(__file__).resolve().parent/'controls/SourceConnectionReview.hs'
        shutil.copyfile(original, drivers/original.name)
        (output/'driver-identity.json').write_text(json.dumps({
            'git_blob': git_blob(original.read_bytes()),
            'sha256': hashlib.sha256(original.read_bytes()).hexdigest(),
            'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'production_pin': PIN, 'required_group_ids': KEYS}, indent=2)+'\n')
        fixture_manifest = {}
        for module,(path,blob) in FIXTURES.items():
            raw = (subject/path).read_bytes()
            if git_blob(raw) != blob:
                raise RuntimeError(f'fixture identity changed: {path}')
            before = raw.decode('utf-8')
            needle = 'module Main (main) where'
            if before.count(needle) != 1:
                raise RuntimeError(f'non-unique fixture module header: {path}')
            after = before.replace(needle, f'module {module} where')
            (drivers/(module+'.original.hs')).write_bytes(raw)
            (drivers/(module+'.hs')).write_text(after)
            (drivers/(module+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile=path,tofile=module+'.hs')))
            fixture_manifest[module] = {'source':path,'original_git_blob':blob,
                'adapted_sha256':hashlib.sha256(after.encode()).hexdigest(),'change':'module/export declaration only'}
        (output/'fixtures.json').write_text(json.dumps(fixture_manifest,indent=2)+'\n')
        source_manifest = {}
        for path in SOURCES:
            data = (subject/path).read_bytes()
            stored = output/'source'/path
            stored.parent.mkdir(parents=True,exist_ok=True)
            stored.write_bytes(data)
            source_manifest[path] = {'git_blob':git_blob(data),'sha256':hashlib.sha256(data).hexdigest()}
        (output/'sources.json').write_text(json.dumps(source_manifest,indent=2)+'\n')
        if args.preflight_only:
            clean('after')
            (output/'status.json').write_text(json.dumps({'status':'preflight_only','semantic_cases_executed':0})+'\n')
            exit_code = 0
        else:
            capture(['cabal','update'],'cabal-update',600)
            capture(['cabal','build','all','--enable-tests'],'build',1800)
            plan = subject/'dist-newstyle/cache/plan.json'
            if plan.exists():
                shutil.copyfile(plan,output/'cabal-plan.json')
            build_dir = output/'build-driver'
            build_dir.mkdir()
            exe = output/'SourceConnectionReview'
            capture(['cabal','exec','--','ghc','-O0','-Wall','-Werror','-isrc','-i'+str(drivers),
                     '-outputdir',str(build_dir),str(drivers/original.name),'-o',str(exe)],'compile',1200)
            (output/'execution-state.json').write_text(json.dumps({
                'independent_driver_started': True, 'production_pin': PIN})+'\n')
            run = capture([str(exe)],'requirements',300,required=False)
            result = protocol(run.stdout.decode('utf-8'),run.returncode)
            (output/'protocol.json').write_text(json.dumps(result,indent=2)+'\n')
            permanent = []
            for module,(path,_) in FIXTURES.items():
                replay = capture(['cabal','exec','--','runghc','-isrc','-Wall','-Werror',path],
                                 'permanent-'+module,600,required=False)
                lines = replay.stdout.decode('utf-8').splitlines()
                passing = [line for line in lines if line.startswith('PASS: ')]
                failing = [line for line in lines if line.startswith('FAIL: ')]
                label_domain_complete = len(passing) + len(failing) == PERMANENT_LABEL_COUNTS[module]
                permanent.append({'source':path,'exit':replay.returncode,
                    'passing_labels':passing, 'failing_labels':failing,
                    'expected_label_count':PERMANENT_LABEL_COUNTS[module],
                    'complete_label_inventory':label_domain_complete})
            (output/'permanent.json').write_text(json.dumps(permanent,indent=2)+'\n')
            clean('after')
            if run.returncode == 2 or any(not p['complete_label_inventory'] for p in permanent):
                exit_code = 2
            elif result['all_required_pass'] and all(p['exit']==0 and not p['failing_labels'] for p in permanent):
                exit_code = 0
            else:
                exit_code = 1
    except (OSError, UnicodeError, ValueError, RuntimeError) as error:
        (output/'runner-error.txt').write_text(str(error)+'\n')
        print('SETUP/PROTOCOL: '+str(error),file=sys.stderr)
    finally:
        # The emitted executable/object files are not part of the public evidence
        # seal. All original source/commands/raw text/results are included.
        inventory = {}
        for p in sorted(output.rglob('*')):
            if not p.is_file() or p.name == 'payload-sha256.json' or 'build-driver' in p.parts or p.name == 'SourceConnectionReview':
                continue
            inventory[p.relative_to(output).as_posix()] = hashlib.sha256(p.read_bytes()).hexdigest()
        (output/'payload-sha256.json').write_text(json.dumps(inventory,indent=2)+'\n')
    return exit_code

if __name__ == '__main__':
    sys.exit(main())
