#!/usr/bin/env bash
set -euo pipefail

PHIL_LLVM18_TOOLS="llvm-as llvm-link clang"
source scripts/ci/resolve-llvm18.sh
unset PHIL_LLVM18_TOOLS

WORKDIR="${RUNNER_TEMP:-/tmp}/phil-int005-native-release"
rm -rf "$WORKDIR"
mkdir -p "$WORKDIR"

for witness in upload steve; do
  llvm="$WORKDIR/${witness}.ll"
  bitcode="$WORKDIR/${witness}.bc"
  shim="$WORKDIR/${witness}-runtime-shim.ll"
  shim_bc="$WORKDIR/${witness}-runtime-shim.bc"
  launcher="$WORKDIR/${witness}-launcher.ll"
  launcher_bc="$WORKDIR/${witness}-launcher.bc"
  linked="$WORKDIR/${witness}-linked.bc"
  executable="$WORKDIR/${witness}-release-smoke"

  cabal exec -- runghc -isrc -itest -Wall -Werror \
    test/Phase1INT005EmitCertifiedReleaseMain.hs "$witness" > "$llvm"

  "$LLVM_AS" "$llvm" -o "$bitcode"

  python3 - "$llvm" "$shim" "$launcher" <<'PY'
import re
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text().splitlines()
shim_path = Path(sys.argv[2])
launcher_path = Path(sys.argv[3])

declare_re = re.compile(r'^declare (void|i1) @([A-Za-z_.$][A-Za-z0-9_.$]*)\(\)$')
define_re = re.compile(r'^define i32 @([A-Za-z_.$][A-Za-z0-9_.$]*)\(\) \{$')

declarations = {}
functions = []

for line in source:
    stripped = line.strip()
    if stripped.startswith('declare '):
        match = declare_re.fullmatch(stripped)
        if not match:
            raise SystemExit(f'unsupported INT-005 conservative runtime declaration: {stripped}')
        result_type, name = match.groups()
        previous = declarations.get(name)
        if previous is not None and previous != result_type:
            raise SystemExit(f'conflicting declaration for {name}: {previous} vs {result_type}')
        declarations[name] = result_type
    elif stripped.startswith('define '):
        match = define_re.fullmatch(stripped)
        if not match:
            raise SystemExit(f'unsupported INT-005 witness function signature: {stripped}')
        functions.append(match.group(1))

if not functions:
    raise SystemExit('certified witness LLVM defines no runnable functions')

shim_lines = [
    '; INT-005 deterministic smoke runtime: separate from certified witness artifact',
    'target triple = "x86_64-unknown-linux-gnu"',
    '',
]
for name, result_type in sorted(declarations.items()):
    shim_lines.append(f'define {result_type} @{name}() {{')
    shim_lines.append('entry:')
    if result_type == 'void':
        shim_lines.append('  ret void')
    else:
        shim_lines.append('  ret i1 false')
    shim_lines.append('}')
    shim_lines.append('')
shim_path.write_text('\n'.join(shim_lines))

launcher_lines = [
    '; INT-005 native witness launcher: links beside the exact certified artifact',
    'target triple = "x86_64-unknown-linux-gnu"',
    '',
]
for name in functions:
    launcher_lines.append(f'declare i32 @{name}()')
launcher_lines.extend(['', 'define i32 @main() {', 'entry:'])
for index, name in enumerate(functions):
    launcher_lines.append(f'  %result{index} = call i32 @{name}()')
launcher_lines.extend(['  ret i32 0', '}', ''])
launcher_path.write_text('\n'.join(launcher_lines))
PY

  "$LLVM_AS" "$shim" -o "$shim_bc"
  "$LLVM_AS" "$launcher" -o "$launcher_bc"
  "$LLVM_LINK" "$bitcode" "$shim_bc" "$launcher_bc" -o "$linked"
  "$CLANG" --target=x86_64-unknown-linux-gnu "$linked" -o "$executable"
  timeout 10s "$executable"

  echo "PASS: INT-005 ${witness} exact certified LLVM assembled, linked, and executed natively"
done

"$LLVM_AS" --version | head -n 1
"$CLANG" --version | head -n 1
