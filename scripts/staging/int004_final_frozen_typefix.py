#!/usr/bin/env python3
from pathlib import Path

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()
old = "_ <- traverse (validateNodeReference sessionId nodeMap) nodes"
new = "_ <- traverse (validateNodeReference sessionId) nodes"

if new in text:
    print("INT-004 final frozen typecheck repair already applied")
elif old in text:
    path.write_text(text.replace(old, new, 1))
    print("applied INT-004 final frozen typecheck repair")
else:
    raise SystemExit("missing INT-004 final frozen typecheck repair anchor")
