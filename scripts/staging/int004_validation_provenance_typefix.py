from pathlib import Path

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()

old = '''  where
    materializeRequirement requirement = do
'''
new = '''  where
    materializeRequirement
      :: PortableEnvironmentRequirement
      -> Either Text (Text, Text, Proposition)
    materializeRequirement requirement = do
'''

if new in text:
    raise SystemExit(0)
count = text.count(old)
if count != 1:
    raise SystemExit(f"expected exactly one materializeRequirement site, found {count}")
path.write_text(text.replace(old, new, 1))
