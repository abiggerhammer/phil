from pathlib import Path

path = Path('test/Phase1INT004PortableCallableStructuralModeNegativeMain.hs')
text = path.read_text()
needle = 'import Data.Map.Strict (Map)\n'
if text.count(needle) != 1:
    raise SystemExit('expected exactly one redundant Data.Map.Strict (Map) import')
path.write_text(text.replace(needle, '', 1))
