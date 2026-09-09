#!/usr/bin/env python3
from pathlib import Path

path = Path("test/Phase1INT004PortableGenericInstantiationNegativeMain.hs")
text = path.read_text()

old_import = "import Data.Set (Set)\n"
if old_import in text:
    text = text.replace(old_import, "", 1)

old_helper = '''groupRows :: Ord k => (a -> k) -> [a] -> Map k [a]\ngroupRows key = Map.fromListWith (++) . map (\\value -> (key value, [value]))\n\n'''
if old_helper in text:
    text = text.replace(old_helper, "", 1)

path.write_text(text)
print("removed unused Set import and groupRows helper")
