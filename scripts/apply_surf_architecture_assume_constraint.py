from pathlib import Path

path = Path("src/Phil/Surface/GrammarV1/Parser.hs")
text = path.read_text()

old_ast = '''  | GrammarV1ArchitectureObservable
      (Located GrammarV1QualifiedName)
  deriving (Eq, Show)
'''
new_ast = '''  | GrammarV1ArchitectureObservable
      (Located GrammarV1QualifiedName)
  | GrammarV1ArchitectureAssume
      (Located GrammarV1Proposition)
      (Located GrammarV1QualifiedName)
  | GrammarV1ArchitectureConstraint
      (Located GrammarV1Proposition)
  deriving (Eq, Show)
'''

old_parser = '''    Just (GrammarKeyword "observable") -> do
      start <- expectKeyword "observable"
      target <- parseQualifiedName
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1ArchitectureObservable target)
    Just other -> failParser $
'''
new_parser = '''    Just (GrammarKeyword "observable") -> do
      start <- expectKeyword "observable"
      target <- parseQualifiedName
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1ArchitectureObservable target)
    Just (GrammarKeyword "assume") -> do
      start <- expectKeyword "assume"
      proposition <- parseProposition
      _ <- expectKeyword "within"
      scope <- parseQualifiedName
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1ArchitectureAssume proposition scope)
    Just (GrammarKeyword "constraint") -> do
      start <- expectKeyword "constraint"
      proposition <- parseProposition
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1ArchitectureConstraint proposition)
    Just other -> failParser $
'''

for label, old, new in [
    ("architecture AST", old_ast, new_ast),
    ("architecture parser", old_parser, new_parser),
]:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one {label} anchor, found {count}")
    text = text.replace(old, new, 1)

path.write_text(text)
