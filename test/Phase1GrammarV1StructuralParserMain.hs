{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 record declaration fixture parses with exact linear mode"
        (expectFixtureMode "accepted/11-record-explicit-linear-mode.phil" GrammarV1Linear)
    , testIO "SURF-002 data declaration fixture parses with exact affine mode"
        (expectFixtureMode "accepted/12-sum-explicit-affine-mode.phil" GrammarV1Affine)
    , testIO "SURF-002 unrestricted capability fixture parses"
        (expectFixtureMode "accepted/13-capability-unrestricted-mode.phil" GrammarV1Unrestricted)
    , testIO "SURF-002 affine capability fixture parses"
        (expectFixtureMode "accepted/14-capability-affine-mode.phil" GrammarV1Affine)
    , testIO "SURF-002 linear capability fixture parses"
        (expectFixtureMode "accepted/15-capability-linear-mode.phil" GrammarV1Linear)
    , testIO "SURF-003 malformed record mode rejects at syntax"
        (expectFixtureReject "rejected/10-record-mode-missing-literal.phil")
    , testIO "SURF-003 unknown capability mode rejects at syntax"
        (expectFixtureReject "rejected/11-capability-mode-unknown-literal.phil")
    , test "SURF-002 source envelope preserves module imports attributes and fields"
        sourceEnvelopePreserved
    , test "SURF-003 nontrivia trailing token cannot be ignored"
        trailingTokenRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectFixtureMode :: FilePath -> GrammarV1StructuralMode -> IO (Either String ())
expectFixtureMode relativePath expectedMode = do
  parsed <- parseFixture relativePath
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ topLevel] ->
        let actualMode = declarationMode (locatedValue (grammarV1Declaration topLevel))
        in assert (actualMode == Just expectedMode) $
            "expected mode " <> show expectedMode <> ", got " <> show actualMode
      declarations -> Left ("expected exactly one declaration, got " <> show (length declarations))

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

declarationMode :: GrammarV1Declaration -> Maybe GrammarV1StructuralMode
declarationMode declaration = case declaration of
  GrammarV1RecordDeclaration value -> grammarV1RecordMode value
  GrammarV1DataDeclaration value -> grammarV1DataMode value
  GrammarV1CapabilityDeclaration value -> Just (grammarV1CapabilityMode value)

sourceEnvelopePreserved :: Either String ()
sourceEnvelopePreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "envelope" source
  assert (hasModule sourceFile) "module declaration was not preserved"
  assert (length (grammarV1ImportDecls sourceFile) == 2) "expected two import declarations"
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> do
      assert (length (grammarV1Attributes topLevel) == 1) "expected one declaration attribute"
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1RecordDeclaration recordDecl -> do
          assert (grammarV1RecordMode recordDecl == Just GrammarV1Unrestricted)
            "record mode was not preserved"
          assert (length (grammarV1RecordFields recordDecl) == 2)
            "record fields were not preserved"
        other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))
  where
    source = Text.unlines
      [ "module demo.root;"
      , "import dep.alpha;"
      , "import dep.beta { x, y };"
      , "@key(\"decl.demo\")"
      , "record R mode unrestricted {"
      , "  x : U32,"
      , "  y : dep.T,"
      , "}"
      ]

hasModule :: GrammarV1SourceFile -> Bool
hasModule sourceFile = case grammarV1ModuleDecl sourceFile of
  Just _ -> True
  Nothing -> False

trailingTokenRejects :: Either String ()
trailingTokenRejects = case parseGrammarV1StructuralSource "trailing" source of
  Left _ -> Right ()
  Right value -> Left ("expected complete-input rejection, got " <> show value)
  where
    source = "module demo; record R {} stray"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
