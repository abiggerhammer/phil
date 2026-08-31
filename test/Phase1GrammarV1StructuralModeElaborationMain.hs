{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Syntax (Mode (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1StructuralMode)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-008 record linear mode routes exactly"
        (expectFixtureMode "accepted/11-record-explicit-linear-mode.phil" (Just Linear))
    , testIO "SURF-008 data affine mode routes exactly"
        (expectFixtureMode "accepted/12-sum-explicit-affine-mode.phil" (Just Affine))
    , testIO "SURF-008 capability unrestricted mode routes exactly"
        (expectFixtureMode "accepted/13-capability-unrestricted-mode.phil" (Just Unrestricted))
    , test "SURF-008 omitted record mode remains omitted before semantic derivation"
        omittedRecordModeRemainsAbsent
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectFixtureMode :: FilePath -> Maybe Mode -> IO (Either String ())
expectFixtureMode relativePath expected = do
  source <- TextIO.readFile ("test/fixtures/phase1-surface/" <> relativePath)
  pure $ do
    parsed <- mapLeft show $ parseGrammarV1StructuralSource (Text.pack relativePath) source
    actual <- exactlyOneMode parsed
    assert (actual == expected)
      ("expected semantic mode " <> show expected <> ", got " <> show actual)

omittedRecordModeRemainsAbsent :: Either String ()
omittedRecordModeRemainsAbsent = do
  parsed <- mapLeft show $ parseGrammarV1StructuralSource "omitted-mode"
    "record Plain { value : U32 }"
  actual <- exactlyOneMode parsed
  assert (actual == Nothing)
    ("omitted record mode was defaulted during source elaboration: " <> show actual)

exactlyOneMode :: GrammarV1SourceFile -> Either String (Maybe Mode)
exactlyOneMode sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1RecordDeclaration declaration ->
          Right (grammarV1StructuralMode <$> grammarV1RecordMode declaration)
        GrammarV1DataDeclaration declaration ->
          Right (grammarV1StructuralMode <$> grammarV1DataMode declaration)
        GrammarV1CapabilityDeclaration declaration ->
          Right (Just (grammarV1StructuralMode (grammarV1CapabilityMode declaration)))
        other -> Left ("expected mode-bearing declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
