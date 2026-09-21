{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List (nub)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler
  ( RunnableProgram (..)
  , compileRunnable
  )
import Phil.LLVM.IR (LLVMArtifact (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "R1 source and synthetic scalar names remain distinct after LLVM rendering" sourceSyntheticCollision
    , test "R1 source scalar and entry block names occupy distinct LLVM namespaces" valueBlockCollision
    , test "R1 apostrophe and underscore source names remain distinct" apostropheUnderscoreDistinct
    , test "R1 accepted Latin-1 source name renders as ASCII LLVM identity" unicodeCafeLegal
    , test "R1 accepted Greek source name renders as ASCII LLVM identity" unicodeAlphaLegal
    , test "R1 escape-looking source spelling cannot imitate an encoded character" escapePrefixLookingDistinct
    , test "R1 source name cannot collide with generated return temporary" generatedTemporaryDistinct
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sourceSyntheticCollision :: Either String ()
sourceSyntheticCollision = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let return_value_0 = 1"
    , "  return 2"
    , "}"
    ]
  assertContains "%source_value_return__value__0 = add i32 0, 1" rendered
  assertContains "%synthetic_return_value_0 = add i32 0, 2" rendered
  assertUniqueDefinitions rendered

valueBlockCollision :: Either String ()
valueBlockCollision = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let entry = 42"
    , "  return entry"
    , "}"
    ]
  assertContains "block_entry:" rendered
  assertContains "%source_value_entry = add i32 0, 42" rendered
  assert (not (Text.isInfixOf "\nentry:\n" rendered))
    "raw source spelling still occupied the LLVM block-label namespace"
  assertUniqueDefinitions rendered

apostropheUnderscoreDistinct :: Either String ()
apostropheUnderscoreDistinct = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let x' = 1"
    , "  let x_ = 2"
    , "  return x_"
    , "}"
    ]
  assertContains "%source_value_x_u39_ = add i32 0, 1" rendered
  assertContains "%source_value_x__ = add i32 0, 2" rendered
  assertContains "ret i32 %source_value_x__" rendered
  assert (not (Text.isInfixOf "%source_value_x_ = add" rendered))
    "lossy apostrophe/underscore spelling returned"
  assertUniqueDefinitions rendered

unicodeCafeLegal :: Either String ()
unicodeCafeLegal = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let café = 7"
    , "  return café"
    , "}"
    ]
  assertContains "%source_value_caf_u233_ = add i32 0, 7" rendered
  assertContains "ret i32 %source_value_caf_u233_" rendered
  assert (not (Text.isInfixOf "café" rendered))
    "raw non-ASCII source spelling escaped into unquoted LLVM"
  assertASCIIIdentityDefinitions rendered

unicodeAlphaLegal :: Either String ()
unicodeAlphaLegal = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let α = 9"
    , "  return α"
    , "}"
    ]
  assertContains "%source_value__u945_ = add i32 0, 9" rendered
  assertContains "ret i32 %source_value__u945_" rendered
  assert (not (Text.isInfixOf "α" rendered))
    "raw Greek source spelling escaped into unquoted LLVM"
  assertASCIIIdentityDefinitions rendered

escapePrefixLookingDistinct :: Either String ()
escapePrefixLookingDistinct = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let x' = 1"
    , "  let x_u39_ = 2"
    , "  return x_u39_"
    , "}"
    ]
  assertContains "%source_value_x_u39_ = add i32 0, 1" rendered
  assertContains "%source_value_x__u39__ = add i32 0, 2" rendered
  assertContains "ret i32 %source_value_x__u39__" rendered
  assertUniqueDefinitions rendered

generatedTemporaryDistinct :: Either String ()
generatedTemporaryDistinct = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let synthetic_return_value_0 = 4"
    , "  return 5"
    , "}"
    ]
  assertContains "%source_value_synthetic__return__value__0 = add i32 0, 4" rendered
  assertContains "%synthetic_return_value_0 = add i32 0, 5" rendered
  assertUniqueDefinitions rendered

compileText :: Text -> Either String Text
compileText source =
  case compileRunnable "review-r1.phil" source of
    Left err -> Left ("compileRunnable rejected R1 regression source: " <> show err)
    Right runnable -> Right (llvmArtifactText (runnableLLVMArtifact runnable))

assertUniqueDefinitions :: Text -> Either String ()
assertUniqueDefinitions rendered =
  let names = definitionNames rendered
  in assert (length names == length (nub names))
      ("duplicate rendered LLVM local definition: " <> show names)

assertASCIIIdentityDefinitions :: Text -> Either String ()
assertASCIIIdentityDefinitions rendered = do
  assertUniqueDefinitions rendered
  let names = definitionNames rendered
  assert (all (Text.all (\character -> fromEnum character < 128)) names)
    ("non-ASCII rendered LLVM local definition: " <> show names)

definitionNames :: Text -> [Text]
definitionNames rendered = concatMap one (Text.lines rendered)
  where
    one line =
      let stripped = Text.strip line
      in case Text.stripPrefix "%" stripped of
          Just rest ->
            let (name, suffix) = Text.breakOn " = " rest
            in if Text.null suffix then [] else [name]
          Nothing
            | Text.isSuffixOf ":" stripped ->
                let name = Text.dropEnd 1 stripped
                in if Text.null name then [] else [name]
            | otherwise -> []

assertContains :: Text -> Text -> Either String ()
assertContains needle haystack =
  assert (Text.isInfixOf needle haystack)
    ("missing rendered LLVM fragment: " <> Text.unpack needle)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail
