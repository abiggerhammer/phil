{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List (nub)
import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax (Name (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , grammarV1BinderCoreName
  , grammarV1DecodeBinderCoreName
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "FSEM-01 actual Text encoder roundtrips every admitted sample"
        allSampleKeysRoundtrip
    , test "FSEM-01 exact generated names distinguish root/ordinal pairs"
        sampleKeysDoNotCollide
    , test "FSEM-01 length prefix is independent of embedded delimiters"
        deliberateDelimiterExamples
    , test "FSEM-01 Unicode Text lengths roundtrip without byte guessing"
        unicodeLengthExamples
    , test "FSEM-01 malformed or noncanonical names are not identities"
        malformedNamesRefused
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label outcome = case outcome of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail)
    >> pure False

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

roots :: [Text.Text]
roots =
  [ ""
  , "a"
  , "a:b"
  , "a:1:b"
  , "a::b"
  , "1:a"
  , "a:0:0"
  , "$phil.local:4:spam:9"
  , "$phil.local:"
  , "x.lock"
  , "root\nline"
  , "é"
  , "e\x0301"
  , "🐈"
  , "👩‍💻"
  , "猫:fish"
  , "a\0b"
  ]

ordinals :: [Int]
ordinals = [0, 1, 2, 9, 10, 99, 100, 1048576, maxBound]

sampleKeys :: [GrammarV1BinderKey]
sampleKeys =
  [GrammarV1BinderKey (DeclarationKey root) ordinal
  | root <- roots, ordinal <- ordinals]

allSampleKeysRoundtrip :: Either String ()
allSampleKeysRoundtrip = mapM_ check sampleKeys
  where
    check key =
      assert
        (grammarV1DecodeBinderCoreName (grammarV1BinderCoreName key) == Just key)
        ("did not roundtrip exact semantic key: " <> show key)

sampleKeysDoNotCollide :: Either String ()
sampleKeysDoNotCollide =
  let names = map grammarV1BinderCoreName sampleKeys
  in assert (length (nub names) == length sampleKeys)
       "two different declaration roots/ordinals produced the same Core.Name"

deliberateDelimiterExamples :: Either String ()
deliberateDelimiterExamples = do
  let examples =
        [ (GrammarV1BinderKey (DeclarationKey "") 0, "$phil.local:0::0")
        , (GrammarV1BinderKey (DeclarationKey "a:b") 10, "$phil.local:3:a:b:10")
        , (GrammarV1BinderKey (DeclarationKey ":") 2, "$phil.local:1:::2")
        , (GrammarV1BinderKey (DeclarationKey "ab") 7, "$phil.local:2:ab:7")
        ]
  mapM_
    (\(key, expected) ->
      assert (grammarV1BinderCoreName key == Name expected)
        ("wrong canonical text serialization for " <> show key))
    examples

unicodeLengthExamples :: Either String ()
unicodeLengthExamples = do
  let cases =
        [ (GrammarV1BinderKey (DeclarationKey "é") 3, "$phil.local:1:é:3")
        , (GrammarV1BinderKey (DeclarationKey "🐈") 4, "$phil.local:1:🐈:4")
        , (GrammarV1BinderKey (DeclarationKey "e\x0301") 5, "$phil.local:2:e\x0301:5")
        , (GrammarV1BinderKey (DeclarationKey "👩‍💻") 6, "$phil.local:3:👩‍💻:6")
        ]
  mapM_
    (\(key, expected) ->
      assert (grammarV1BinderCoreName key == Name expected
        && grammarV1DecodeBinderCoreName (Name expected) == Just key)
        ("Unicode codepoint length mismatch for " <> show key))
    cases

malformedNamesRefused :: Either String ()
malformedNamesRefused = mapM_ check invalid
  where
    invalid =
      [ ""
      , "owner"
      , "$phil.local:"
      , "$phil.local:1:a"
      , "$phil.local:01:a:1"
      , "$phil.local:1:a:00"
      , "$phil.local:1:a:+1"
      , "$phil.local:1:a:-1"
      , "$phil.local:0:a:1"
      , "$phil.local:1:a:1:extra"
      , "$phil.local:1:a:1\n"
      , "$phil.local:2:é:0"
      , "$phil.local:999999999999999999999999999999:a:1"
      , "$phil.local:1:a:999999999999999999999999999999999"
      ]
    check name =
      assert (grammarV1DecodeBinderCoreName (Name name) == Nothing)
        ("accepted noncanonical/generated-impossible name " <> show name)
