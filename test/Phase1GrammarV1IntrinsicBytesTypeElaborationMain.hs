{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (RefTerm (..), Ty (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicBytesType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 literal Bytes sizes elaborate exactly"
        literalBytesSizesElaborateExactly
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

literalBytesSizesElaborateExactly :: Either String ()
literalBytesSizesElaborateExactly = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bytes-literals" source
  actual <- mapM bytesType (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "literal Bytes elaboration changed or guessed a contextual size: " <> show actual
  where
    expected =
      [ Just (TyBytes (RefNat 0))
      , Just (TyBytes (RefNat 7))
      , Nothing
      , Nothing
      ]

bytesType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
bytesType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1IntrinsicBytesType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type EmptyBytes = Bytes[0];"
  , "type SevenBytes = Bytes[7];"
  , "type NamedBytes = Bytes[n];"
  , "type PlainWord = U8;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
