{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 primitive types preserve exact Core meaning"
        primitiveTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

primitiveTypesPreserveMeaning :: Either String ()
primitiveTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-primitive-types" source
  actual <- mapM primitiveType (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "primitive type elaboration changed or accepted an invalid width: " <> show actual
  where
    expected =
      [ Just TyUnit
      , Just TyBool
      , Just (TyUInt 1)
      , Just (TyUInt 32)
      , Nothing
      , Nothing
      , Nothing
      ]

primitiveType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
primitiveType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1PrimitiveType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type UnitT = Unit;"
  , "type BoolT = Bool;"
  , "type BitT = U1;"
  , "type WordT = U32;"
  , "type ZeroWidth = U0;"
  , "type HugeWidth = U999999999999999999999999999999999999999999;"
  , "type NamedT = Other;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
