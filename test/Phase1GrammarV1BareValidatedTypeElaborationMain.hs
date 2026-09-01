{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Name (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.IntrinsicValidatedType
  ( grammarV1BareValidatedType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 bare Grammar-v1 Validated types preserve exact Core identities"
        bareValidatedTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

bareValidatedTypesPreserveMeaning :: Either String ()
bareValidatedTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-validated-types" source
  actual <- mapM validatedType (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "Validated elaboration changed explicit identities or accepted a lossy form: " <> show actual
  where
    expected =
      [ Just (TyValidated "Check" (Name "payload") (Name "evidence"))
      , Just (TyValidated "auth.Check" (Name "payload") (Name "evidence"))
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      ]

validatedType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
validatedType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1BareValidatedType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type Checked = Validated[Check, payload, evidence];"
  , "type QualifiedValidator = Validated[auth.Check, payload, evidence];"
  , "type SpecializedValidator = Validated[Check[U32], payload, evidence];"
  , "type QualifiedInput = Validated[Check, pkg.payload, evidence];"
  , "type ProjectedInput = Validated[Check, (payload).field, evidence];"
  , "type NotValidated = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
