{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( GrammarId (..)
  , Name (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.IntrinsicType (grammarV1IntrinsicType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic type composition preserves exact Core meaning"
        intrinsicTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicTypesPreserveMeaning :: Either String ()
intrinsicTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-types" source
  actual <- mapM intrinsicType (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "intrinsic type composition changed a verified type or accepted a contextual/specialized form: " <> show actual
  where
    expected =
      [ Just TyUnit
      , Just TyBool
      , Just (TyUInt 32)
      , Just (TyBytes (RefNat 7))
      , Just
          (TyProof
            (Disjunction
              (Atom "Ready" [RefNat 1])
              (Equal (RefNat 1) (RefNat 1))))
      , Just (TyFrame (GrammarId "Hello"))
      , Just (TyFrame (GrammarId "Wire.Codec"))
      , Just (TyValidated "Check" (Name "payload") (Name "evidence"))
      , Just (TyValidated "Rules.Check" (Name "payload") (Name "evidence"))
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      ]

intrinsicType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
intrinsicType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1IntrinsicType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type UnitT = Unit;"
  , "type BoolT = Bool;"
  , "type WordT = U32;"
  , "type BytesT = Bytes[7];"
  , "type ProofT = Proof[Ready(1) or 1 == 1];"
  , "type FrameT = Frame[Hello];"
  , "type QualifiedFrameT = Frame[Wire.Codec];"
  , "type ValidatedT = Validated[Check, payload, evidence];"
  , "type QualifiedValidatedT = Validated[Rules.Check, payload, evidence];"
  , "type SpecializedValidated = Validated[Check[U32], payload, evidence];"
  , "type QualifiedValidatedInput = Validated[Check, pkg.payload, evidence];"
  , "type ProjectedValidatedInput = Validated[Check, (payload).field, evidence];"
  , "type ZeroWidth = U0;"
  , "type ContextBytes = Bytes[x];"
  , "type SpecializedFrame = Frame[Wire.Codec[U32]];"
  , "type NamedT = Other;"
  , "type TupleT = (U32, Bool);"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
