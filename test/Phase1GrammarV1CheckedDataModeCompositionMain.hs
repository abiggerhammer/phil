{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.NominalDataMode
  ( NominalModeError (..)
  , NominalRestrictionJustification (..)
  )
import Phil.Core.Static
  ( declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..)
  , GrammarV1CheckedDataModeError (..)
  , GrammarV1CheckedVariantMode (..)
  , GrammarV1CheckedVariantModePayload (..)
  , grammarV1CheckedClosedDataMode
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed data mode derives from exact checked payload modes"
        checkedClosedDataMode
    , test "SURF-008 closed data mode preserves nominal strengthening and weakening semantics"
        nominalModeSemantics
    , test "SURF-008 closed data mode preserves focusing rejection and mode competence walls"
        competenceAndFailureBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedClosedDataMode :: Either String ()
checkedClosedDataMode = do
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  declaration <- parseData $ unlines
    [ "data Choice ="
    , "    None"
    , "  | EmptyTuple()"
    , "  | EmptyRecord{}"
    , "  | Pair(U8, Bool)"
    , "  | Owned(Bytes[7])"
    , "  | Named{left : U32, refined : {v : U8 | Positive(v)},}"
    , "  | Same(U8)"
    , "  | Same(Bytes[3])"
    , "  ;"
    ]
  case grammarV1CheckedClosedDataMode context Nothing declaration of
    Just
      (Right
        (GrammarV1CheckedDataMode
          [ GrammarV1CheckedVariantMode "None" Nothing
          , GrammarV1CheckedVariantMode "EmptyTuple"
              (Just (GrammarV1CheckedVariantModeTuple []))
          , GrammarV1CheckedVariantMode "EmptyRecord"
              (Just (GrammarV1CheckedVariantModeRecord []))
          , GrammarV1CheckedVariantMode "Pair"
              (Just (GrammarV1CheckedVariantModeTuple
                [ (CheckedTypeMode (TyUInt 8) Unrestricted, [])
                , (CheckedTypeMode TyBool Unrestricted, [])
                ]))
          , GrammarV1CheckedVariantMode "Owned"
              (Just (GrammarV1CheckedVariantModeTuple
                [(CheckedTypeMode (TyBytes (RefNat 7)) Linear, [])]))
          , GrammarV1CheckedVariantMode "Named"
              (Just (GrammarV1CheckedVariantModeRecord
                [ ("left", CheckedTypeMode (TyUInt 32) Unrestricted, [])
                , ( "refined"
                  , CheckedTypeMode (TyRefined binder base predicate) Unrestricted
                  , steps
                  )
                ]))
          , GrammarV1CheckedVariantMode "Same"
              (Just (GrammarV1CheckedVariantModeTuple
                [(CheckedTypeMode (TyUInt 8) Unrestricted, [])]))
          , GrammarV1CheckedVariantMode "Same"
              (Just (GrammarV1CheckedVariantModeTuple
                [(CheckedTypeMode (TyBytes (RefNat 3)) Linear, [])]))
          ]
          Linear)) -> do
            assert (binder == Name "v" && base == TyUInt 8)
              "checked data-mode refinement changed binder or base type"
            assert
              (predicate == LessThan
                (RefNat 0)
                (RefToNat (RefVar (Name "v"))))
              "checked data-mode refinement changed canonical predicate"
            assert (ExpandedTransparentClaim "Positive" `elem` steps)
              "checked data-mode refinement lost focusing trace"
    other -> Left
      ("closed data-mode composition changed variant order/shape/type/mode or duplicate identity: "
        <> show other)

nominalModeSemantics :: Either String ()
nominalModeSemantics = do
  strengthened <- parseData "data Token mode affine = Token(U64);"
  weakened <- parseData "data Bad mode unrestricted = Holds(Bytes[7]);"
  assert
    ( grammarV1CheckedClosedDataMode emptyStaticContext Nothing strengthened
        == Just
          (Left
            (GrammarV1DataModeNominalError
              (StrongerModeMissingJustification Unrestricted Affine)))
    )
    "strict data-mode strengthening bypassed Core justification requirements"
  case grammarV1CheckedClosedDataMode
      emptyStaticContext
      (Just (AdmittedResourceObligation "nominal token lifecycle"))
      strengthened of
    Just (Right result) ->
      assert (checkedDataStructuralMode result == Affine)
        "admitted nominal justification did not permit affine strengthening"
    other -> Left
      ("admitted data-mode strengthening did not close: " <> show other)
  assert
    ( grammarV1CheckedClosedDataMode emptyStaticContext Nothing weakened
        == Just
          (Left
            (GrammarV1DataModeNominalError
              (DeclaredModeWeakensDerived Linear Unrestricted)))
    )
    "explicit unrestricted data mode laundered intrinsic linear payload mode"

competenceAndFailureBoundaries :: Either String ()
competenceAndFailureBoundaries = do
  unknown <- parseData "data Unknown = Bad(Proof[Missing()]);"
  named <- parseData "data Named = Value(Resource);"
  frame <- parseData "data Framed = Value(Frame[Hello]);"
  generic <- parseData "data Box[T : Type] = Value(T);"
  constrained <- parseData
    "data Constrained requires { proposition true; } = Value(U8);"
  assert
    ( grammarV1CheckedClosedDataMode emptyStaticContext Nothing unknown
        == Just (Left (GrammarV1DataModeFocusingError (UnknownClaim "Missing")))
    )
    "data payload Core focusing error collapsed into source non-competence"
  assert
    (grammarV1CheckedClosedDataMode emptyStaticContext Nothing named == Nothing)
    "opaque named payload acquired a guessed structural mode"
  assert
    (grammarV1CheckedClosedDataMode emptyStaticContext Nothing frame == Nothing)
    "Frame payload acquired a constructor-spelling structural mode"
  assert
    (grammarV1CheckedClosedDataMode emptyStaticContext Nothing generic == Nothing)
    "generic data declaration bypassed the closed data-mode competence wall"
  assert
    (grammarV1CheckedClosedDataMode emptyStaticContext Nothing constrained == Nothing)
    "requirement-bearing data declaration bypassed the closed data-mode competence wall"

parseData :: String -> Either String GrammarV1DataDecl
parseData source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-data-mode-composition" (Text.pack source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1DataDeclaration declaration -> Right declaration
      other -> Left ("expected data declaration, got " <> show other)
    declarations -> Left
      ("expected one data declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
