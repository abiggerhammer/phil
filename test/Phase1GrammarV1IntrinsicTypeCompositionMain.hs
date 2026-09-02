{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( declareOpaqueClaim
  , declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( GrammarId (..)
  , Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  , moveVariable
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundType (grammarV1BoundType)
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedType)
import Phil.Surface.GrammarV1.IntrinsicType (grammarV1IntrinsicType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic type composition preserves exact Core meaning"
        intrinsicTypesPreserveMeaning
    , test "SURF-008 binding-aware type composition preserves richer verified fragments and focused coercion"
        boundTypesPreserveMeaning
    , test "SURF-008 checked type composition preserves structural competence and Core focusing outcomes"
        checkedTypesPreserveCompetence
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicTypesPreserveMeaning :: Either String ()
intrinsicTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-types" intrinsicSource
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
      , Just (TyRefined (Name "v") (TyUInt 8) Truth)
      , Just
          (TyRefined
            (Name "b")
            TyBool
            (Conjunction Truth (Negation Falsehood)))
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Just (TyOpaque "Other")
      , Just (TyOpaque "pkg.Other")
      , Nothing
      , Nothing
      ]

boundTypesPreserveMeaning :: Either String ()
boundTypesPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "flag" Unrestricted TyBool state1
  state3 <- bind "u" Unrestricted (TyUInt 32) state2
  state4 <- bind "bytes" Unrestricted (TyBytes (RefNat 4)) state3
  state5 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state4
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state5
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-types" boundSource
  actual <- mapM (boundType state) (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "binding-aware type composition changed a verified type or accepted an unresolved contextual form: " <> show actual
  where
    expected =
      [ Just TyUnit
      , Just (TyBytes (RefNat 7))
      , Just (TyBytes (RefVar (Name "n")))
      , Just (TyBytes (RefAdd (RefVar (Name "n")) (RefNat 1)))
      , Just (TyBytes (RefLen (RefVar (Name "bytes"))))
      , Just (TyBytes (RefToNat (RefVar (Name "u"))))
      , Just
          (TyProof
            (Conjunction
              (LessThan (RefVar (Name "n")) (RefNat 7))
              (Atom "Ready" [RefVar (Name "flag"), RefVar (Name "n")])))
      , Just
          (TyProof
            (Disjunction
              (Atom "Ready" [RefNat 1])
              (Equal (RefNat 1) (RefNat 1))))
      , Just (TyFrame (GrammarId "Hello"))
      , Just (TyValidated "Check" (Name "payload") (Name "evidence"))
      , Just (TyRefined (Name "v") (TyUInt 8) Truth)
      , Just
          (TyRefined
            (Name "b")
            TyBool
            (Equal (RefVar (Name "b")) (RefBool True)))
      , Just
          (TyRefined
            (Name "b")
            TyBool
            (Equal (RefVar (Name "b")) (RefVar (Name "flag"))))
      , Nothing
      , Just
          (TyRefined
            (Name "v")
            (TyUInt 8)
            (LessThan (RefNat 0) (RefToNat (RefVar (Name "v")))))
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Just
          (TyProof
            (Equal
              (RefAdd (RefVar (Name "n")) (RefNat 1))
              (RefNat 7)))
      , Nothing
      , Just (TyOpaque "Other")
      , Just (TyOpaque "pkg.Other")
      , Nothing
      , Nothing
      ]

checkedTypesPreserveCompetence :: Either String ()
checkedTypesPreserveCompetence = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "flag" Unrestricted TyBool state1
  state <- bind "u8" Unrestricted (TyUInt 8) state2
  context1 <- mapLeft show $
    declareOpaqueClaim "Flagged" [(Name "flag", SortBool)] emptyStaticContext
  context2 <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context1
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      context2
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-checked-types" checkedSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  let n = RefVar (Name "n")
      flag = RefVar (Name "flag")
      u8 = RefVar (Name "u8")
      v = RefVar (Name "v")
      actual = map (grammarV1CheckedType context state) sourceTypes
      expected =
        [ Just (Right (TyUnit, []))
        , Just (Right (TyBytes (RefAdd n (RefNat 1)), []))
        , Just (Right (TyFrame (GrammarId "Hello"), []))
        , Just (Right (TyOpaque "Other", []))
        , Just (Right (TyProof (Atom "Flagged" [flag]), []))
        , Just
            (Right
              ( TyProof (Atom "NeedsNat" [RefToNat u8])
              , [InsertedUIntToNat u8]
              ))
        , Just (Left (UnknownClaim "Missing"))
        , Just
            (Right
              ( TyRefined
                  (Name "v")
                  (TyUInt 8)
                  (LessThan (RefNat 0) (RefToNat v))
              , [ExpandedTransparentClaim "Positive"]
              ))
        , Just
            (Right
              ( TyRefined
                  (Name "v")
                  (TyUInt 8)
                  (Atom "NeedsNat" [RefToNat v])
              , [InsertedUIntToNat v]
              ))
        , Just (Left (UnknownClaim "Missing"))
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "checked type composition changed type/trace meaning or collapsed source non-competence with Core rejection: "
      <> show actual

intrinsicType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
intrinsicType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1IntrinsicType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

boundType
  :: SurfaceState
  -> Located GrammarV1TopLevelDecl
  -> Either String (Maybe Ty)
boundType state (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1BoundType state (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

typeAliasTarget
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Type
typeAliasTarget (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (locatedValue (grammarV1TypeAliasTarget aliasDecl))
    other -> Left ("expected type alias declaration, got " <> show other)

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "type UnitT = Unit;"
  , "type BoolT = Bool;"
  , "type WordT = U32;"
  , "type BytesT = Bytes[7];"
  , "type ProofT = Proof[Ready(1) or 1 == 1];"
  , "type FrameT = Frame[Hello];"
  , "type QualifiedFrameT = Frame[Wire.Codec];"
  , "type ValidatedT = Validated[Check, payload, evidence];"
  , "type QualifiedValidatedT = Validated[Rules.Check, payload, evidence];"
  , "type IntrinsicRefinement = {v : U8 | true};"
  , "type IntrinsicRefinementTree = {b : Bool | true and not false};"
  , "type BinderRefinement = {b : Bool | b == true};"
  , "type SpecializedValidated = Validated[Check[U32], payload, evidence];"
  , "type QualifiedValidatedInput = Validated[Check, pkg.payload, evidence];"
  , "type ProjectedValidatedInput = Validated[Check, (payload).field, evidence];"
  , "type ZeroWidth = U0;"
  , "type ContextBytes = Bytes[x];"
  , "type SpecializedFrame = Frame[Wire.Codec[U32]];"
  , "type NamedT = Other;"
  , "type QualifiedNamedT = pkg.Other;"
  , "type SpecializedNamedT = Other[U32];"
  , "type TupleT = (U32, Bool);"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "type UnitT = Unit;"
  , "type LiteralBytes = Bytes[7];"
  , "type BoundBytes = Bytes[n];"
  , "type ArithmeticBytes = Bytes[n + 1];"
  , "type LengthBytes = Bytes[len(bytes)];"
  , "type ToNatBytes = Bytes[toNat(u)];"
  , "type BoundProof = Proof[n < 7 and Ready(flag, n)];"
  , "type IntrinsicProof = Proof[Ready(1) or 1 == 1];"
  , "type FrameT = Frame[Hello];"
  , "type ValidatedT = Validated[Check, payload, evidence];"
  , "type IntrinsicRefinement = {v : U8 | true};"
  , "type BoundRefinement = {b : Bool | b == true};"
  , "type OuterRefinement = {b : Bool | b == flag};"
  , "type ShadowedRefinement = {flag : Bool | true};"
  , "type CoercionRefinement = {v : U8 | v > 0};"
  , "type WrongSortBytes = Bytes[flag];"
  , "type UnknownBytes = Bytes[missing];"
  , "type UnknownProof = Proof[missing == n];"
  , "type ConsumedProof = Proof[Ready(spent)];"
  , "type ArithmeticProof = Proof[n + 1 == 7];"
  , "type SpecializedProof = Proof[Ready[U32](n)];"
  , "type NamedT = Other;"
  , "type QualifiedNamedT = pkg.Other;"
  , "type SpecializedNamedT = Other[U32];"
  , "type TupleT = (U32, Bool);"
  ]

checkedSource :: Text.Text
checkedSource = Text.unlines
  [ "type UnitT = Unit;"
  , "type BytesT = Bytes[n + 1];"
  , "type FrameT = Frame[Hello];"
  , "type NamedT = Other;"
  , "type OpaqueProof = Proof[Flagged(flag)];"
  , "type CoercingProof = Proof[NeedsNat(u8)];"
  , "type UnknownProof = Proof[Missing(flag)];"
  , "type TransparentRefinement = {v : U8 | Positive(v)};"
  , "type CoercingRefinement = {v : U8 | NeedsNat(v)};"
  , "type UnknownRefinement = {v : U8 | Missing(v)};"
  , "type SpecializedProof = Proof[Flagged[U8](flag)];"
  , "type WrongSortBytes = Bytes[flag];"
  , "type TupleT = (U8, Bool);"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
