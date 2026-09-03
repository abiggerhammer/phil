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
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundaryFailureTypes
  ( grammarV1CheckedBoundaryFailureTypes
  )
import Phil.Surface.GrammarV1.BoundaryPropositions
  ( grammarV1CheckedBoundaryCorrespondences
  , grammarV1CheckedBoundaryLaws
  )
import Phil.Surface.GrammarV1.BoundaryValueType
  ( grammarV1CheckedBoundaryValueType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 checked boundary value types preserve Core focusing outcomes"
        checkedBoundaryValueTypes
    , test "SURF-008 checked boundary failure types preserve order and Core focusing outcomes"
        checkedBoundaryFailureTypes
    , test "SURF-008 checked boundary propositions preserve categories names and Core focusing outcomes"
        checkedBoundaryPropositions
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedBoundaryValueTypes :: Either String ()
checkedBoundaryValueTypes = do
  context1 <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  context <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context1
  state <- bind "u" Unrestricted (TyUInt 8) emptySurfaceState
  primitive <- parseBoundary "boundary-checked-primitive"
    "boundary Word : U32 { canonical; }"
  coercingProof <- parseBoundary "boundary-checked-proof"
    "boundary Evidence : Proof[NeedsNat(u)] { canonical; }"
  transparentRefinement <- parseBoundary "boundary-checked-refinement"
    "boundary PositiveValue : {v : U8 | Positive(v)} { canonical; }"
  unknownClaim <- parseBoundary "boundary-checked-unknown"
    "boundary Unknown : Proof[Missing(u)] { canonical; }"
  tupleType <- parseBoundary "boundary-checked-tuple"
    "boundary Pair : (U8, Bool) { canonical; }"

  let u = RefVar (Name "u")
  assert
    (grammarV1CheckedBoundaryValueType context state primitive ==
      Just (Right (TyUInt 32, [])))
    "ordinary checked boundary type changed Ty or acquired a focusing trace"

  assert
    (grammarV1CheckedBoundaryValueType context state coercingProof ==
      Just
        (Right
          ( TyProof (Atom "NeedsNat" [RefToNat u])
          , [InsertedUIntToNat u]
          )))
    "checked boundary Proof did not preserve exact Core coercion and trace"

  case grammarV1CheckedBoundaryValueType context state transparentRefinement of
    Just (Right (TyRefined binder base predicate, steps)) -> do
      assert (binder == Name "v" && base == TyUInt 8)
        "checked boundary refinement changed binder or base type"
      assert
        (predicate == LessThan
          (RefNat 0)
          (RefToNat (RefVar (Name "v"))))
        "checked boundary refinement did not preserve canonical predicate"
      assert (ExpandedTransparentClaim "Positive" `elem` steps)
        "checked boundary refinement lost transparent-claim focusing trace"
    other -> Left
      ("checked boundary refinement did not produce a focused TyRefined: " <> show other)

  assert
    (grammarV1CheckedBoundaryValueType context state unknownClaim ==
      Just (Left (UnknownClaim "Missing")))
    "checked boundary type collapsed Core UnknownClaim into source non-competence"

  assert
    (grammarV1CheckedBoundaryValueType context state tupleType == Nothing)
    "unsupported tuple boundary type bypassed the checked type competence wall"

checkedBoundaryFailureTypes :: Either String ()
checkedBoundaryFailureTypes = do
  context1 <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  context <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context1
  state <- bind "u" Unrestricted (TyUInt 8) emptySurfaceState
  none <- parseBoundary "boundary-checked-failures-none"
    "boundary None : U8 { canonical; }"
  mixed <- parseBoundary "boundary-checked-failures-mixed" $ Text.unlines
    [ "boundary Mixed : U8 {"
    , "  failure U32;"
    , "  failure Proof[NeedsNat(u)];"
    , "  failure {v : U8 | Positive(v)};"
    , "}"
    ]
  unknown <- parseBoundary "boundary-checked-failures-unknown" $ Text.unlines
    [ "boundary UnknownFailure : U8 {"
    , "  failure U32;"
    , "  failure Proof[Missing(u)];"
    , "}"
    ]
  unsupported <- parseBoundary "boundary-checked-failures-unsupported" $ Text.unlines
    [ "boundary UnsupportedFailure : U8 {"
    , "  failure U8;"
    , "  failure (U32, Bool);"
    , "}"
    ]

  let u = RefVar (Name "u")
  assert
    (grammarV1CheckedBoundaryFailureTypes context state none == Just (Right []))
    "boundary without failure declarations did not preserve exact empty checked surface"

  case grammarV1CheckedBoundaryFailureTypes context state mixed of
    Just
      (Right
        [ (TyUInt 32, [])
        , (TyProof proofProposition, proofSteps)
        , (TyRefined binder base predicate, refinementSteps)
        ]) -> do
          assert
            (proofProposition == Atom "NeedsNat" [RefToNat u])
            "checked boundary failure Proof changed canonical proposition"
          assert
            (proofSteps == [InsertedUIntToNat u])
            "checked boundary failure Proof lost exact UInt-to-Nat trace"
          assert (binder == Name "v" && base == TyUInt 8)
            "checked boundary failure refinement changed binder or base type"
          assert
            (predicate == LessThan
              (RefNat 0)
              (RefToNat (RefVar (Name "v"))))
            "checked boundary failure refinement changed canonical predicate"
          assert (ExpandedTransparentClaim "Positive" `elem` refinementSteps)
            "checked boundary failure refinement lost transparent-claim trace"
    other -> Left
      ("checked boundary failure routing changed order, type meaning, or trace shape: "
        <> show other)

  assert
    (grammarV1CheckedBoundaryFailureTypes context state unknown ==
      Just (Left (UnknownClaim "Missing")))
    "boundary failure Core error collapsed into source non-competence or partial success"

  assert
    (grammarV1CheckedBoundaryFailureTypes context state unsupported == Nothing)
    "unsupported tuple failure type was partially accepted by checked boundary routing"

checkedBoundaryPropositions :: Either String ()
checkedBoundaryPropositions = do
  context1 <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  context <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context1
  state <- bind "u" Unrestricted (TyUInt 8) emptySurfaceState
  none <- parseBoundary "boundary-checked-propositions-none"
    "boundary None : U8 { canonical; }"
  rich <- parseBoundary "boundary-checked-propositions-rich" $ Text.unlines
    [ "boundary Facts : U8 {"
    , "  correspondence NeedsNat(u);"
    , "  correspondence true;"
    , "  law PositiveLaw : Positive(u);"
    , "  law LiteralLaw : true;"
    , "}"
    ]
  badLaw <- parseBoundary "boundary-checked-propositions-bad-law" $ Text.unlines
    [ "boundary BadLaw : U8 {"
    , "  correspondence true;"
    , "  law Bad : Missing(u);"
    , "}"
    ]
  badCorrespondence <- parseBoundary "boundary-checked-propositions-bad-correspondence" $ Text.unlines
    [ "boundary BadCorrespondence : U8 {"
    , "  correspondence Missing(u);"
    , "  law Fine : true;"
    , "}"
    ]
  unsupportedLaw <- parseBoundary "boundary-checked-propositions-unsupported-law" $ Text.unlines
    [ "boundary UnsupportedLaw : U8 {"
    , "  law Specialized : NeedsNat[U8](u);"
    , "}"
    ]

  let u = RefVar (Name "u")
  assert
    (grammarV1CheckedBoundaryCorrespondences context state none == Just (Right []))
    "boundary without correspondences did not preserve exact empty checked category"
  assert
    (grammarV1CheckedBoundaryLaws context state none == Just (Right []))
    "boundary without laws did not preserve exact empty checked category"

  case grammarV1CheckedBoundaryCorrespondences context state rich of
    Just
      (Right
        [ (Atom "NeedsNat" [RefToNat actualU], [InsertedUIntToNat tracedU])
        , (Truth, [])
        ]) -> do
          assert (actualU == u && tracedU == u)
            "checked boundary correspondence lost exact UInt-to-Nat subject/trace"
    other -> Left
      ("checked boundary correspondences changed order, canonical meaning, or trace: "
        <> show other)

  case grammarV1CheckedBoundaryLaws context state rich of
    Just
      (Right
        [ ("PositiveLaw", predicate, positiveSteps)
        , ("LiteralLaw", Truth, [])
        ]) -> do
          assert
            (predicate == LessThan (RefNat 0) (RefToNat u))
            "checked boundary law lost transparent canonical proposition"
          assert (ExpandedTransparentClaim "Positive" `elem` positiveSteps)
            "checked boundary law lost transparent-claim expansion trace"
    other -> Left
      ("checked boundary laws changed names, order, canonical meaning, or trace: "
        <> show other)

  assert
    (grammarV1CheckedBoundaryCorrespondences context state badLaw ==
      Just (Right [(Truth, [])]))
    "bad law incorrectly poisoned independent correspondence category"
  assert
    (grammarV1CheckedBoundaryLaws context state badLaw ==
      Just (Left (UnknownClaim "Missing")))
    "law Core error collapsed into source non-competence"

  assert
    (grammarV1CheckedBoundaryCorrespondences context state badCorrespondence ==
      Just (Left (UnknownClaim "Missing")))
    "correspondence Core error collapsed into source non-competence"
  assert
    (grammarV1CheckedBoundaryLaws context state badCorrespondence ==
      Just (Right [("Fine", Truth, [])]))
    "bad correspondence incorrectly poisoned independent law category"

  assert
    (grammarV1CheckedBoundaryLaws context state unsupportedLaw == Nothing)
    "specialized law application bypassed checked proposition competence wall"

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

parseBoundary :: Text.Text -> Text.Text -> Either String GrammarV1BoundaryDecl
parseBoundary label source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource label source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1BoundaryDeclaration boundary -> Right boundary
      other -> Left ("expected boundary declaration, got " <> show other)
    declarations -> Left
      ("expected one boundary declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
