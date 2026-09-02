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
