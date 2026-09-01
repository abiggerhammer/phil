{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
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
  , moveVariable
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundProofType
  ( grammarV1BoundProofType
  )
import Phil.Surface.GrammarV1.IntrinsicProofType
  ( grammarV1IntrinsicProofType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic Proof composition preserves exact Core meaning"
        intrinsicProofTypesPreserveMeaning
    , test "SURF-008 binding-aware Proof composition preserves exact Core meaning and poisons unresolved trees"
        boundProofTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicProofTypesPreserveMeaning :: Either String ()
intrinsicProofTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-proof-composition" intrinsicSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicProofType sourceTypes
      expected =
        [ Just (TyProof (greaterThanCanonical 7 3))
        , Just (TyProof (Conjunction (Atom "Ready" [RefNat 1]) (Negation Falsehood)))
        , Just (TyProof (Disjunction (Equal (RefNat 1) (RefNat 1)) (Atom "Flag" [RefBool True])))
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "intrinsic Proof composition changed a verified leaf/tree or accepted contextual specialization: " <> show actual
  where
    greaterThanCanonical left right = LessThan (RefNat right) (RefNat left)

boundProofTypesPreserveMeaning :: Either String ()
boundProofTypesPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "flag" Unrestricted TyBool state2
  state4 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state3
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state4
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-proof-composition" boundSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  let actual = map (grammarV1BoundProofType state) sourceTypes
      expected =
        [ Just
            (TyProof
              (Conjunction
                Truth
                (LessThan (RefVar (Name "n")) (RefVar (Name "m")))))
        , Just
            (TyProof
              (Disjunction
                (Atom "Ready" [RefVar (Name "n"), RefBool True])
                Falsehood))
        , Just
            (TyProof
              ( Disjunction
                  (Conjunction
                    (Negation Falsehood)
                    (LessEqual (RefVar (Name "n")) (RefNat 7)))
                  (Atom "Ready" [RefVar (Name "flag"), RefVar (Name "n")])
              ))
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binding-aware Proof composition changed a verified tree or failed to poison an unresolved nested leaf: " <> show actual

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

typeAliasTarget
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Type
typeAliasTarget (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (locatedValue (grammarV1TypeAliasTarget aliasDecl))
    other -> Left ("expected type alias declaration, got " <> show other)

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "type RelationProof = Proof[7 > 3];"
  , "type ClaimProof = Proof[Ready(1) and not false];"
  , "type MixedProof = Proof[1 == 1 or Flag(true)];"
  , "type ContextProof = Proof[x == 0];"
  , "type SpecializedProof = Proof[Ready[U32](1)];"
  , "type NotProof = Bool;"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "type BoundRelationProof = Proof[true and n < m];"
  , "type BoundClaimProof = Proof[Ready(n, true) or false];"
  , "type MixedBoundProof = Proof[not false and n <= 7 or Ready(flag, n)];"
  , "type UnknownProof = Proof[true and missing == n];"
  , "type ArithmeticProof = Proof[true and n + 1 == m];"
  , "type SpecializedProof = Proof[true and Ready[U32](n)];"
  , "type ConsumedProof = Proof[Ready(spent) or false];"
  , "type ProjectedProof = Proof[(n).field == n or true];"
  , "type NotProof = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
