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
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.IntrinsicProposition
  ( grammarV1IntrinsicProposition
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic proposition fragments compose exactly and fail closed"
        intrinsicPropositionsComposeExactly
    , test "SURF-008 binding-aware proposition fragments compose richer verified trees and poison unresolved trees"
        boundPropositionsComposeExactly
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicPropositionsComposeExactly :: Either String ()
intrinsicPropositionsComposeExactly = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-propositions" intrinsicSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicProposition propositions
      expected =
        [ Just (Conjunction (Negation Falsehood) Truth)
        , Just (Conjunction Truth (LessThan (RefNat 3) (RefNat 7)))
        , Just (Disjunction (Atom "Ready" [RefNat 1, RefBool True]) Falsehood)
        , Just
            ( Disjunction
                (Conjunction (Negation Falsehood) (LessThan (RefNat 3) (RefNat 7)))
                (Atom "Ready" [RefNat 1, RefBool True])
            )
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "intrinsic proposition composition changed a verified leaf/tree or accepted a contextual leaf: " <> show actual

boundPropositionsComposeExactly :: Either String ()
boundPropositionsComposeExactly = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "flag" Unrestricted TyBool state2
  state4 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state3
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state4
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-propositions" boundSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map (grammarV1BoundProposition state) propositions
      expected =
        [ Just
            (Conjunction
              Truth
              (LessThan (RefVar (Name "n")) (RefVar (Name "m"))))
        , Just
            (Disjunction
              (Atom "Ready" [RefVar (Name "n"), RefBool True])
              Falsehood)
        , Just
            ( Disjunction
                (Conjunction
                  (Negation Falsehood)
                  (LessEqual (RefVar (Name "n")) (RefNat 7)))
                (Atom "Ready" [RefVar (Name "flag"), RefVar (Name "n")])
            )
        , Nothing
        , Just
            (Conjunction
              Truth
              (Equal
                (RefAdd (RefVar (Name "n")) (RefNat 1))
                (RefVar (Name "m"))))
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binding-aware proposition composition changed a verified tree or failed to poison an unresolved nested leaf: " <> show actual

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

claimProposition
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Proposition
claimProposition (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl ->
      case grammarV1ClaimProposition claimDecl of
        Just proposition -> Right (locatedValue proposition)
        Nothing -> Left "claim had no proposition"
    other -> Left ("expected claim declaration, got " <> show other)

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "claim TruthTree = not false and true;"
  , "claim RelationTree = true and 7 > 3;"
  , "claim ClaimTree = Ready(1, true) or false;"
  , "claim MixedTree = not false and 7 > 3 or Ready(1, true);"
  , "claim Contextual(x : U32) = true and x == 1;"
  , "claim Specialized = true and Ready[U32](1);"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "claim BoundRelationTree = true and n < m;"
  , "claim BoundClaimTree = Ready(n, true) or false;"
  , "claim MixedBoundTree = not false and n <= 7 or Ready(flag, n);"
  , "claim UnknownNested = true and missing == n;"
  , "claim ArithmeticNested = true and n + 1 == m;"
  , "claim SpecializedNested = true and Ready[U32](n);"
  , "claim ConsumedNested = Ready(spent) or false;"
  , "claim ProjectedNested = (n).field == n or true;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
