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
import Phil.Surface.GrammarV1.BoundRelation
  ( grammarV1BoundRelationProposition
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1RelationProposition)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 relation operators preserve exact Core meaning"
        relationOperatorsPreserveMeaning
    , test "SURF-008 binding-aware relation routing preserves richer refinement expressions and sort competence"
        boundRelationsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

relationOperatorsPreserveMeaning :: Either String ()
relationOperatorsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-relations" relationSource
  operators <- mapM relationOperator (grammarV1TopLevelDecls sourceFile)
  assert (operators == expectedOperators) $
    "parsed relation operator sequence changed: " <> show operators
  let actual = map (\operator -> grammarV1RelationProposition operator leftTerm rightTerm) operators
  assert (actual == expectedPropositions) $
    "relation elaboration changed semantic proposition: " <> show actual
  where
    leftTerm = RefVar (Name "left")
    rightTerm = RefVar (Name "right")
    expectedOperators =
      [ GrammarV1EqualRelation
      , GrammarV1NotEqualRelation
      , GrammarV1LessEqualRelation
      , GrammarV1GreaterEqualRelation
      , GrammarV1LessRelation
      , GrammarV1GreaterRelation
      , GrammarV1InRelation
      , GrammarV1DisjointRelation
      ]
    expectedPropositions =
      [ Equal leftTerm rightTerm
      , NotEqual leftTerm rightTerm
      , LessEqual leftTerm rightTerm
      , LessEqual rightTerm leftTerm
      , LessThan leftTerm rightTerm
      , LessThan rightTerm leftTerm
      , Member leftTerm rightTerm
      , Disjoint leftTerm rightTerm
      ]

boundRelationsPreserveMeaning :: Either String ()
boundRelationsPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "flag" Unrestricted TyBool state2
  state4 <- bind "flag2" Unrestricted TyBool state3
  state5 <- bind "u" Unrestricted (TyUInt 32) state4
  state6 <- bind "v" Unrestricted (TyUInt 32) state5
  state7 <- bind "bytes" Unrestricted (TyBytes (RefNat 4)) state6
  state8 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state7
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state8
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-relations" boundRelationSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let n = RefVar (Name "n")
      m = RefVar (Name "m")
      u = RefVar (Name "u")
      bytes = RefVar (Name "bytes")
      actual = map (grammarV1BoundRelationProposition state) propositions
      expected =
        [ Just (LessThan n m)
        , Just (LessEqual n (RefNat 7))
        , Just (Equal (RefVar (Name "flag")) (RefVar (Name "flag2")))
        , Just (Equal u (RefVar (Name "v")))
        , Just (LessThan n m)
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Just (Equal (RefAdd n (RefNat 1)) m)
        , Just (Equal (RefSub m (RefNat 1)) n)
        , Just (Equal (RefScale 2 n) m)
        , Just (Equal (RefScale 2 n) m)
        , Just (Equal (RefLen bytes) (RefNat 4))
        , Just (Equal (RefToNat u) (RefNat 7))
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binding-aware relation elaboration changed meaning or accepted an incompetent source form: " <> show actual

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

relationOperator
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1RelationOperator
relationOperator (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl ->
      case grammarV1ClaimProposition claimDecl of
        Just (Located _ (GrammarV1RelationProposition _ operator _)) ->
          Right (locatedValue operator)
        other -> Left ("expected relation claim proposition, got " <> show other)
    other -> Left ("expected claim declaration, got " <> show other)

relationSource :: Text.Text
relationSource = Text.unlines
  [ "claim Eq(a : U32, b : U32) = a == b;"
  , "claim Ne(a : U32, b : U32) = a != b;"
  , "claim Le(a : U32, b : U32) = a <= b;"
  , "claim Ge(a : U32, b : U32) = a >= b;"
  , "claim Lt(a : U32, b : U32) = a < b;"
  , "claim Gt(a : U32, b : U32) = a > b;"
  , "claim In(a : U32, b : U32) = a in b;"
  , "claim Dj(a : U32, b : U32) = a disjoint b;"
  ]

boundRelationSource :: Text.Text
boundRelationSource = Text.unlines
  [ "claim NatOrder = n < m;"
  , "claim NatMixed = n <= 7;"
  , "claim BoolEq = flag == flag2;"
  , "claim UIntEq = u == v;"
  , "claim Greater = m > n;"
  , "claim SortMismatch = n == flag;"
  , "claim BadOrder = flag < flag2;"
  , "claim Unknown = missing == n;"
  , "claim Qualified = pkg.n == n;"
  , "claim Specialized = n[U32] == n;"
  , "claim Called = n(1) == n;"
  , "claim Projected = (n).field == n;"
  , "claim Consumed = spent == n;"
  , "claim Arithmetic = n + 1 == m;"
  , "claim Subtraction = m - 1 == n;"
  , "claim ScaleLeft = 2 * n == m;"
  , "claim ScaleRight = n * 2 == m;"
  , "claim Length = len(bytes) == 4;"
  , "claim ExplicitToNat = toNat(u) == 7;"
  , "claim MixedNeedsFocus = u < 7;"
  , "claim SymbolicMultiply = n * m == n;"
  , "claim TruthLeaf = true;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
