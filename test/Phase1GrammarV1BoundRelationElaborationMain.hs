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
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 binding-aware relation routing preserves exact meaning and sort competence"
        boundRelationsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

boundRelationsPreserveMeaning :: Either String ()
boundRelationsPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "flag" Unrestricted TyBool state2
  state4 <- bind "flag2" Unrestricted TyBool state3
  state5 <- bind "u" Unrestricted (TyUInt 32) state4
  state6 <- bind "v" Unrestricted (TyUInt 32) state5
  state7 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state6
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state7
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-relations" source
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual =
        map (grammarV1BoundRelationProposition state) propositions
          <> [ grammarV1BoundRelationProposition state projectedProposition
             , grammarV1BoundRelationProposition state arithmeticProposition
             ]
      expected =
        [ Just (LessThan (RefVar (Name "n")) (RefVar (Name "m")))
        , Just (LessEqual (RefVar (Name "n")) (RefNat 7))
        , Just (Equal (RefVar (Name "flag")) (RefVar (Name "flag2")))
        , Just (Equal (RefVar (Name "u")) (RefVar (Name "v")))
        , Just (LessThan (RefVar (Name "n")) (RefVar (Name "m")))
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
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

projectedProposition :: GrammarV1Proposition
projectedProposition =
  GrammarV1RelationProposition
    (Located syntheticSpan
      (GrammarV1ProjectionExpression
        (Located syntheticSpan (simpleNameExpression "n"))
        (Located syntheticSpan "field")))
    (Located syntheticSpan GrammarV1EqualRelation)
    (Located syntheticSpan (simpleNameExpression "n"))

arithmeticProposition :: GrammarV1Proposition
arithmeticProposition =
  GrammarV1RelationProposition
    (Located syntheticSpan
      (GrammarV1BinaryExpression
        (Located syntheticSpan (simpleNameExpression "n"))
        (Located syntheticSpan GrammarV1Add)
        (Located syntheticSpan (GrammarV1IntegerExpression "1"))))
    (Located syntheticSpan GrammarV1EqualRelation)
    (Located syntheticSpan (simpleNameExpression "m"))

simpleNameExpression :: Text.Text -> GrammarV1Expression
simpleNameExpression name =
  GrammarV1NameExpression
    (GrammarV1StaticReference (GrammarV1QualifiedName [name]) [])
    []

source :: Text.Text
source = Text.unlines
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
  , "claim Consumed = spent == n;"
  , "claim TruthLeaf = true;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
