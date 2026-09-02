{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
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
import Phil.Surface.GrammarV1.BoundRefExpression
  ( grammarV1BoundRefExpression
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 binding-aware Grammar-v1 refinement expressions preserve exact Core structure"
        boundRefExpressionsPreserveStructure
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

boundRefExpressionsPreserveStructure :: Either String ()
boundRefExpressionsPreserveStructure = do
  state1 <- bind "n" (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "bytes" (TyBytes (RefNat 8)) state2
  state4 <- bind "word" (TyUInt 16) state3
  state <- bind "flag" TyBool state4
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-ref-expressions" source
  actual <- mapM (refExpression state) (grammarV1TopLevelDecls sourceFile)
  let n = RefVar (Name "n")
      m = RefVar (Name "m")
      bytes = RefVar (Name "bytes")
      word = RefVar (Name "word")
      expected =
        [ Just (RefNat 7)
        , Just n
        , Just n
        , Just (RefAdd n (RefNat 2))
        , Just (RefSub n (RefNat 1))
        , Just (RefScale 3 n)
        , Just (RefScale 3 n)
        , Just (RefLen bytes)
        , Just (RefToNat word)
        , Just (RefAdd n word)
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "refinement-expression composition changed structure or invented an unsupported interpretation: " <> show actual
  assert (m /= n) "test fixture accidentally collapsed distinct bindings"

refExpression
  :: SurfaceState
  -> Located GrammarV1TopLevelDecl
  -> Either String (Maybe RefTerm)
refExpression state (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      case locatedValue (grammarV1TypeAliasTarget aliasDecl) of
        GrammarV1BytesType expression ->
          Right (grammarV1BoundRefExpression state expression)
        other -> Left ("expected Bytes type alias target, got " <> show other)
    other -> Left ("expected type alias declaration, got " <> show other)

bind :: Text.Text -> Ty -> SurfaceState -> Either String SurfaceState
bind name ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta Unrestricted ty PlainShape) state

source :: Text.Text
source = Text.unlines
  [ "type Literal = Bytes[7];"
  , "type Live = Bytes[n];"
  , "type Grouped = Bytes[(n)];"
  , "type Add = Bytes[n + 2];"
  , "type Sub = Bytes[n - 1];"
  , "type LeftScale = Bytes[3 * n];"
  , "type RightScale = Bytes[n * 3];"
  , "type Length = Bytes[len(bytes)];"
  , "type ExplicitToNat = Bytes[toNat(word)];"
  , "type MixedSortRaw = Bytes[n + word];"
  , "type Unknown = Bytes[n + missing];"
  , "type SymbolicScale = Bytes[n * m];"
  , "type Projected = Bytes[(bytes).length];"
  , "type OrdinaryCall = Bytes[f(n)];"
  , "type SpecializedLen = Bytes[len[U8](bytes)];"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
