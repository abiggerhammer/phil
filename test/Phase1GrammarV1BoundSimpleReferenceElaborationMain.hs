{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
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
import Phil.Surface.GrammarV1.BoundRef (grammarV1BoundRefTerm)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 binding-aware simple reference routing is exact and live"
        boundSimpleReferencesAreExact
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

boundSimpleReferencesAreExact :: Either String ()
boundSimpleReferencesAreExact = do
  live <- mapLeft show $
    insertBindingMeta
      syntheticSpan
      "n"
      (BindingMeta Unrestricted (TyUInt 32) PlainShape)
      emptySurfaceState
  withSpent <- mapLeft show $
    insertBindingMeta
      syntheticSpan
      "spent"
      (BindingMeta Affine (TyUInt 32) PlainShape)
      live
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" withSpent
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-simple-ref" source
  actual <- mapM (boundBytesIndex state) (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "binding-aware simple reference routing accepted an unresolved or consumed source form: " <> show actual
  where
    expected =
      [ Just (RefVar (Name "n"))
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      , Nothing
      ]

boundBytesIndex
  :: SurfaceState
  -> Located GrammarV1TopLevelDecl
  -> Either String (Maybe RefTerm)
boundBytesIndex state (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      case locatedValue (grammarV1TypeAliasTarget aliasDecl) of
        GrammarV1BytesType expression -> Right (grammarV1BoundRefTerm state expression)
        other -> Left ("expected Bytes type alias, got " <> show other)
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type Live = Bytes[n];"
  , "type Unknown = Bytes[missing];"
  , "type Qualified = Bytes[pkg.n];"
  , "type Specialized = Bytes[n[U32]];"
  , "type Called = Bytes[n(1)];"
  , "type Projected = Bytes[(n).field];"
  , "type Consumed = Bytes[spent];"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
