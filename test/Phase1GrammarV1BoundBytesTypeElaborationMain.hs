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
  , moveVariable
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundBytesType (grammarV1BoundBytesType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 binding-aware Bytes routing requires a live Nat-sorted name"
        boundBytesRequiresLiveNat
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

boundBytesRequiresLiveNat :: Either String ()
boundBytesRequiresLiveNat = do
  withNat <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  withUInt <- bind "u" Unrestricted (TyUInt 32) withNat
  withBool <- bind "flag" Unrestricted TyBool withUInt
  withSpent <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) withBool
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" withSpent
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-bytes" source
  actual <- mapM (boundType state) (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "binding-aware Bytes routing accepted a wrong-sort, unresolved, consumed, or non-bound form: " <> show actual
  where
    expected =
      [ Just (TyBytes (RefVar (Name "n")))
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

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta
      syntheticSpan
      name
      (BindingMeta mode ty PlainShape)
      state

boundType :: SurfaceState -> Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
boundType state (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1BoundBytesType state (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type LiveNat = Bytes[n];"
  , "type UIntWrong = Bytes[u];"
  , "type BoolWrong = Bytes[flag];"
  , "type Unknown = Bytes[missing];"
  , "type Qualified = Bytes[pkg.n];"
  , "type Specialized = Bytes[n[U32]];"
  , "type Called = Bytes[n(1)];"
  , "type Projected = Bytes[(n).field];"
  , "type Consumed = Bytes[spent];"
  , "type Literal = Bytes[7];"
  , "type NotBytes = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
