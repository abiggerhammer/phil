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
    [ test "SURF-008 binding-aware Bytes routing preserves richer Nat expressions and sort competence"
        boundBytesPreserveRicherNatExpressions
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

boundBytesPreserveRicherNatExpressions :: Either String ()
boundBytesPreserveRicherNatExpressions = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "u" Unrestricted (TyUInt 32) state2
  state4 <- bind "flag" Unrestricted TyBool state3
  state5 <- bind "bytes" Unrestricted (TyBytes (RefNat 4)) state4
  state6 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state5
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state6
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-bytes" source
  actual <- mapM (boundType state) (grammarV1TopLevelDecls sourceFile)
  let n = RefVar (Name "n")
      u = RefVar (Name "u")
      bytes = RefVar (Name "bytes")
      expected =
        [ Just (TyBytes n)
        , Just (TyBytes (RefNat 7))
        , Just (TyBytes n)
        , Just (TyBytes (RefAdd n (RefNat 2)))
        , Just (TyBytes (RefSub n (RefNat 1)))
        , Just (TyBytes (RefScale 2 n))
        , Just (TyBytes (RefScale 2 n))
        , Just (TyBytes (RefLen bytes))
        , Just (TyBytes (RefToNat u))
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
        , Nothing
        ]
  assert (actual == expected) $
    "binding-aware Bytes routing changed a verified Nat expression or accepted a wrong-sort/unresolved form: " <> show actual

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
  , "type Literal = Bytes[7];"
  , "type Grouped = Bytes[(n)];"
  , "type Add = Bytes[n + 2];"
  , "type Sub = Bytes[n - 1];"
  , "type ScaleLeft = Bytes[2 * n];"
  , "type ScaleRight = Bytes[n * 2];"
  , "type Length = Bytes[len(bytes)];"
  , "type ExplicitToNat = Bytes[toNat(u)];"
  , "type UIntWrong = Bytes[u];"
  , "type BoolWrong = Bytes[flag];"
  , "type MixedSortRaw = Bytes[n + u];"
  , "type Unknown = Bytes[missing];"
  , "type Qualified = Bytes[pkg.n];"
  , "type Specialized = Bytes[n[U32]];"
  , "type Called = Bytes[n(1)];"
  , "type Projected = Bytes[(n).field];"
  , "type Consumed = Bytes[spent];"
  , "type SymbolicMultiply = Bytes[n * m];"
  , "type NotBytes = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
