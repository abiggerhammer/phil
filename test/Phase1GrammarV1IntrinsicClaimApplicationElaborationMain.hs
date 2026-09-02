{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
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
  , moveVariable
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundClaimApplication
  ( grammarV1BoundClaimApplication
  )
import Phil.Surface.GrammarV1.ClaimDeclaration
  ( grammarV1ClaimDeclaration
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicClaimApplication)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic claim applications preserve exact Core atoms"
        intrinsicClaimApplicationsPreserveMeaning
    , test "SURF-008 binding-aware claim arguments preserve richer verified term structure"
        boundClaimApplicationsPreserveMeaning
    , test "SURF-008 primitive Grammar-v1 claim declarations route to exact Core ClaimDecl semantics"
        claimDeclarationsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicClaimApplicationsPreserveMeaning :: Either String ()
intrinsicClaimApplicationsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-claims" intrinsicSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicClaimApplication propositions
      expected =
        [ Just (Atom "Ready" [RefNat 7, RefNat 0])
        , Just (Atom "Flag" [RefBool True, RefBool False])
        , Just (Atom "Rules.Ready" [RefNat 1])
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "claim application elaboration changed identity/arguments or accepted contextual specialization: " <> show actual

boundClaimApplicationsPreserveMeaning :: Either String ()
boundClaimApplicationsPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "u" Unrestricted (TyUInt 32) state2
  state4 <- bind "flag" Unrestricted TyBool state3
  state5 <- bind "bytes" Unrestricted (TyBytes (RefNat 8)) state4
  state6 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state5
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state6
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-claims" boundSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let n = RefVar (Name "n")
      m = RefVar (Name "m")
      u = RefVar (Name "u")
      bytes = RefVar (Name "bytes")
      actual = map (grammarV1BoundClaimApplication state) propositions
      expected =
        [ Just (Atom "Ready" [n, RefNat 1])
        , Just (Atom "Flag" [RefVar (Name "flag"), RefBool False])
        , Just (Atom "Rules.Ready" [n])
        , Just (Atom "Ready" [n])
        , Just (Atom "Ready" [RefAdd n (RefNat 1)])
        , Just (Atom "Ready" [RefSub n (RefNat 1)])
        , Just (Atom "Ready" [RefScale 2 n])
        , Just (Atom "Ready" [RefScale 2 n])
        , Just (Atom "Ready" [RefLen bytes])
        , Just (Atom "Ready" [RefToNat u])
        , Just (Atom "Ready" [RefAdd n u])
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
    "binding-aware claim application changed identity/arguments or invented an unsupported source form: " <> show actual
  assert (m /= n) "test fixture accidentally collapsed distinct bindings"

claimDeclarationsPreserveMeaning :: Either String ()
claimDeclarationsPreserveMeaning = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-claim-declarations" declarationSource
  declarations <- mapM claimDeclaration (grammarV1TopLevelDecls sourceFile)
  let x = RefVar (Name "x")
      ok = RefVar (Name "ok")
      actual = map grammarV1ClaimDeclaration declarations
      expected =
        [ Just
            ( "OpaqueFlag"
            , ClaimDecl
                { claimParameters = [(Name "flag", SortBool)]
                , claimDefinition = OpaqueClaim
                }
            )
        , Just
            ( "Positive"
            , ClaimDecl
                { claimParameters = [(Name "x", SortUInt 8)]
                , claimDefinition = TransparentClaim
                    (LessThan (RefNat 0) (RefToNat x))
                }
            )
        , Just
            ( "Mixed"
            , ClaimDecl
                { claimParameters =
                    [ (Name "x", SortUInt 8)
                    , (Name "ok", SortBool)
                    ]
                , claimDefinition = TransparentClaim
                    (Conjunction
                      (LessThan (RefToNat x) (RefNat 7))
                      (Atom "Ready" [ok]))
                }
            )
        , Just
            ( "NoParams"
            , ClaimDecl
                { claimParameters = []
                , claimDefinition = TransparentClaim Truth
                }
            )
        , Just
            ( "EmptyParams"
            , ClaimDecl
                { claimParameters = []
                , claimDefinition = TransparentClaim Truth
                }
            )
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "claim declaration routing changed name/parameter/body meaning or admitted a deferred declaration form: "
      <> show actual

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

claimDeclaration
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1ClaimDecl
claimDeclaration (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl -> Right claimDecl
    other -> Left ("expected claim declaration, got " <> show other)

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "claim IntClaim = Ready(7, 0);"
  , "claim BoolClaim = Flag(true, false);"
  , "claim QualifiedClaim = Rules.Ready(1);"
  , "claim ContextClaim(x : U32) = Ready(x);"
  , "claim SpecializedClaim = Ready[U32](1);"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "claim BoundNat = Ready(n, 1);"
  , "claim BoundBool = Flag(flag, false);"
  , "claim QualifiedClaim = Rules.Ready(n);"
  , "claim GroupedArg = Ready((n));"
  , "claim ArithmeticArg = Ready(n + 1);"
  , "claim SubtractionArg = Ready(n - 1);"
  , "claim ScaleLeftArg = Ready(2 * n);"
  , "claim ScaleRightArg = Ready(n * 2);"
  , "claim LengthArg = Ready(len(bytes));"
  , "claim ExplicitToNatArg = Ready(toNat(u));"
  , "claim MixedSortRaw = Ready(n + u);"
  , "claim Unknown = Ready(missing);"
  , "claim Consumed = Ready(spent);"
  , "claim SpecializedClaim = Ready[U32](n);"
  , "claim CalledArg = Ready(f(1));"
  , "claim ProjectedArg = Ready((n).field);"
  , "claim QualifiedArg = Ready(pkg.n);"
  , "claim SymbolicMultiply = Ready(n * m);"
  , "claim NonClaim = n == 1;"
  ]

declarationSource :: Text.Text
declarationSource = Text.unlines
  [ "claim OpaqueFlag(flag : Bool);"
  , "claim Positive(x : U8) = x > 0;"
  , "claim Mixed(x : U8, ok : Bool) = x < 7 and Ready(ok);"
  , "claim NoParams = true;"
  , "claim EmptyParams() = true;"
  , "claim UnitParam(x : Unit);"
  , "claim BytesParam(x : Bytes[4]);"
  , "claim NamedParam(x : Widget);"
  , "claim Generic[T : Type](x : U8);"
  , "claim Required requires { proposition true; } (x : U8);"
  , "claim Duplicate(x : U8, x : U8);"
  , "claim BadBody(x : U8) = missing < x;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
