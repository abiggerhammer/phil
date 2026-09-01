{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Proposition (..), RefTerm (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicClaimApplication)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic claim applications preserve exact Core atoms"
        intrinsicClaimApplicationsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicClaimApplicationsPreserveMeaning :: Either String ()
intrinsicClaimApplicationsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-claims" source
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

source :: Text.Text
source = Text.unlines
  [ "claim IntClaim = Ready(7, 0);"
  , "claim BoolClaim = Flag(true, false);"
  , "claim QualifiedClaim = Rules.Ready(1);"
  , "claim ContextClaim(x : U32) = Ready(x);"
  , "claim SpecializedClaim = Ready[U32](1);"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
