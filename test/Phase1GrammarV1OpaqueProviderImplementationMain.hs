{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProviderImplementationSurface
  ( GrammarV1CheckedOpaqueProviderImplementationSurface (..)
  , grammarV1CheckedClosedOpaqueProviderImplementationSurface
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed opaque provider implementation preserves stable identity and unresolved contract reference"
        closedOpaqueProviderSurface
    , test "SURF-008 opaque provider implementation rename is presentation-only under supplied stable identity"
        opaqueProviderRenameIsNonsemantic
    , test "SURF-008 richer opaque provider implementation headers remain fail-closed"
        opaqueProviderCompetenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedOpaqueProviderSurface :: Either String ()
closedOpaqueProviderSurface = do
  declaration <- onlyOpaqueProvider
    "opaque provider implementation RemoteStore satisfies contracts.Store;"
  let expected = GrammarV1CheckedOpaqueProviderImplementationSurface
        { checkedOpaqueProviderDeclarationKey = declarationKey
        , checkedOpaqueProviderDefinitionRevision = definitionRevision
        , checkedOpaqueProviderContractReference =
            ReferencedGenericStaticActual "contracts.Store"
        }
  assert
    ( grammarV1CheckedClosedOpaqueProviderImplementationSurface
        declarationKey definitionRevision declaration
        == Just expected
    )
    "closed opaque provider implementation changed stable identity or contract reference"

opaqueProviderRenameIsNonsemantic :: Either String ()
opaqueProviderRenameIsNonsemantic = do
  first <- onlyOpaqueProvider
    "opaque provider implementation RemoteStore satisfies contracts.Store;"
  renamed <- onlyOpaqueProvider
    "opaque provider implementation RenamedPresentation satisfies contracts.Store;"
  let project = grammarV1CheckedClosedOpaqueProviderImplementationSurface
        declarationKey definitionRevision
  assert (project first == project renamed)
    "opaque provider source display-name change leaked into stable semantic identity"

opaqueProviderCompetenceBoundaries :: Either String ()
opaqueProviderCompetenceBoundaries = do
  specialized <- onlyOpaqueProvider
    "opaque provider implementation Specialized satisfies Store[U32];"
  structured <- onlyOpaqueProvider
    "opaque provider implementation Structured satisfies U8;"
  generic <- onlyOpaqueProvider
    "opaque provider implementation Generic[T : Type] satisfies Store;"
  required <- onlyOpaqueProvider
    "opaque provider implementation Required requires { proposition true; } satisfies Store;"
  let project = grammarV1CheckedClosedOpaqueProviderImplementationSurface
        declarationKey definitionRevision
  assert (project specialized == Nothing)
    "specialized opaque-provider target was flattened to its base spelling"
  assert (project structured == Nothing)
    "structured opaque-provider satisfaction type was reinterpreted as a provider reference"
  assert (project generic == Nothing)
    "generic opaque provider implementation escaped the closed competence wall"
  assert (project required == Nothing)
    "requirement-bearing opaque provider implementation escaped the closed competence wall"

onlyOpaqueProvider
  :: Text.Text
  -> Either String GrammarV1OpaqueProviderImplementationDecl
onlyOpaqueProvider source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-opaque-provider" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1OpaqueProviderImplementationDeclaration declaration -> Right declaration
      other -> Left ("expected opaque provider implementation, got " <> show other)
    declarations -> Left
      ("expected one opaque provider implementation, got " <> show (length declarations))

declarationKey :: DeclarationKey
declarationKey = DeclarationKey "provider.opaque.remote-store"

definitionRevision :: DefinitionRevision
definitionRevision = DefinitionRevision "provider.opaque.remote-store.impl.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
