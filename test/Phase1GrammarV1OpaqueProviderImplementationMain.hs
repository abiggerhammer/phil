{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusingError (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.ProviderQualification
  ( ProviderOperationKey (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Control (..)
  , Proposition (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProviderImplementationSurface
  ( GrammarV1CheckedOpaqueProviderImplementationSurface (..)
  , GrammarV1CheckedProviderImplementationItem (..)
  , GrammarV1CheckedProviderImplementationSurface (..)
  , GrammarV1ProviderImplementationSurfaceError (..)
  , grammarV1CheckedClosedOpaqueProviderImplementationSurface
  , grammarV1CheckedClosedProviderImplementationSurface
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
    , test "SURF-008 closed ordinary provider implementation preserves exact source item semantics"
        closedProviderImplementationSurface
    , test "SURF-008 ordinary provider implementation rename is presentation-only under supplied stable identity"
        providerImplementationRenameIsNonsemantic
    , test "SURF-008 ordinary provider proposition failures remain semantic rejections"
        providerImplementationFocusingFailure
    , test "SURF-008 ordinary provider operation body failures come from production checking"
        providerImplementationBodyFailure
    , test "SURF-008 duplicate ordinary provider operation spellings remain visible before qualification"
        providerImplementationDuplicateVisibility
    , test "SURF-008 richer ordinary provider implementation forms remain fail-closed"
        providerImplementationCompetenceBoundaries
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

closedProviderImplementationSurface :: Either String ()
closedProviderImplementationSurface = do
  declaration <- onlyProviderImplementation $ Text.unlines
    [ "provider implementation MemStore satisfies contracts.Store {"
    , "  operation ping satisfies api.Ping {"
    , "    unit;"
    , "    return true;"
    , "  }"
    , "  law coherent = true;"
    , "  lifecycle alive = false;"
    , "}"
    ]
  let expected = GrammarV1CheckedProviderImplementationSurface
        { checkedProviderImplementationDeclarationKey = providerDeclarationKey
        , checkedProviderImplementationDefinitionRevision = providerDefinitionRevision
        , checkedProviderImplementationContractReference =
            ReferencedGenericStaticActual "contracts.Store"
        , checkedProviderImplementationItems =
            [ GrammarV1CheckedProviderImplementationOperation
                (ProviderOperationKey "ping")
                (ReferencedGenericStaticActual "api.Ping")
                [Return TyBool]
            , GrammarV1CheckedProviderImplementationLaw "coherent" Truth []
            , GrammarV1CheckedProviderImplementationLifecycle "alive" Falsehood []
            ]
        }
  assert
    ( grammarV1CheckedClosedProviderImplementationSurface
        emptyStaticContext
        providerDeclarationKey
        providerDefinitionRevision
        declaration
        == Just (Right expected)
    )
    "ordinary provider implementation changed item order, unresolved identities, proposition semantics, or body controls"

providerImplementationRenameIsNonsemantic :: Either String ()
providerImplementationRenameIsNonsemantic = do
  first <- onlyProviderImplementation
    "provider implementation MemStore satisfies Store { operation ping satisfies Ping { return unit; } }"
  renamed <- onlyProviderImplementation
    "provider implementation RenamedPresentation satisfies Store { operation ping satisfies Ping { return unit; } }"
  let project = grammarV1CheckedClosedProviderImplementationSurface
        emptyStaticContext providerDeclarationKey providerDefinitionRevision
  assert (project first == project renamed)
    "ordinary provider implementation display-name change leaked into stable semantic identity"

providerImplementationFocusingFailure :: Either String ()
providerImplementationFocusingFailure = do
  declaration <- onlyProviderImplementation $ Text.unlines
    [ "provider implementation BadLaw satisfies Store {"
    , "  operation ping satisfies Ping { return unit; }"
    , "  law bad = Missing();"
    , "}"
    ]
  let actual = grammarV1CheckedClosedProviderImplementationSurface
        emptyStaticContext
        providerDeclarationKey
        providerDefinitionRevision
        declaration
  assert
    ( actual
        == Just
          (Left
            (GrammarV1ProviderImplementationFocusingError
              (UnknownClaim "Missing")))
    )
    ("ordinary provider proposition failure did not preserve Core focusing rejection: " <> show actual)

providerImplementationBodyFailure :: Either String ()
providerImplementationBodyFailure = do
  declaration <- onlyProviderImplementation $ Text.unlines
    [ "provider implementation BadBody satisfies Store {"
    , "  operation ping satisfies Ping {"
    , "    return true;"
    , "    unit;"
    , "  }"
    , "}"
    ]
  case grammarV1CheckedClosedProviderImplementationSurface
      emptyStaticContext
      providerDeclarationKey
      providerDefinitionRevision
      declaration of
    Just
      (Left
        (GrammarV1ProviderImplementationBodyError
          (ProviderOperationKey "ping")
          surfaceError)) ->
      assert (surfaceErrorClass surfaceError == ControlAfterTerminal)
        "provider operation body lost production ControlAfterTerminal rejection"
    other -> Left
      ("provider operation statement-after-return did not fail through production checking: " <> show other)

providerImplementationDuplicateVisibility :: Either String ()
providerImplementationDuplicateVisibility = do
  declaration <- onlyProviderImplementation $ Text.unlines
    [ "provider implementation Duplicate satisfies Store {"
    , "  operation access satisfies Reader { return unit; }"
    , "  operation access satisfies Writer { return unit; }"
    , "}"
    ]
  case grammarV1CheckedClosedProviderImplementationSurface
      emptyStaticContext
      providerDeclarationKey
      providerDefinitionRevision
      declaration of
    Just (Right checked) ->
      assert
        ( checkedProviderImplementationItems checked
            == [ GrammarV1CheckedProviderImplementationOperation
                   (ProviderOperationKey "access")
                   (ReferencedGenericStaticActual "Reader")
                   [Return TyUnit]
               , GrammarV1CheckedProviderImplementationOperation
                   (ProviderOperationKey "access")
                   (ReferencedGenericStaticActual "Writer")
                   [Return TyUnit]
               ]
        )
        "duplicate provider operation spelling was normalized before competent qualification"
    other -> Left ("duplicate ordinary provider surface did not check: " <> show other)

providerImplementationCompetenceBoundaries :: Either String ()
providerImplementationCompetenceBoundaries = do
  generic <- onlyProviderImplementation
    "provider implementation Generic[T : Type] satisfies Store { operation ping satisfies Ping { return unit; } }"
  required <- onlyProviderImplementation
    "provider implementation Required requires { proposition true; } satisfies Store { operation ping satisfies Ping { return unit; } }"
  specializedTarget <- onlyProviderImplementation
    "provider implementation SpecializedTarget satisfies Store[U32] { operation ping satisfies Ping { return unit; } }"
  structuredTarget <- onlyProviderImplementation
    "provider implementation StructuredTarget satisfies U8 { operation ping satisfies Ping { return unit; } }"
  specializedOperation <- onlyProviderImplementation
    "provider implementation SpecializedOperation satisfies Store { operation ping satisfies Ping[U32] { return unit; } }"
  structuredOperation <- onlyProviderImplementation
    "provider implementation StructuredOperation satisfies Store { operation ping satisfies U8 { return unit; } }"
  nameBody <- onlyProviderImplementation
    "provider implementation NameBody satisfies Store { operation ping satisfies Ping { return missing; } }"
  let project = grammarV1CheckedClosedProviderImplementationSurface
        emptyStaticContext providerDeclarationKey providerDefinitionRevision
  mapM_ (\(label, declaration) ->
    assert (project declaration == Nothing)
      (label <> " escaped the bounded ordinary-provider implementation competence wall"))
    [ ("generic implementation", generic)
    , ("requirement-bearing implementation", required)
    , ("specialized provider target", specializedTarget)
    , ("structured provider target", structuredTarget)
    , ("specialized operation reference", specializedOperation)
    , ("structured operation reference", structuredOperation)
    , ("name-bearing operation body", nameBody)
    ]

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

onlyProviderImplementation
  :: Text.Text
  -> Either String GrammarV1ProviderImplementationDecl
onlyProviderImplementation source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-provider-implementation" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProviderImplementationDeclaration declaration -> Right declaration
      other -> Left ("expected ordinary provider implementation, got " <> show other)
    declarations -> Left
      ("expected one ordinary provider implementation, got " <> show (length declarations))

declarationKey :: DeclarationKey
declarationKey = DeclarationKey "provider.opaque.remote-store"

definitionRevision :: DefinitionRevision
definitionRevision = DefinitionRevision "provider.opaque.remote-store.impl.v1"

providerDeclarationKey :: DeclarationKey
providerDeclarationKey = DeclarationKey "provider.implementation.mem-store"

providerDefinitionRevision :: DefinitionRevision
providerDefinitionRevision = DefinitionRevision "provider.implementation.mem-store.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
