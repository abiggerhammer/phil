{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusingError (..)
  )
import Phil.Core.Generic
  ( GenericRequirement (..)
  , GenericStaticParameterKey (..)
  )
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.ProviderQualification
  ( ProviderOperationKey (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
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
import Phil.Surface.GrammarV1.GenericDischarge
  ( GrammarV1CheckedGenericRequirement (..)
  )
import Phil.Surface.GrammarV1.GenericProviderImplementationSurface
  ( GrammarV1CheckedGenericProviderImplementationSurface (..)
  , GrammarV1GenericProviderImplementationSurfaceError (..)
  , GrammarV1ResolvedGenericProviderParameter (..)
  , grammarV1CheckedGenericProviderImplementationSurface
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
    , test "SURF-008 generic provider implementations compose resolved schemas with the ordinary checked surface"
        genericProviderImplementationSurface
    , test "SURF-008 generic provider parameter evidence is exact and key-safe"
        genericProviderParameterEvidenceFailures
    , test "SURF-008 generic provider requirement evidence preserves exact Core-backed category"
        genericProviderRequirementEvidenceFailures
    , test "SURF-008 unsupported generic provider requirement categories remain fail-closed"
        genericProviderUnsupportedRequirement
    , test "SURF-008 generic provider bodies preserve ordinary production rejection"
        genericProviderBodyFailure
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

genericProviderImplementationSurface :: Either String ()
genericProviderImplementationSurface = do
  declaration <- onlyProviderImplementation genericProviderSource
  sourceParameter <- oneGenericParameter declaration
  sourceRequirements <- twoGenericRequirements declaration
  let stableParameter = GenericStaticParameter
        (GenericStaticParameterKey "provider.generic.type-parameter")
        GenericTypeKind
      parameterEvidence =
        [ GrammarV1ResolvedGenericProviderParameter sourceParameter stableParameter ]
      requirementEvidence = checkedGenericProviderRequirements sourceRequirements
  case grammarV1CheckedGenericProviderImplementationSurface
      emptyStaticContext
      genericProviderDeclarationKey
      genericProviderDefinitionRevision
      parameterEvidence
      requirementEvidence
      declaration of
    Just (Right checked) -> do
      assert
        (checkedGenericProviderParameters checked == [stableParameter])
        "generic provider parameter stable identity/kind was not preserved"
      assert
        (checkedGenericProviderRequirements checked == requirementEvidence)
        "generic provider checked requirements lost source order or focus evidence"
      let ordinary = checkedGenericProviderOrdinarySurface checked
      assert
        ( checkedProviderImplementationContractReference ordinary
            == ReferencedGenericStaticActual "contracts.Store"
        )
        "generic provider ordinary surface changed unresolved contract reference"
      assert
        ( checkedProviderImplementationItems ordinary
            == [ GrammarV1CheckedProviderImplementationOperation
                   (ProviderOperationKey "ping")
                   (ReferencedGenericStaticActual "api.Ping")
                   [Return TyUnit]
               , GrammarV1CheckedProviderImplementationLaw "coherent" Truth []
               ]
        )
        "generic provider ordinary item semantics diverged from the #637 path"
    other -> Left ("generic provider surface did not compose: " <> show other)

genericProviderParameterEvidenceFailures :: Either String ()
genericProviderParameterEvidenceFailures = do
  declaration <- onlyProviderImplementation
    "provider implementation Generic[T : Type] satisfies Store { operation ping satisfies Ping { return unit; } }"
  sourceParameter <- oneGenericParameter declaration
  otherDeclaration <- onlyProviderImplementation
    "provider implementation Other[U : Type] satisfies Store { operation ping satisfies Ping { return unit; } }"
  otherParameter <- oneGenericParameter otherDeclaration
  let key = GenericStaticParameterKey "provider.generic.parameter"
      valid = GrammarV1ResolvedGenericProviderParameter
        sourceParameter (GenericStaticParameter key GenericTypeKind)
      wrongSource = GrammarV1ResolvedGenericProviderParameter
        otherParameter (GenericStaticParameter key GenericTypeKind)
      wrongKind = GrammarV1ResolvedGenericProviderParameter
        sourceParameter (GenericStaticParameter key GenericMessageKind)
      project params = grammarV1CheckedGenericProviderImplementationSurface
        emptyStaticContext
        genericProviderDeclarationKey
        genericProviderDefinitionRevision
        params
        []
        declaration
  assert
    (project [] == Just (Left
      (GrammarV1GenericProviderParameterEvidenceCountMismatch 1 0)))
    "missing generic provider parameter evidence did not reject explicitly"
  case project [wrongSource] of
    Just (Left (GrammarV1GenericProviderParameterSourceMismatch 0 _ _)) -> Right ()
    other -> Left ("foreign generic provider parameter evidence was accepted: " <> show other)
  assert
    ( project [wrongKind]
        == Just
          (Left
            (GrammarV1GenericProviderParameterKindMismatch
              key GenericTypeKind GenericMessageKind))
    )
    "wrong-kind generic provider parameter evidence was accepted"
  assert
    (project [valid] /= Nothing)
    "valid generic provider parameter evidence lost structural competence"
  duplicateDeclaration <- onlyProviderImplementation
    "provider implementation Duplicate[T : Type, U : Type] satisfies Store { operation ping satisfies Ping { return unit; } }"
  case grammarV1ProviderImplementationGenericParams duplicateDeclaration of
    [firstParameter, secondParameter] ->
      let duplicateEvidence =
            [ GrammarV1ResolvedGenericProviderParameter
                firstParameter (GenericStaticParameter key GenericTypeKind)
            , GrammarV1ResolvedGenericProviderParameter
                secondParameter (GenericStaticParameter key GenericTypeKind)
            ]
      in assert
          ( grammarV1CheckedGenericProviderImplementationSurface
              emptyStaticContext
              genericProviderDeclarationKey
              genericProviderDefinitionRevision
              duplicateEvidence
              []
              duplicateDeclaration
              == Just (Left (GrammarV1DuplicateGenericProviderParameterKey key))
          )
          "duplicate stable generic provider parameter keys were accepted"
    params -> Left ("expected two generic provider parameters, got " <> show (length params))

genericProviderRequirementEvidenceFailures :: Either String ()
genericProviderRequirementEvidenceFailures = do
  declaration <- onlyProviderImplementation
    "provider implementation Required requires { proposition true; } satisfies Store { operation ping satisfies Ping { return unit; } }"
  sourceRequirement <- oneGenericRequirement declaration
  let providerKey = GenericStaticParameterKey "provider.foreign"
      wrongCategory = GrammarV1CheckedGenericRequirement
        { checkedGenericRequirementSource = sourceRequirement
        , checkedGenericRequirementCore =
            GenericProviderContractRequirement
              providerKey
              (InterfaceRevision "provider.foreign.v1")
        , checkedGenericRequirementFocusSteps = []
        }
      project evidence = grammarV1CheckedGenericProviderImplementationSurface
        emptyStaticContext
        genericProviderDeclarationKey
        genericProviderDefinitionRevision
        []
        evidence
        declaration
  assert
    ( project []
        == Just
          (Left
            (GrammarV1GenericProviderRequirementEvidenceCountMismatch 1 0))
    )
    "missing generic provider requirement evidence did not reject explicitly"
  assert
    ( project [wrongCategory]
        == Just
          (Left
            (GrammarV1GenericProviderRequirementCategoryMismatch
              0
              GenericPropositionCategory
              GenericProviderCategory))
    )
    "generic provider requirement evidence for the wrong category was accepted"

genericProviderUnsupportedRequirement :: Either String ()
genericProviderUnsupportedRequirement = do
  declaration <- onlyProviderImplementation
    "provider implementation Unsupported requires { callable C : CallableContract; } satisfies Store { operation ping satisfies Ping { return unit; } }"
  assert
    ( grammarV1CheckedGenericProviderImplementationSurface
        emptyStaticContext
        genericProviderDeclarationKey
        genericProviderDefinitionRevision
        []
        []
        declaration
        == Nothing
    )
    "non-Core-backed generic provider requirement category escaped competence wall"

genericProviderBodyFailure :: Either String ()
genericProviderBodyFailure = do
  declaration <- onlyProviderImplementation $ Text.unlines
    [ "provider implementation Generic[T : Type] satisfies Store {"
    , "  operation ping satisfies Ping {"
    , "    return true;"
    , "    unit;"
    , "  }"
    , "}"
    ]
  sourceParameter <- oneGenericParameter declaration
  let parameterEvidence =
        [ GrammarV1ResolvedGenericProviderParameter
            sourceParameter
            (GenericStaticParameter
              (GenericStaticParameterKey "provider.generic.type-parameter")
              GenericTypeKind)
        ]
  case grammarV1CheckedGenericProviderImplementationSurface
      emptyStaticContext
      genericProviderDeclarationKey
      genericProviderDefinitionRevision
      parameterEvidence
      []
      declaration of
    Just
      (Left
        (GrammarV1GenericProviderOrdinarySurfaceError
          (GrammarV1ProviderImplementationBodyError
            (ProviderOperationKey "ping")
            surfaceError))) ->
      assert (surfaceErrorClass surfaceError == ControlAfterTerminal)
        "generic provider body lost ordinary production ControlAfterTerminal rejection"
    other -> Left ("generic provider body failure did not preserve ordinary checker error: " <> show other)

checkedGenericProviderRequirements
  :: (Located GrammarV1GenericRequirement, Located GrammarV1GenericRequirement)
  -> [GrammarV1CheckedGenericRequirement]
checkedGenericProviderRequirements (propositionRequirement, providerRequirement) =
  [ GrammarV1CheckedGenericRequirement
      { checkedGenericRequirementSource = propositionRequirement
      , checkedGenericRequirementCore = GenericPropositionRequirement Truth
      , checkedGenericRequirementFocusSteps = []
      }
  , GrammarV1CheckedGenericRequirement
      { checkedGenericRequirementSource = providerRequirement
      , checkedGenericRequirementCore = GenericProviderContractRequirement
          (GenericStaticParameterKey "provider.generic.requirement-P")
          (InterfaceRevision "provider.generic.requirement-P.v1")
      , checkedGenericRequirementFocusSteps = []
      }
  ]

oneGenericParameter
  :: GrammarV1ProviderImplementationDecl
  -> Either String (Located GrammarV1GenericParam)
oneGenericParameter declaration =
  case grammarV1ProviderImplementationGenericParams declaration of
    [parameter] -> Right parameter
    parameters -> Left ("expected one generic provider parameter, got " <> show (length parameters))

oneGenericRequirement
  :: GrammarV1ProviderImplementationDecl
  -> Either String (Located GrammarV1GenericRequirement)
oneGenericRequirement declaration =
  case grammarV1ProviderImplementationRequirements declaration of
    [requirement] -> Right requirement
    requirements -> Left ("expected one generic provider requirement, got " <> show (length requirements))

twoGenericRequirements
  :: GrammarV1ProviderImplementationDecl
  -> Either String
      (Located GrammarV1GenericRequirement, Located GrammarV1GenericRequirement)
twoGenericRequirements declaration =
  case grammarV1ProviderImplementationRequirements declaration of
    [firstRequirement, secondRequirement] -> Right (firstRequirement, secondRequirement)
    requirements -> Left ("expected two generic provider requirements, got " <> show (length requirements))

genericProviderSource :: Text.Text
genericProviderSource = Text.unlines
  [ "provider implementation Generic[T : Type] requires {"
  , "  proposition true;"
  , "  provider P : ProviderContract;"
  , "} satisfies contracts.Store {"
  , "  operation ping satisfies api.Ping { return unit; }"
  , "  law coherent = true;"
  , "}"
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

genericProviderDeclarationKey :: DeclarationKey
genericProviderDeclarationKey = DeclarationKey "provider.implementation.generic-store"

genericProviderDefinitionRevision :: DefinitionRevision
genericProviderDefinitionRevision = DefinitionRevision "provider.implementation.generic-store.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
