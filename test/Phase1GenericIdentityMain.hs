{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Generic
import Phil.Core.Static
  ( ArchitectureChildSpec (..)
  , ArchitectureNodeSpec (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InterfaceRevision (..)
  , OccurrenceSlotKey (..)
  , SemanticForm (..)
  , checkedArchitectureChildren
  , deriveDeclarationIdentity
  , instantiateArchitecture
  , lookupArchitectureInstance
  )
import Phil.Core.Syntax (Proposition (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "GEN-009 evidence replacement preserves semantic application" evidenceReplacementPreservesApplication
    , test "GEN-009 evidence replacement changes discharge lineage" evidenceReplacementChangesLineage
    , test "semantic evidence argument changes semantic application" semanticEvidenceArgumentChangesApplication
    , test "GEN-010 ordinary generic application is applicative" applicativeApplication
    , test "GEN-010 semantic argument order is nonsemantic" argumentOrderIsNonsemantic
    , test "duplicate semantic argument rejects" duplicateArgumentRejects
    , test "GEN-010 architecture repetition remains generative" architectureRepetitionRemainsGenerative
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

evidenceReplacementPreservesApplication :: Either String ()
evidenceReplacementPreservesApplication = do
  application <- applicationIdentity baseArguments
  recordA <- instantiationWithEvidence "proof.ordering.001"
  recordB <- instantiationWithEvidence "proof.ordering.002"
  let lineageA = deriveGenericDischargeLineage application definitionRevision recordA
      lineageB = deriveGenericDischargeLineage application definitionRevision recordB
  assert
    ( genericDischargeApplicationIdentity lineageA
        == genericDischargeApplicationIdentity lineageB )
    "changing discharge evidence changed semantic application identity"

evidenceReplacementChangesLineage :: Either String ()
evidenceReplacementChangesLineage = do
  application <- applicationIdentity baseArguments
  recordA <- instantiationWithEvidence "proof.ordering.001"
  recordB <- instantiationWithEvidence "proof.ordering.002"
  let lineageA = deriveGenericDischargeLineage application definitionRevision recordA
      lineageB = deriveGenericDischargeLineage application definitionRevision recordB
  assert (lineageA /= lineageB)
    "different accepted evidence did not change discharge lineage"

semanticEvidenceArgumentChangesApplication :: Either String ()
semanticEvidenceArgumentChangesApplication = do
  left <- applicationIdentity
    ((evidenceParameter, SemanticAtom "proof.ordering.001") : baseArguments)
  right <- applicationIdentity
    ((evidenceParameter, SemanticAtom "proof.ordering.002") : baseArguments)
  assert (left /= right)
    "identity-bearing semantic evidence argument was treated as discharge-only metadata"

applicativeApplication :: Either String ()
applicativeApplication = do
  first <- applicationIdentity baseArguments
  second <- applicationIdentity baseArguments
  assert (first == second)
    "equal ordinary generic applications became generative"

argumentOrderIsNonsemantic :: Either String ()
argumentOrderIsNonsemantic = do
  first <- applicationIdentity baseArguments
  second <- applicationIdentity (reverse baseArguments)
  assert (first == second)
    "semantic argument traversal order changed generic application identity"

duplicateArgumentRejects :: Either String ()
duplicateArgumentRejects =
  case deriveGenericApplicationIdentity
      genericDeclarationKey
      interfaceRevision
      [ (typeParameter, SemanticAtom "Blob")
      , (typeParameter, SemanticAtom "Blob")
      ] of
    Left (DuplicateGenericSemanticArgument key) ->
      assert (key == typeParameter) "duplicate diagnostic named wrong parameter"
    other -> Left ("duplicate semantic argument did not reject: " <> show other)

architectureRepetitionRemainsGenerative :: Either String ()
architectureRepetitionRemainsGenerative = do
  application <- applicationIdentity baseArguments
  graph <- mapLeft show $ instantiateArchitecture
    rootInstance
    (rootNode
      { architectureNodeChildren =
          [ ArchitectureChildSpec primarySlot (childNode application)
          , ArchitectureChildSpec backupSlot (childNode application)
          ]
      })
  root <- maybe
    (Left "root architecture occurrence missing")
    Right
    (lookupArchitectureInstance rootInstance graph)
  primary <- maybe
    (Left "primary child occurrence missing")
    Right
    (Map.lookup primarySlot (checkedArchitectureChildren root))
  backup <- maybe
    (Left "backup child occurrence missing")
    Right
    (Map.lookup backupSlot (checkedArchitectureChildren root))
  assert (primary /= backup)
    "equal generic application collapsed distinct architecture occurrences"

applicationIdentity
  :: [(GenericStaticParameterKey, SemanticForm)]
  -> Either String GenericApplicationIdentity
applicationIdentity arguments =
  mapLeft show $ deriveGenericApplicationIdentity
    genericDeclarationKey
    interfaceRevision
    arguments

instantiationWithEvidence :: String -> Either String GenericInstantiationRecord
instantiationWithEvidence evidenceId =
  mapLeft show $ checkGenericInstantiation
    strictGenericInstantiationPolicy
    (Set.singleton lawRequirement)
    [ ( lawRequirement
      , GenericSatisfiedByEvidence GenericEvidence
          { genericEvidenceProposition = orderingLaw
          , genericEvidenceIdentity = Text.pack evidenceId
          }
      )
    ]

childNode :: GenericApplicationIdentity -> ArchitectureNodeSpec
childNode application = ArchitectureNodeSpec
  { architectureNodeDeclaration = childDeclarationIdentity
  , architectureNodeStaticBindings = Map.singleton
      "generic-application"
      (genericApplicationSemanticForm application)
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

rootNode :: ArchitectureNodeSpec
rootNode = ArchitectureNodeSpec
  { architectureNodeDeclaration = rootDeclarationIdentity
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

rootDeclarationIdentity :: DeclarationIdentity
rootDeclarationIdentity = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "Root" ["phase1"]
  , declarationKey = DeclarationKey "decl.root"
  , declarationInterfaceSemantics = SemanticAtom "root-interface"
  , declarationDefinitionSemantics = SemanticAtom "root-definition"
  }

childDeclarationIdentity :: DeclarationIdentity
childDeclarationIdentity = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "Worker" ["phase1"]
  , declarationKey = DeclarationKey "decl.worker"
  , declarationInterfaceSemantics = SemanticAtom "worker-interface"
  , declarationDefinitionSemantics = SemanticAtom "worker-definition"
  }

rootInstance :: InstanceKey
rootInstance = InstanceKey "instance.root"

primarySlot, backupSlot :: OccurrenceSlotKey
primarySlot = OccurrenceSlotKey "primary"
backupSlot = OccurrenceSlotKey "backup"

genericDeclarationKey :: DeclarationKey
genericDeclarationKey = DeclarationKey "generic.map"

interfaceRevision :: InterfaceRevision
interfaceRevision = InterfaceRevision "generic.map.interface.v1"

definitionRevision :: DefinitionRevision
definitionRevision = DefinitionRevision "generic.map.definition.v1"

typeParameter, providerParameter, evidenceParameter :: GenericStaticParameterKey
typeParameter = GenericStaticParameterKey "T"
providerParameter = GenericStaticParameterKey "P"
evidenceParameter = GenericStaticParameterKey "ordering-proof"

baseArguments :: [(GenericStaticParameterKey, SemanticForm)]
baseArguments =
  [ (typeParameter, SemanticAtom "Blob")
  , (providerParameter, SemanticAtom "provider.compare.v1")
  ]

orderingLaw :: Proposition
orderingLaw = Atom "StrictWeakOrdering" []

lawRequirement :: GenericRequirement
lawRequirement = GenericPropositionRequirement orderingLaw

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
