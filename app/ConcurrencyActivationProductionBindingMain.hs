{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.ConcurrencyActivationCertification
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessParticipants
import Phil.Core.Protocol
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified activation and participant composition accepts" certifiedCompositionAccepts
    , test "ambient activation preserves native diagnostic precedence" ambientNativePrecedence
    , test "duplicate restricted owner preserves native diagnostic precedence" duplicateRestrictedNativePrecedence
    , test "cross-process direct stateful alias preserves native diagnostic precedence" directStatefulNativePrecedence
    , test "empty native population fails closed at kernel boundary" emptyPopulationFailsClosed
    , test "mismatched ProcessNetwork map key fails closed at kernel boundary" mismatchedProcessKeyFailsClosed
    , test "injected activation fact disagreement fails closed" injectedActivationDisagreementFailsClosed
    , test "certified participant classification accepts internal plus external" certifiedParticipantAccepts
    , test "missing participant classification preserves native diagnostic precedence" missingParticipantNativePrecedence
    , test "empty role sentinel fails closed after native success" emptyRoleSentinelFailsClosed
    , test "injected participant fact disagreement fails closed" injectedParticipantDisagreementFailsClosed
    , test "outer certified conjunction disagreement fails closed" injectedCertifiedDisagreementFailsClosed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " <> label) >> pure True
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

certifiedCompositionAccepts :: Either String ()
certifiedCompositionAccepts = do
  graph <- mapLeft show rootGraph
  network <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let (processA, processB) = processKeys network
      contracts =
        [ ProcessActivationContract processA [ownedBinding "owner-a" "a"]
        , ProcessActivationContract processB [ownedBinding "owner-b" "b"]
        ]
      declarations =
        [ ParticipantDeclaration roleA (InternalParticipantTarget targetA)
        , ParticipantDeclaration roleB ExternalParticipantTarget
        ]
  result <- mapLeft show $
    certifyConcurrencyActivation graph network contracts [roleA, roleB] declarations
  assert
    (all ((== Active) . processOccurrenceActivation)
      (Map.elems (processNetworkPopulation (certifiedActivationNetwork result))))
    "certified composition did not retain exact active population"

ambientNativePrecedence :: Either String ()
ambientNativePrecedence = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      ambient = (ownedBinding "ambient" "host")
        { activationCheckedTypeMode = CheckedTypeMode (TyOpaque "HostHandle") Unrestricted
        , activationBindingOrigin = AmbientActivationOrigin "host registry"
        , activationReachability = ExtensionalImmutableReachability
        }
  case activateProcessStateCertified network
      [ ProcessActivationContract processA [ambient]
      , ProcessActivationContract processB []
      ] of
    Left (ConcurrencyActivationNativeError
      (AmbientActivationBinding actualProcess (Name "host") detail)) -> do
        assert (actualProcess == processA) "ambient diagnostic named wrong process"
        assert (detail == "host registry") "ambient diagnostic lost source detail"
    other -> Left ("native ambient diagnostic was not preserved: " <> show other)

duplicateRestrictedNativePrecedence :: Either String ()
duplicateRestrictedNativePrecedence = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      occurrence = ActivationOccurrenceKey "same-owner"
      first = ownedBindingFrom occurrence "left"
      second = ownedBindingFrom occurrence "right"
  case activateProcessStateCertified network
      [ ProcessActivationContract processA [first]
      , ProcessActivationContract processB [second]
      ] of
    Left (ConcurrencyActivationNativeError
      (DuplicateRestrictedActivationOccurrence actual firstProcess _ secondProcess _)) -> do
        assert (actual == occurrence) "duplicate-owner diagnostic changed occurrence identity"
        assert (firstProcess == processA && secondProcess == processB)
          "duplicate-owner diagnostic changed process identity"
    other -> Left ("native duplicate-owner diagnostic was not preserved: " <> show other)

directStatefulNativePrecedence :: Either String ()
directStatefulNativePrecedence = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      shared = ActivationOccurrenceKey "shared-stateful"
      first = directUnrestrictedBinding shared "left"
      second = directUnrestrictedBinding shared "right"
  case activateProcessStateCertified network
      [ ProcessActivationContract processA [first]
      , ProcessActivationContract processB [second]
      ] of
    Left (ConcurrencyActivationNativeError
      (CrossProcessDirectStatefulAlias actual firstProcess _ secondProcess _)) -> do
        assert (actual == shared) "direct-stateful diagnostic changed occurrence identity"
        assert (firstProcess == processA && secondProcess == processB)
          "direct-stateful diagnostic changed process identity"
    other -> Left ("native direct-stateful diagnostic was not preserved: " <> show other)

emptyPopulationFailsClosed :: Either String ()
emptyPopulationFailsClosed = do
  network <- baseNetwork
  let emptyNetwork = network { processNetworkPopulation = Map.empty }
  case activateProcessStateCertified emptyNetwork [] of
    Left (ConcurrencyActivationKernelDisagreement facts) ->
      assert (not (activationPopulationValid facts))
        "empty population disagreement did not identify population validity"
    other -> Left ("empty population did not fail closed: " <> show other)

mismatchedProcessKeyFailsClosed :: Either String ()
mismatchedProcessKeyFailsClosed = do
  network <- baseNetwork
  let population = processNetworkPopulation network
      (firstKey, firstOccurrence) = Map.findMin population
      malformed = network
        { processNetworkPopulation = Map.insert firstKey
            (firstOccurrence { processOccurrenceKey = ProcessKey "wrong-inner-key" })
            population
        }
      contracts =
        [ ProcessActivationContract processKey []
        | processKey <- Map.keys population
        ]
  case activateProcessStateCertified malformed contracts of
    Left (ConcurrencyActivationKernelDisagreement facts) ->
      assert (not (activationPopulationValid facts))
        "mismatched map/occurrence key did not invalidate reflected population"
    other -> Left ("mismatched ProcessKey did not fail closed: " <> show other)

injectedActivationDisagreementFailsClosed :: Either String ()
injectedActivationDisagreementFailsClosed =
  case verifyActivationContextKernelFacts ActivationContextKernelFacts
      { activationPopulationValid = True
      , activationBindingsExplicit = True
      , activationBindingProcessesActivated = True
      , activationRestrictedBindingsExact = True
      , activationNoInventedRestrictedOwner = False
      , activationDirectStatefulBindingsExact = True
      , activationNoInventedDirectStatefulOwner = True
      } of
    Left (ConcurrencyActivationKernelDisagreement _) -> Right ()
    other -> Left ("injected activation disagreement was accepted: " <> show other)

certifiedParticipantAccepts :: Either String ()
certifiedParticipantAccepts = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  checked <- mapLeft show $ checkParticipantClassificationsCertified
    graph network [roleA, roleB]
    [ ParticipantDeclaration roleA (InternalParticipantTarget targetA)
    , ParticipantDeclaration roleB ExternalParticipantTarget
    ]
  assert (Map.keysSet (participantClassifications checked) == Map.keysSet (Map.fromList
    [(roleA, ()), (roleB, ())]))
    "certified participant classification changed exact role domain"

missingParticipantNativePrecedence :: Either String ()
missingParticipantNativePrecedence = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  case checkParticipantClassificationsCertified
      graph network [roleA, roleB]
      [ParticipantDeclaration roleA (InternalParticipantTarget targetA)] of
    Left (ConcurrencyParticipantNativeError (MissingParticipantClassification actual)) ->
      assert (actual == roleB) "missing-participant diagnostic named wrong role"
    other -> Left ("native missing-participant diagnostic was not preserved: " <> show other)

emptyRoleSentinelFailsClosed :: Either String ()
emptyRoleSentinelFailsClosed = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  let emptyRole = ProtocolRoleOccurrence
        (ProtocolInstanceRevision "")
        (ProtocolRoleKey "")
  case checkParticipantClassificationsCertified
      graph network [emptyRole]
      [ParticipantDeclaration emptyRole ExternalParticipantTarget] of
    Left (ConcurrencyParticipantKernelDisagreement facts) ->
      assert (not (participantNoEmptyRole facts))
        "empty role sentinel disagreement did not identify no-empty-role fact"
    other -> Left ("empty role sentinel did not fail closed: " <> show other)

injectedParticipantDisagreementFailsClosed :: Either String ()
injectedParticipantDisagreementFailsClosed =
  case verifyParticipantClassificationKernelFacts ParticipantClassificationKernelFacts
      { participantClassificationExact = True
      , participantInternalActivated = True
      , participantInternalStatic = False
      , participantNoEmptyRole = True
      } of
    Left (ConcurrencyParticipantKernelDisagreement _) -> Right ()
    other -> Left ("injected participant disagreement was accepted: " <> show other)

injectedCertifiedDisagreementFailsClosed :: Either String ()
injectedCertifiedDisagreementFailsClosed =
  case verifyCertifiedConcurrencyActivationKernelFacts True False of
    Left (ConcurrencyActivationCertifiedKernelDisagreement True False) -> Right ()
    other -> Left ("injected outer certified disagreement was accepted: " <> show other)

ownedBinding :: Text -> Text -> ActivationBinding
ownedBinding occurrence name = ownedBindingFrom (ActivationOccurrenceKey occurrence) name

ownedBindingFrom :: ActivationOccurrenceKey -> Text -> ActivationBinding
ownedBindingFrom occurrence name = ActivationBinding
  { activationOccurrenceKey = occurrence
  , activationLocalName = Name name
  , activationCheckedTypeMode = CheckedTypeMode (TyOpaque "Owned") Linear
  , activationBindingOrigin = TargetParameterOrigin ("target." <> name)
  , activationReachability = DirectStatefulReachability occurrence
  , activationStartsSharedLoan = False
  }

directUnrestrictedBinding :: ActivationOccurrenceKey -> Text -> ActivationBinding
directUnrestrictedBinding occurrence name = ActivationBinding
  { activationOccurrenceKey = ActivationOccurrenceKey ("wrapper-" <> name)
  , activationLocalName = Name name
  , activationCheckedTypeMode = CheckedTypeMode (TyOpaque "SharedWrapper") Unrestricted
  , activationBindingOrigin = RootEntryOrigin ("root." <> name)
  , activationReachability = DirectStatefulReachability occurrence
  , activationStartsSharedLoan = False
  }

baseNetwork :: Either String ProcessNetwork
baseNetwork = do
  graph <- mapLeft show rootGraph
  mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey siteA)
     , deriveProcessKey rootRevision (processSiteKey siteB)
     )

roleA, roleB :: ProtocolRoleOccurrence
roleA = ProtocolRoleOccurrence protocolInstance (ProtocolRoleKey "client")
roleB = ProtocolRoleOccurrence protocolInstance (ProtocolRoleKey "server")

protocolInstance :: ProtocolInstanceRevision
protocolInstance = ProtocolInstanceRevision "protocol.conc.activation.v1"

rootGraph :: Either ArchitectureInstantiationError ArchitectureInstanceGraph
rootGraph = instantiateArchitecture rootKey rootSpec

rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ ArchitectureChildSpec slotA workerSpec
      , ArchitectureChildSpec slotB workerSpec
      ]
  , architectureNodeReferences = []
  }

workerSpec :: ArchitectureNodeSpec
workerSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "worker"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation
      { declarationDisplayName = label
      , declarationModulePath = []
      }
  , declarationKey = DeclarationKey ("decl-" <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "site-b") targetB

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
