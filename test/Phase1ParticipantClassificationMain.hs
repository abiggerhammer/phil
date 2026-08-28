{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Process
import Phil.Core.ProcessParticipants
import Phil.Core.Protocol
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-010 explicit internal and external classifications accept" explicitClassificationsAccept
    , test "CONC-010 missing classification does not imply external" missingClassificationRejects
    , test "CONC-010 duplicate role classification rejects" duplicateClassificationRejects
    , test "CONC-010 unknown internal target rejects" unknownInternalTargetRejects
    , test "CONC-010 unactivated executable target rejects" unactivatedTargetRejects
    , test "CONC-010 inactive process target rejects" inactiveProcessRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

explicitClassificationsAccept :: Either String ()
explicitClassificationsAccept = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  checked <- mapLeft show $ checkParticipantClassifications
    graph
    network
    [roleA, roleB]
    [ ParticipantDeclaration roleA (InternalParticipantTarget targetA)
    , ParticipantDeclaration roleB ExternalParticipantTarget
    ]
  let classifications = participantClassifications checked
      rootRevision = identityInstanceRevision (processNetworkRoot network)
      processA = deriveProcessKey rootRevision (processSiteKey siteA)
  case Map.lookup roleA classifications of
    Just (CheckedInternalParticipant actualRole actualTarget actualProcess) -> do
      assert (actualRole == roleA) "internal classification changed exact role occurrence"
      assert (actualTarget == targetA) "internal classification changed target occurrence"
      assert (actualProcess == processA) "internal classification lost exact ProcessKey"
    other -> Left ("expected checked internal participant, got " <> show other)
  case Map.lookup roleB classifications of
    Just (CheckedExternalParticipant actualRole) ->
      assert (actualRole == roleB)
        "external classification carried anything other than its exact role occurrence"
    other -> Left ("expected checked external participant, got " <> show other)

missingClassificationRejects :: Either String ()
missingClassificationRejects = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  case checkParticipantClassifications
      graph network [roleA, roleB]
      [ParticipantDeclaration roleA (InternalParticipantTarget targetA)] of
    Left (MissingParticipantClassification actualRole) ->
      assert (actualRole == roleB)
        "missing-classification rejection named wrong role"
    other -> Left ("missing role was silently externalized: " <> show other)

duplicateClassificationRejects :: Either String ()
duplicateClassificationRejects = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  case checkParticipantClassifications
      graph network [roleA]
      [ ParticipantDeclaration roleA (InternalParticipantTarget targetA)
      , ParticipantDeclaration roleA ExternalParticipantTarget
      ] of
    Left (DuplicateParticipantDeclaration actualRole) ->
      assert (actualRole == roleA)
        "ambiguous-classification rejection named wrong role"
    other -> Left ("ambiguous participant classification was accepted: " <> show other)

unknownInternalTargetRejects :: Either String ()
unknownInternalTargetRejects = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  let missing = InstanceKey "missing-worker"
  case checkParticipantClassifications
      graph network [roleA]
      [ParticipantDeclaration roleA (InternalParticipantTarget missing)] of
    Left (UnknownInternalParticipantTarget actualRole actualTarget) ->
      assert (actualRole == roleA && actualTarget == missing)
        "unknown-target rejection lost exact role/target identity"
    other -> Left ("unknown internal participant target was accepted: " <> show other)

unactivatedTargetRejects :: Either String ()
unactivatedTargetRejects = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  network <- mapLeft show $ activateRootProcesses network0
  case checkParticipantClassifications
      graph network [roleB]
      [ParticipantDeclaration roleB (InternalParticipantTarget targetB)] of
    Left (InternalParticipantTargetUnactivated actualRole actualTarget) ->
      assert (actualRole == roleB && actualTarget == targetB)
        "unactivated-target rejection lost exact role/target identity"
    other -> Left ("existing target without ProcessOccurrence was accepted: " <> show other)

inactiveProcessRejects :: Either String ()
inactiveProcessRejects = do
  graph <- mapLeft show rootGraph
  network <- mapLeft show $ elaborateProcessNetwork graph [siteA]
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
      processA = deriveProcessKey rootRevision (processSiteKey siteA)
  case checkParticipantClassifications
      graph network [roleA]
      [ParticipantDeclaration roleA (InternalParticipantTarget targetA)] of
    Left (InternalParticipantProcessNotActive actualRole actualProcess NotActivated) ->
      assert (actualRole == roleA && actualProcess == processA)
        "inactive-process rejection lost exact role/ProcessKey identity"
    other -> Left ("role bound to inactive process was accepted: " <> show other)

roleA, roleB :: ProtocolRoleOccurrence
roleA = ProtocolRoleOccurrence protocolInstance (ProtocolRoleKey "client")
roleB = ProtocolRoleOccurrence protocolInstance (ProtocolRoleKey "server")

protocolInstance :: ProtocolInstanceRevision
protocolInstance = ProtocolInstanceRevision "protocol.conc010.v1"

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

siteA :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA

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
