{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Process
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-001 exact population is declaration-order independent" populationOrderIndependent
    , test "CONC-001 every process activates exactly once" activatesExactlyOnce
    , test "CONC-001 unknown target cannot enter population" unknownTargetRejects
    , test "CLOSURE-020 equal local process sites are scoped by owning architecture occurrence" nestedLocalSitesAreScoped
    , test "CLOSURE-020 duplicate local site within one owner rejects" duplicateNestedSiteRejects
    , test "CLOSURE-020 shared exact target cannot clone process population" sharedNestedTargetRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

populationOrderIndependent :: Either String ()
populationOrderIndependent = do
  graph <- mapLeft show rootGraph
  forward <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  reverseOrder <- mapLeft show $ elaborateProcessNetwork graph [siteB, siteA]
  assert
    (processNetworkPopulation forward == processNetworkPopulation reverseOrder)
    "process declaration order changed semantic population"
  assert
    (Map.size (processNetworkPopulation forward) == 2)
    "root did not produce exactly two process occurrences"
  let occurrences = Map.elems (processNetworkPopulation forward)
      targetKeys = map (identityInstanceKey . processOccurrenceTarget) occurrences
      ownerKeys = map (identityInstanceKey . processOccurrenceOwner) occurrences
  assert (targetA `elem` targetKeys && targetB `elem` targetKeys)
    "population did not retain both exact target occurrences"
  assert (all (== rootKey) ownerKeys)
    "root shorthand did not bind process sites to the exact root owner"
  assert
    (length (Map.keys (processNetworkPopulation forward)) == 2)
    "generative process sites did not produce distinct ProcessKeys"

activatesExactlyOnce :: Either String ()
activatesExactlyOnce = do
  graph <- mapLeft show rootGraph
  initial <- mapLeft show $ elaborateProcessNetwork graph [siteB, siteA]
  activated <- mapLeft show $ activateRootProcesses initial
  assert
    (all ((== Active) . processOccurrenceActivation)
      (Map.elems (processNetworkPopulation activated)))
    "root activation did not activate every process occurrence"
  case activateRootProcesses activated of
    Left (ProcessAlreadyActivated _) -> Right ()
    other -> Left ("reactivation did not reject: " <> show other)

unknownTargetRejects :: Either String ()
unknownTargetRejects = do
  graph <- mapLeft show rootGraph
  case elaborateProcessNetwork graph
    [ProcessDeclarationSite (ProcessSiteKey "missing-site") (InstanceKey "missing-target")] of
    Left (UnknownProcessTarget (ProcessSiteKey "missing-site") (InstanceKey "missing-target")) -> Right ()
    other -> Left ("unknown process target did not reject exactly: " <> show other)

nestedLocalSitesAreScoped :: Either String ()
nestedLocalSitesAreScoped = do
  graph <- mapLeft show nestedGraph
  forward <- mapLeft show $ elaborateProcessNetwork graph [nestedSiteLeft, nestedSiteRight]
  reverseOrder <- mapLeft show $ elaborateProcessNetwork graph [nestedSiteRight, nestedSiteLeft]
  let population = processNetworkPopulation forward
      occurrences = Map.elems population
      owners = Set.fromList (map (identityInstanceKey . processOccurrenceOwner) occurrences)
      targets = Set.fromList (map (identityInstanceKey . processOccurrenceTarget) occurrences)
      keys = Map.keysSet population
      expectedKeys = Set.fromList
        [ deriveScopedProcessKey cellLeftKey localRunSite
        , deriveScopedProcessKey cellRightKey localRunSite
        ]
  assert
    (population == processNetworkPopulation reverseOrder)
    "nested process population depends on occurrence enumeration order"
  assert (Map.size population == 2)
    "equal declaration-local process sites collided across nested instances"
  assert (owners == Set.fromList [cellLeftKey, cellRightKey])
    "nested process occurrence lost exact owning ArchitectureInstance identity"
  assert (targets == Set.fromList [nestedTargetLeft, nestedTargetRight])
    "nested process occurrence lost exact executable target identity"
  assert (keys == expectedKeys)
    "nested process keys were not scoped by owning InstanceKey"

duplicateNestedSiteRejects :: Either String ()
duplicateNestedSiteRejects = do
  graph <- mapLeft show nestedGraph
  case elaborateProcessNetwork graph [nestedSiteLeft, nestedSiteLeft] of
    Left (DuplicateScopedProcessSiteKey owner siteKey) -> do
      assert (owner == cellLeftKey) "duplicate nested-site diagnostic named wrong owner"
      assert (siteKey == localRunSite) "duplicate nested-site diagnostic named wrong local site"
    other -> Left ("duplicate nested local process site was accepted: " <> show other)

sharedNestedTargetRejects :: Either String ()
sharedNestedTargetRejects = do
  graph <- mapLeft show nestedGraph
  let aliased = ScopedProcessDeclarationSite cellRightKey localRunSite nestedTargetLeft
  case elaborateProcessNetwork graph [nestedSiteLeft, aliased] of
    Left (DuplicateScopedProcessTarget target firstOwner firstSite secondOwner secondSite) -> do
      assert (target == nestedTargetLeft) "shared-target diagnostic named wrong target"
      assert
        (firstOwner == cellLeftKey && firstSite == localRunSite)
        "shared-target diagnostic lost first exact owner/site"
      assert
        (secondOwner == cellRightKey && secondSite == localRunSite)
        "shared-target diagnostic lost second exact owner/site"
    other -> Left ("shared exact target cloned process population: " <> show other)

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

nestedGraph :: Either ArchitectureInstantiationError ArchitectureInstanceGraph
nestedGraph = instantiateArchitecture nestedRootKey nestedRootSpec

nestedRootSpec :: ArchitectureNodeSpec
nestedRootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "nested-root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ ArchitectureChildSpec cellLeftSlot cellSpec
      , ArchitectureChildSpec cellRightSlot cellSpec
      ]
  , architectureNodeReferences = []
  }

cellSpec :: ArchitectureNodeSpec
cellSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "cell"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = [ArchitectureChildSpec localWorkerSlot workerSpec]
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

declaration :: String -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation
      { declarationDisplayName = fromString label
      , declarationModulePath = []
      }
  , declarationKey = DeclarationKey (fromString ("decl-" <> label))
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "site-b") targetB

nestedSiteLeft, nestedSiteRight :: ProcessDeclarationSite
nestedSiteLeft = ScopedProcessDeclarationSite cellLeftKey localRunSite nestedTargetLeft
nestedSiteRight = ScopedProcessDeclarationSite cellRightKey localRunSite nestedTargetRight

localRunSite :: ProcessSiteKey
localRunSite = ProcessSiteKey "run"

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

nestedRootKey, cellLeftKey, cellRightKey, nestedTargetLeft, nestedTargetRight :: InstanceKey
nestedRootKey = InstanceKey "nested-root-instance"
cellLeftKey = scopedInstanceKey nestedRootKey cellLeftSlot
cellRightKey = scopedInstanceKey nestedRootKey cellRightSlot
nestedTargetLeft = scopedInstanceKey cellLeftKey localWorkerSlot
nestedTargetRight = scopedInstanceKey cellRightKey localWorkerSlot

slotA, slotB, cellLeftSlot, cellRightSlot, localWorkerSlot :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"
cellLeftSlot = OccurrenceSlotKey "cell-left"
cellRightSlot = OccurrenceSlotKey "cell-right"
localWorkerSlot = OccurrenceSlotKey "worker"

fromString :: String -> Text
fromString = Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
