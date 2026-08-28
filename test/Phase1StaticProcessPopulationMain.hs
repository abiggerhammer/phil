{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.ProcessNetwork
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-001 exact population is declaration-order independent" populationOrderIndependent
    , test "CONC-001 every process activates exactly once" activatesExactlyOnce
    , test "CONC-001 unknown target cannot enter population" unknownTargetRejects
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
  assert (targetA `elem` targetKeys && targetB `elem` targetKeys)
    "population did not retain both exact target occurrences"
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

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"

fromString :: String -> Text
fromString = Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
