{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Process
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-002 equal-looking sites retain distinct ProcessKeys" distinctEqualLookingSites
    , test "CONC-002 duplicate target activation rejects" duplicateTargetRejects
    , test "CONC-002 backend worker labels do not define process identity" backendLabelsDoNotCollapseIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

distinctEqualLookingSites :: Either String ()
distinctEqualLookingSites = do
  graph <- mapLeft show rootGraph
  workerA <- maybe (Left "missing worker-a occurrence") Right $
    lookupArchitectureInstance targetA graph
  workerB <- maybe (Left "missing worker-b occurrence") Right $
    lookupArchitectureInstance targetB graph
  assert
    (architectureDeclarationIdentity (checkedArchitectureDescriptor workerA)
      == architectureDeclarationIdentity (checkedArchitectureDescriptor workerB))
    "equal-looking worker occurrences did not share declaration semantics"
  network <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let population = processNetworkPopulation network
      keys = Map.keys population
      targets = map (identityInstanceKey . processOccurrenceTarget) (Map.elems population)
  assert (length keys == 2 && Set.size (Set.fromList keys) == 2)
    "equal-looking process sites collapsed ProcessKey identity"
  assert (Set.fromList targets == Set.fromList [targetA, targetB])
    "process identity lost exact executable occurrence identity"

duplicateTargetRejects :: Either String ()
duplicateTargetRejects = do
  graph <- mapLeft show rootGraph
  let duplicateSite = ProcessDeclarationSite (ProcessSiteKey "site-a-duplicate") targetA
  case elaborateProcessNetwork graph [siteA, duplicateSite] of
    Left (DuplicateProcessTarget target firstSite secondSite) -> do
      assert (target == targetA) "duplicate-target diagnostic named the wrong target"
      assert
        (firstSite == ProcessSiteKey "site-a"
          && secondSite == ProcessSiteKey "site-a-duplicate")
        "duplicate-target diagnostic did not retain both process sites"
    other -> Left ("double activation did not reject exactly: " <> show other)

backendLabelsDoNotCollapseIdentity :: Either String ()
backendLabelsDoNotCollapseIdentity = do
  graph <- mapLeft show rootGraph
  network <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let population = processNetworkPopulation network
      sameWorkerLabel :: Text
      sameWorkerLabel = "worker-0"
      realizationMetadata = Map.fromList
        [ (processOccurrenceKey occurrence, sameWorkerLabel)
        | occurrence <- Map.elems population
        ]
  assert (Map.size realizationMetadata == 2)
    "realization metadata lost one semantic ProcessKey"
  assert (Set.size (Set.fromList (Map.elems realizationMetadata)) == 1)
    "fixture did not assign the same backend worker label to both processes"
  assert (Map.size population == 2)
    "shared backend worker label collapsed semantic process population"

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
