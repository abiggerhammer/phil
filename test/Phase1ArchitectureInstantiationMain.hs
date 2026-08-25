{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Static
  ( ArchitectureChildSpec (..)
  , ArchitectureInstanceGraph (..)
  , ArchitectureInstanceIdentity (..)
  , ArchitectureInstantiationError (..)
  , ArchitectureNodeSpec (..)
  , ArchitectureReferenceSpec (..)
  , ArchitectureRequirement (..)
  , ArchitectureRequirementDisposition (..)
  , ArchitectureRequirementKind (..)
  , CheckedArchitectureInstance (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , InstanceKey (..)
  , OccurrenceSlotKey (..)
  , ReferenceKey (..)
  , RequirementKey (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  , instantiateArchitecture
  , lookupArchitectureInstance
  , lookupArchitectureReference
  , scopedInstanceKey
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "ARCH-005 distinct equal-looking occurrences remain distinct" distinctEqualLookingOccurrences
    , test "ARCH-006 explicit reference shares an existing occurrence" explicitReferenceShares
    , test "ARCH-006 nested occurrence identity is generative under each parent" nestedGenerativity
    , test "ARCH-006 changed static argument preserves occurrence key and revises instance" changedStaticArgumentRevisesOnlyRevision
    , test "ARCH-008 root requirements do not receive magical initial bindings" rootRequirementNeedsExplicitDisposition
    , test "ARCH-009 existing provider candidates are never selected ambiently" providerCandidatesDoNotImplicitlyBind
    , test "ARCH-009 explicit provider binding checks the required interface" explicitProviderBindingChecksInterface
    , test "architecture binding to a missing occurrence rejects" missingBindingTargetRejects
    , test "duplicate stable occurrence slots reject" duplicateOccurrenceSlotRejects
    , test "explicit re-export closes an architecture-level requirement" explicitReexportClosesRequirement
    , test "explicit sharing target must exist in the checked graph" missingReferenceTargetRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

distinctEqualLookingOccurrences :: Either String ()
distinctEqualLookingOccurrences = do
  graph <- mapLeft show $ instantiateArchitecture rootKey root
  let primaryKey = scopedInstanceKey rootKey primarySlot
      backupKey = scopedInstanceKey rootKey backupSlot
  assert (primaryKey /= backupKey) "different occurrence slots produced one InstanceKey"
  assert (Map.size (architectureGraphInstances graph) == 3)
    "root plus two child occurrences were not preserved as three instances"
  primary <- requireInstance primaryKey graph
  backup <- requireInstance backupKey graph
  assert
    (identityInstanceRevision (checkedArchitectureIdentity primary)
      /= identityInstanceRevision (checkedArchitectureIdentity backup))
    "distinct occurrence keys did not induce distinct InstanceRevisions"
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ ArchitectureChildSpec primarySlot (emptyNode providerDeclaration)
          , ArchitectureChildSpec backupSlot (emptyNode providerDeclaration)
          ]
      }

explicitReferenceShares :: Either String ()
explicitReferenceShares = do
  graph <- mapLeft show $ instantiateArchitecture rootKey root
  assert (Map.size (architectureGraphInstances graph) == 2)
    "explicit sharing created a second occurrence"
  assert
    (lookupArchitectureReference rootKey (ReferenceKey "preferred-store") graph
      == Just primaryKey)
    "explicit reference did not preserve the existing InstanceKey"
  where
    primaryKey = scopedInstanceKey rootKey primarySlot
    root = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ArchitectureChildSpec primarySlot (emptyNode providerDeclaration)]
      , architectureNodeReferences =
          [ArchitectureReferenceSpec (ReferenceKey "preferred-store") primaryKey]
      }

nestedGenerativity :: Either String ()
nestedGenerativity = do
  graph <- mapLeft show $ instantiateArchitecture rootKey root
  let eastKey = scopedInstanceKey rootKey eastSlot
      westKey = scopedInstanceKey rootKey westSlot
      eastStore = scopedInstanceKey eastKey storeSlot
      westStore = scopedInstanceKey westKey storeSlot
  assert (eastKey /= westKey) "distinct parent slots collapsed"
  assert (eastStore /= westStore)
    "same child slot under distinct parent occurrences collapsed"
  _ <- requireInstance eastStore graph
  _ <- requireInstance westStore graph
  pure ()
  where
    cluster = (emptyNode clusterDeclaration)
      { architectureNodeChildren =
          [ArchitectureChildSpec storeSlot (emptyNode providerDeclaration)]
      }
    root = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ ArchitectureChildSpec eastSlot cluster
          , ArchitectureChildSpec westSlot cluster
          ]
      }

changedStaticArgumentRevisesOnlyRevision :: Either String ()
changedStaticArgumentRevisesOnlyRevision = do
  firstGraph <- mapLeft show $ instantiateArchitecture rootKey (root "v1")
  secondGraph <- mapLeft show $ instantiateArchitecture rootKey (root "v2")
  first <- requireInstance childKey firstGraph
  second <- requireInstance childKey secondGraph
  assert
    (identityInstanceKey (checkedArchitectureIdentity first)
      == identityInstanceKey (checkedArchitectureIdentity second))
    "semantic edit changed stable occurrence lineage"
  assert
    (identityInstanceRevision (checkedArchitectureIdentity first)
      /= identityInstanceRevision (checkedArchitectureIdentity second))
    "identity-bearing static argument change did not revise the instance"
  where
    childKey = scopedInstanceKey rootKey primarySlot
    root mode = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ ArchitectureChildSpec primarySlot
              ((emptyNode providerDeclaration)
                { architectureNodeStaticBindings =
                    Map.singleton "mode" (SemanticAtom mode)
                })
          ]
      }

rootRequirementNeedsExplicitDisposition :: Either String ()
rootRequirementNeedsExplicitDisposition =
  case instantiateArchitecture rootKey root of
    Left (UnresolvedArchitectureRequirement owner key CapabilityRequirement) ->
      assert (owner == rootKey && key == RequirementKey "initial-authority")
        "wrong unresolved root requirement reported"
    other -> Left ("undeclared root authority did not reject: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "initial-authority"
              , architectureRequirementKind = CapabilityRequirement
              , architectureRequirementExpectedInterface = Nothing
              , architectureRequirementDisposition = Nothing
              }
          ]
      }

providerCandidatesDoNotImplicitlyBind :: Either String ()
providerCandidatesDoNotImplicitlyBind =
  case instantiateArchitecture rootKey root of
    Left (UnresolvedArchitectureRequirement owner key ProviderRequirement) ->
      assert (owner == rootKey && key == RequirementKey "store")
        "wrong provider requirement reported"
    other -> Left ("ambient provider candidates were implicitly selected: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ ArchitectureChildSpec primarySlot (emptyNode providerDeclaration)
          , ArchitectureChildSpec backupSlot (emptyNode providerDeclaration)
          ]
      , architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "store"
              , architectureRequirementKind = ProviderRequirement
              , architectureRequirementExpectedInterface =
                  Just (identityInterfaceRevision providerDeclaration)
              , architectureRequirementDisposition = Nothing
              }
          ]
      }

explicitProviderBindingChecksInterface :: Either String ()
explicitProviderBindingChecksInterface = do
  graph <- mapLeft show $ instantiateArchitecture rootKey validRoot
  rootNode <- requireInstance rootKey graph
  requirement <- maybe
    (Left "checked provider requirement disappeared")
    Right
    (Map.lookup (RequirementKey "store") (checkedArchitectureRequirements rootNode))
  assert
    (architectureRequirementDisposition requirement == Just (RequirementBoundTo providerKey))
    "explicit provider binding was not preserved"
  case instantiateArchitecture rootKey invalidRoot of
    Left (ArchitectureBindingInterfaceMismatch _ _ _ _) -> Right ()
    other -> Left ("wrong provider interface was not rejected: " <> show other)
  where
    providerKey = scopedInstanceKey rootKey primarySlot
    commonRoot expected = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ArchitectureChildSpec primarySlot (emptyNode providerDeclaration)]
      , architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "store"
              , architectureRequirementKind = ProviderRequirement
              , architectureRequirementExpectedInterface = Just expected
              , architectureRequirementDisposition = Just (RequirementBoundTo providerKey)
              }
          ]
      }
    validRoot = commonRoot (identityInterfaceRevision providerDeclaration)
    invalidRoot = commonRoot (identityInterfaceRevision clusterDeclaration)

missingBindingTargetRejects :: Either String ()
missingBindingTargetRejects =
  case instantiateArchitecture rootKey root of
    Left (UnknownArchitectureBindingTarget owner key target) ->
      assert
        ( owner == rootKey
          && key == RequirementKey "store"
          && target == InstanceKey "missing.store" )
        "wrong missing binding target reported"
    other -> Left ("binding to missing occurrence did not reject: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "store"
              , architectureRequirementKind = ProviderRequirement
              , architectureRequirementExpectedInterface = Nothing
              , architectureRequirementDisposition =
                  Just (RequirementBoundTo (InstanceKey "missing.store"))
              }
          ]
      }

duplicateOccurrenceSlotRejects :: Either String ()
duplicateOccurrenceSlotRejects =
  case instantiateArchitecture rootKey root of
    Left (DuplicateOccurrenceSlot owner slot) ->
      assert (owner == rootKey && slot == primarySlot)
        "wrong duplicate occurrence slot reported"
    other -> Left ("duplicate occurrence slot did not reject: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeChildren =
          [ ArchitectureChildSpec primarySlot (emptyNode providerDeclaration)
          , ArchitectureChildSpec primarySlot (emptyNode providerDeclaration)
          ]
      }

explicitReexportClosesRequirement :: Either String ()
explicitReexportClosesRequirement = do
  graph <- mapLeft show $ instantiateArchitecture rootKey root
  rootNode <- requireInstance rootKey graph
  requirement <- maybe
    (Left "re-exported requirement disappeared")
    Right
    (Map.lookup (RequirementKey "external-store") (checkedArchitectureRequirements rootNode))
  assert
    (architectureRequirementDisposition requirement
      == Just (RequirementReExported "root.store"))
    "explicit architecture re-export was not preserved"
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "external-store"
              , architectureRequirementKind = ProviderRequirement
              , architectureRequirementExpectedInterface =
                  Just (identityInterfaceRevision providerDeclaration)
              , architectureRequirementDisposition =
                  Just (RequirementReExported "root.store")
              }
          ]
      }

missingReferenceTargetRejects :: Either String ()
missingReferenceTargetRejects =
  case instantiateArchitecture rootKey root of
    Left (UnknownArchitectureReferenceTarget owner key target) ->
      assert
        ( owner == rootKey
          && key == ReferenceKey "shared-store"
          && target == InstanceKey "missing.store" )
        "wrong missing reference target reported"
    other -> Left ("reference to missing occurrence did not reject: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeReferences =
          [ArchitectureReferenceSpec (ReferenceKey "shared-store") (InstanceKey "missing.store")]
      }

emptyNode :: DeclarationIdentity -> ArchitectureNodeSpec
emptyNode declarationIdentity = ArchitectureNodeSpec
  { architectureNodeDeclaration = declarationIdentity
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

rootDeclaration :: DeclarationIdentity
rootDeclaration = declaration
  "architecture.root"
  "RootArchitecture"
  "root-v1"

clusterDeclaration :: DeclarationIdentity
clusterDeclaration = declaration
  "architecture.cluster"
  "StorageCluster"
  "cluster-v1"

providerDeclaration :: DeclarationIdentity
providerDeclaration = declaration
  "provider.blob"
  "BlobProvider{read,install-if-absent}"
  "blob-provider-v1"

declaration :: Text -> Text -> Text -> DeclarationIdentity
declaration key interface definition = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation key ["Phase1"]
  , declarationKey = DeclarationKey key
  , declarationInterfaceSemantics = SemanticAtom interface
  , declarationDefinitionSemantics = SemanticAtom definition
  }

rootKey :: InstanceKey
rootKey = InstanceKey "phase1.root"

primarySlot, backupSlot, eastSlot, westSlot, storeSlot :: OccurrenceSlotKey
primarySlot = OccurrenceSlotKey "store.primary"
backupSlot = OccurrenceSlotKey "store.backup"
eastSlot = OccurrenceSlotKey "cluster.east"
westSlot = OccurrenceSlotKey "cluster.west"
storeSlot = OccurrenceSlotKey "cluster.store"

requireInstance
  :: InstanceKey
  -> ArchitectureInstanceGraph
  -> Either String CheckedArchitectureInstance
requireInstance key graph = maybe
  (Left ("missing expected ArchitectureInstance: " <> show key))
  Right
  (lookupArchitectureInstance key graph)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
