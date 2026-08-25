{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Static
  ( ArchitectureInstanceGraph (..)
  , ArchitectureInstantiationError (..)
  , ArchitectureNodeSpec (..)
  , ArchitectureRequirement (..)
  , ArchitectureRequirementKind (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , InstanceKey (..)
  , RequirementKey (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  , instantiateArchitecture
  )
import Phil.Surface.Check
  ( ImportBinding (..)
  , ImportSelection (..)
  , ImportSpec (..)
  , ModuleName (..)
  , ModuleResolutionError (..)
  , declareModule
  , emptyModuleTable
  , emptyResolutionScope
  , insertLocalDeclaration
  , lookupResolvedDeclaration
  , resolutionBindings
  , resolveImports
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "ARCH-001 import-all changes declaration name availability only" importAllResolvesDeclarations
    , test "ARCH-001 import alias preserves exact declaration identity" importAliasPreservesIdentity
    , test "ARCH-001 module movement does not define declaration identity" moduleMovementDoesNotIdentify
    , test "ARCH-001 importing an architecture declaration does not instantiate it" importDoesNotInstantiate
    , test "ARCH-001 imported provider declaration does not satisfy a provider requirement" importDoesNotSatisfyProvider
    , test "ARCH-001 imported capability-looking declaration does not grant authority" importDoesNotGrantCapability
    , test "ARCH-001 imported assumption-looking declaration does not accept an assumption" importDoesNotAcceptAssumption
    , test "module imports cannot silently shadow local declarations" importCollisionRejects
    , test "unknown module and export lookup fail closed" unknownImportRejects
    , test "duplicate module exports are rejected before resolution" duplicateExportRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

importAllResolvesDeclarations :: Either String ()
importAllResolvesDeclarations = do
  table <- mapLeft show $ declareModule storageModule
    [ ("BlobProvider", providerDeclaration)
    , ("DigestProvider", digestDeclaration)
    ]
    emptyModuleTable
  scope <- mapLeft show $ resolveImports table emptyResolutionScope
    [ImportSpec storageModule ImportAll]
  assert
    (lookupResolvedDeclaration "BlobProvider" scope == Just providerDeclaration)
    "provider declaration identity was not imported exactly"
  assert
    (lookupResolvedDeclaration "DigestProvider" scope == Just digestDeclaration)
    "digest declaration identity was not imported exactly"
  assert
    (Map.size (resolutionBindings scope) == 2)
    "import resolution produced state beyond the two requested name bindings"

importAliasPreservesIdentity :: Either String ()
importAliasPreservesIdentity = do
  table <- mapLeft show $ declareModule storageModule
    [("BlobProvider", providerDeclaration)]
    emptyModuleTable
  scope <- mapLeft show $ resolveImports table emptyResolutionScope
    [ ImportSpec storageModule
        (ImportOnly [ImportBinding "BlobProvider" "Store"])
    ]
  assert
    (lookupResolvedDeclaration "Store" scope == Just providerDeclaration)
    "local alias changed the exported declaration identity"
  assert
    (lookupResolvedDeclaration "BlobProvider" scope == Nothing)
    "explicit import-only alias also introduced the original spelling"

moduleMovementDoesNotIdentify :: Either String ()
moduleMovementDoesNotIdentify = do
  oldTable <- mapLeft show $ declareModule (ModuleName "Old.Storage")
    [("BlobProvider", providerDeclaration)]
    emptyModuleTable
  newTable <- mapLeft show $ declareModule (ModuleName "New.Storage")
    [("BlobProvider", providerDeclaration)]
    emptyModuleTable
  oldScope <- mapLeft show $ resolveImports oldTable emptyResolutionScope
    [ImportSpec (ModuleName "Old.Storage") ImportAll]
  newScope <- mapLeft show $ resolveImports newTable emptyResolutionScope
    [ImportSpec (ModuleName "New.Storage") ImportAll]
  assert
    (oldScope == newScope)
    "module path changed the resolved stable declaration identity"

importDoesNotInstantiate :: Either String ()
importDoesNotInstantiate = do
  table <- mapLeft show $ declareModule (ModuleName "Architectures")
    [("RootArchitecture", rootDeclaration)]
    emptyModuleTable
  scope <- mapLeft show $ resolveImports table emptyResolutionScope
    [ImportSpec (ModuleName "Architectures") ImportAll]
  assert
    (lookupResolvedDeclaration "RootArchitecture" scope == Just rootDeclaration)
    "architecture declaration was not made available"
  graph <- mapLeft show $ instantiateArchitecture rootKey (emptyNode rootDeclaration)
  assert
    (Map.size (architectureGraphInstances graph) == 1)
    "mere declaration availability manufactured a contained architecture occurrence"

importDoesNotSatisfyProvider :: Either String ()
importDoesNotSatisfyProvider = do
  table <- mapLeft show $ declareModule storageModule
    [("BlobProvider", providerDeclaration)]
    emptyModuleTable
  _ <- mapLeft show $ resolveImports table emptyResolutionScope
    [ImportSpec storageModule ImportAll]
  case instantiateArchitecture rootKey root of
    Left (UnresolvedArchitectureRequirement owner key ProviderRequirement) ->
      assert
        (owner == rootKey && key == RequirementKey "store")
        "wrong unresolved provider requirement reported"
    other -> Left ("import availability satisfied provider requirement: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "store"
              , architectureRequirementKind = ProviderRequirement
              , architectureRequirementExpectedInterface =
                  Just (identityInterfaceRevision providerDeclaration)
              , architectureRequirementDisposition = Nothing
              }
          ]
      }

importDoesNotGrantCapability :: Either String ()
importDoesNotGrantCapability = do
  table <- mapLeft show $ declareModule authorityModule
    [("StorageWriteAuthority", capabilityDeclaration)]
    emptyModuleTable
  _ <- mapLeft show $ resolveImports table emptyResolutionScope
    [ImportSpec authorityModule ImportAll]
  case instantiateArchitecture rootKey root of
    Left (UnresolvedArchitectureRequirement owner key CapabilityRequirement) ->
      assert
        (owner == rootKey && key == RequirementKey "write-authority")
        "wrong unresolved capability requirement reported"
    other -> Left ("import availability granted capability authority: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "write-authority"
              , architectureRequirementKind = CapabilityRequirement
              , architectureRequirementExpectedInterface = Nothing
              , architectureRequirementDisposition = Nothing
              }
          ]
      }

importDoesNotAcceptAssumption :: Either String ()
importDoesNotAcceptAssumption = do
  table <- mapLeft show $ declareModule assumptionsModule
    [("TrustedFilesystem", assumptionDeclaration)]
    emptyModuleTable
  _ <- mapLeft show $ resolveImports table emptyResolutionScope
    [ImportSpec assumptionsModule ImportAll]
  case instantiateArchitecture rootKey root of
    Left (UnresolvedArchitectureRequirement owner key BoundaryRequirement) ->
      assert
        (owner == rootKey && key == RequirementKey "trusted-filesystem")
        "wrong unresolved boundary requirement reported"
    other -> Left ("import availability accepted an assumption boundary: " <> show other)
  where
    root = (emptyNode rootDeclaration)
      { architectureNodeRequirements =
          [ ArchitectureRequirement
              { architectureRequirementKey = RequirementKey "trusted-filesystem"
              , architectureRequirementKind = BoundaryRequirement
              , architectureRequirementExpectedInterface = Nothing
              , architectureRequirementDisposition = Nothing
              }
          ]
      }

importCollisionRejects :: Either String ()
importCollisionRejects = do
  table <- mapLeft show $ declareModule storageModule
    [("BlobProvider", providerDeclaration)]
    emptyModuleTable
  localScope <- mapLeft show $ insertLocalDeclaration
    "BlobProvider"
    digestDeclaration
    emptyResolutionScope
  case resolveImports table localScope [ImportSpec storageModule ImportAll] of
    Left (DuplicateResolutionName "BlobProvider") -> Right ()
    other -> Left ("import silently shadowed an existing local name: " <> show other)

unknownImportRejects :: Either String ()
unknownImportRejects = do
  case resolveImports emptyModuleTable emptyResolutionScope
      [ImportSpec (ModuleName "Missing") ImportAll] of
    Left (UnknownModule (ModuleName "Missing")) -> pure ()
    other -> Left ("unknown module did not fail closed: " <> show other)
  table <- mapLeft show $ declareModule storageModule
    [("BlobProvider", providerDeclaration)]
    emptyModuleTable
  case resolveImports table emptyResolutionScope
      [ ImportSpec storageModule
          (ImportOnly [ImportBinding "MissingExport" "MissingExport"])
      ] of
    Left (UnknownModuleExport moduleName "MissingExport") ->
      assert (moduleName == storageModule) "unknown export reported wrong module"
    other -> Left ("unknown module export did not fail closed: " <> show other)

duplicateExportRejects :: Either String ()
duplicateExportRejects =
  case declareModule storageModule
      [ ("BlobProvider", providerDeclaration)
      , ("BlobProvider", digestDeclaration)
      ]
      emptyModuleTable of
    Left (DuplicateModuleExport moduleName "BlobProvider") ->
      assert (moduleName == storageModule) "duplicate export reported wrong module"
    other -> Left ("duplicate module exports were accepted: " <> show other)

emptyNode :: DeclarationIdentity -> ArchitectureNodeSpec
emptyNode declarationIdentity = ArchitectureNodeSpec
  { architectureNodeDeclaration = declarationIdentity
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> Text -> DeclarationIdentity
declaration key interface = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation key ["Phase1"]
  , declarationKey = DeclarationKey key
  , declarationInterfaceSemantics = SemanticAtom interface
  , declarationDefinitionSemantics = SemanticAtom (interface <> ".definition.v1")
  }

rootDeclaration, providerDeclaration, digestDeclaration :: DeclarationIdentity
rootDeclaration = declaration "architecture.root" "RootArchitecture"
providerDeclaration = declaration "provider.blob" "BlobProvider"
digestDeclaration = declaration "provider.digest" "DigestProvider"

capabilityDeclaration, assumptionDeclaration :: DeclarationIdentity
capabilityDeclaration = declaration "capability.storage-write" "StorageWriteAuthority"
assumptionDeclaration = declaration "assumption.trusted-filesystem" "TrustedFilesystem"

storageModule, authorityModule, assumptionsModule :: ModuleName
storageModule = ModuleName "Storage"
authorityModule = ModuleName "Authority"
assumptionsModule = ModuleName "Assumptions"

rootKey :: InstanceKey
rootKey = InstanceKey "phase1.import-test.root"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
