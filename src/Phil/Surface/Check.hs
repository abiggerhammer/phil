module Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
  , ReleaseRequirement (..)
  , ReleaseSemanticAccount (..)
  , ReleaseTransitionOutcome (..)
  , ReleaseResidue (..)
  , ReleaseTransitionContract (..)
  , ReleaseSelectionError (..)
  , selectReleaseTransition
  , SurfaceEnvironment (..)
  , SurfaceCheckResult (..)
  , ModuleName (..)
  , ModuleTable
  , ResolutionScope
  , ImportBinding (..)
  , ImportSelection (..)
  , ImportSpec (..)
  , ModuleResolutionError (..)
  , emptySurfaceEnvironment
  , checkSurfaceComponent
  , emptyModuleTable
  , emptyResolutionScope
  , declareModule
  , insertLocalDeclaration
  , resolveImports
  , lookupResolvedDeclaration
  , resolutionBindings
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (DeclarationIdentity)
import qualified Phil.Surface.Check.Engine as Engine
import Phil.Surface.Check.Preflight (preflightComponent)
import Phil.Surface.Check.Types
import Phil.Surface.Syntax (Component, Located)

checkSurfaceComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceCheckResult
checkSurfaceComponent environment component = do
  preflightComponent environment component
  Engine.checkSurfaceComponent environment component

-- Phase 1 module/import resolution -------------------------------------------

-- | Human-facing module locator.  It is deliberately not a semantic identity.
newtype ModuleName = ModuleName { unModuleName :: Text }
  deriving (Eq, Ord, Show)

-- | A module exports names that locate already checked declaration identities.
-- No authority-bearing or assurance-bearing state lives in this interface.
data ModuleInterface = ModuleInterface
  { moduleInterfaceName :: ModuleName
  , moduleInterfaceExports :: Map.Map Text DeclarationIdentity
  }
  deriving (Eq, Show)

newtype ModuleTable = ModuleTable
  { moduleTableInterfaces :: Map.Map ModuleName ModuleInterface
  }
  deriving (Eq, Show)

-- | The complete semantic result of import resolution in this Phase 1 slice.
-- Imports can change only which DeclarationIdentity is available under which
-- local source name.
newtype ResolutionScope = ResolutionScope
  { resolutionBindings :: Map.Map Text DeclarationIdentity
  }
  deriving (Eq, Show)

-- | Select one exported declaration and optionally change only its local name.
data ImportBinding = ImportBinding
  { importExportName :: Text
  , importLocalName :: Text
  }
  deriving (Eq, Ord, Show)

data ImportSelection
  = ImportAll
  | ImportOnly [ImportBinding]
  deriving (Eq, Ord, Show)

data ImportSpec = ImportSpec
  { importModuleName :: ModuleName
  , importSelection :: ImportSelection
  }
  deriving (Eq, Ord, Show)

data ModuleResolutionError
  = DuplicateModule ModuleName
  | DuplicateModuleExport ModuleName Text
  | DuplicateResolutionName Text
  | UnknownModule ModuleName
  | UnknownModuleExport ModuleName Text
  deriving (Eq, Ord, Show)

emptyModuleTable :: ModuleTable
emptyModuleTable = ModuleTable Map.empty

emptyResolutionScope :: ResolutionScope
emptyResolutionScope = ResolutionScope Map.empty

declareModule
  :: ModuleName
  -> [(Text, DeclarationIdentity)]
  -> ModuleTable
  -> Either ModuleResolutionError ModuleTable
declareModule moduleName exports table
  | Map.member moduleName (moduleTableInterfaces table) =
      Left (DuplicateModule moduleName)
  | otherwise = do
      exportMap <- uniqueExports moduleName exports
      let interface = ModuleInterface
            { moduleInterfaceName = moduleName
            , moduleInterfaceExports = exportMap
            }
      Right table
        { moduleTableInterfaces =
            Map.insert moduleName interface (moduleTableInterfaces table)
        }

insertLocalDeclaration
  :: Text
  -> DeclarationIdentity
  -> ResolutionScope
  -> Either ModuleResolutionError ResolutionScope
insertLocalDeclaration localName declarationIdentity scope
  | Map.member localName (resolutionBindings scope) =
      Left (DuplicateResolutionName localName)
  | otherwise = Right scope
      { resolutionBindings =
          Map.insert localName declarationIdentity (resolutionBindings scope)
      }

resolveImports
  :: ModuleTable
  -> ResolutionScope
  -> [ImportSpec]
  -> Either ModuleResolutionError ResolutionScope
resolveImports table initialScope specs = foldl resolveImport (Right initialScope) specs
  where
    resolveImport accumulated spec = do
      scope <- accumulated
      interface <- maybe
        (Left (UnknownModule (importModuleName spec)))
        Right
        (Map.lookup (importModuleName spec) (moduleTableInterfaces table))
      bindings <- selectedBindings interface (importSelection spec)
      foldl insertBinding (Right scope) bindings

    insertBinding accumulated (localName, declarationIdentity) = do
      scope <- accumulated
      insertLocalDeclaration localName declarationIdentity scope

selectedBindings
  :: ModuleInterface
  -> ImportSelection
  -> Either ModuleResolutionError [(Text, DeclarationIdentity)]
selectedBindings interface selection = case selection of
  ImportAll -> Right (Map.toAscList (moduleInterfaceExports interface))
  ImportOnly bindings -> mapM resolveOne bindings
  where
    resolveOne binding = do
      declarationIdentity <- maybe
        (Left (UnknownModuleExport
          (moduleInterfaceName interface)
          (importExportName binding)))
        Right
        (Map.lookup (importExportName binding) (moduleInterfaceExports interface))
      Right (importLocalName binding, declarationIdentity)

lookupResolvedDeclaration :: Text -> ResolutionScope -> Maybe DeclarationIdentity
lookupResolvedDeclaration localName = Map.lookup localName . resolutionBindings

uniqueExports
  :: ModuleName
  -> [(Text, DeclarationIdentity)]
  -> Either ModuleResolutionError (Map.Map Text DeclarationIdentity)
uniqueExports moduleName = go Set.empty Map.empty
  where
    go _ exports [] = Right exports
    go seen exports ((exportName, declarationIdentity) : rest)
      | Set.member exportName seen = Left (DuplicateModuleExport moduleName exportName)
      | otherwise = go
          (Set.insert exportName seen)
          (Map.insert exportName declarationIdentity exports)
          rest
