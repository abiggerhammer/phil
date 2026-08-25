{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Module
  ( ModuleName (..)
  , ModuleTable
  , ResolutionScope
  , ImportBinding (..)
  , ImportSelection (..)
  , ImportSpec (..)
  , ModuleResolutionError (..)
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

-- | Human-facing module locator.  It is intentionally not a semantic identity:
-- moving a stable declaration between modules need not change its DeclarationKey
-- or checked revisions.
newtype ModuleName = ModuleName { unModuleName :: Text }
  deriving (Eq, Ord, Show)

-- | A Phase 1 module exports names that resolve to already checked declaration
-- identities.  No capability, provider binding, assumption, obligation
-- disposition, architecture occurrence, or runtime initializer is stored here.
data ModuleInterface = ModuleInterface
  { moduleInterfaceName :: ModuleName
  , moduleInterfaceExports :: Map.Map Text DeclarationIdentity
  }
  deriving (Eq, Show)

newtype ModuleTable = ModuleTable
  { moduleTableInterfaces :: Map.Map ModuleName ModuleInterface
  }
  deriving (Eq, Show)

-- | The complete semantic result of module/import resolution in this Phase 1
-- slice.  Imports can only change which declaration identities are available by
-- local source name.  Later elaboration must perform every authority-bearing or
-- obligation-bearing action explicitly.
newtype ResolutionScope = ResolutionScope
  { resolutionBindings :: Map.Map Text DeclarationIdentity
  }
  deriving (Eq, Show)

-- | Select one exported name and optionally give it another local spelling.
-- This is checked resolver input, not a commitment to final surface syntax.
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

-- | Register one checked module interface.  Export spellings are organizational;
-- the exported DeclarationIdentity remains authoritative.
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

-- | Add a declaration already local to the current source unit.  Imports may
-- not silently shadow it, even when the imported declaration happens to have an
-- equal spelling or identity.
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
resolveImports table = foldl resolveImport . Right
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
