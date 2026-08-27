{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.ArchitectureIdentity
  ( interfaceValidityDimension
  , interfaceValidityContext
  , interfaceValidityScope
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import Phil.Assurance.Types (ValidityScope (..))
import Phil.Core.Static
  ( DeclarationIdentity (..)
  , DeclarationKey (..)
  , InterfaceRevision (..)
  )

-- | One stable validity-context dimension for evidence whose applicability
-- depends on the public interface of a declaration.  The dimension key follows
-- declaration lineage, while the value is the exact checked InterfaceRevision.
-- Human presentation and module paths therefore never enter this boundary.
interfaceValidityDimension :: DeclarationIdentity -> Text
interfaceValidityDimension identity =
  "phil.arch.interface-revision.v1:"
    <> unDeclarationKey (identityDeclarationKey identity)

-- | Verification-context fragment required by interface-dependent evidence.
interfaceValidityContext :: DeclarationIdentity -> Map Text Text
interfaceValidityContext identity = Map.singleton
  (interfaceValidityDimension identity)
  (unInterfaceRevision (identityInterfaceRevision identity))

-- | Evidence validity scope for an exact declaration interface revision.
-- Existing assurance verification already fails closed when this scope no
-- longer matches the active verification context.
interfaceValidityScope :: DeclarationIdentity -> ValidityScope
interfaceValidityScope = ValidityScope . interfaceValidityContext
