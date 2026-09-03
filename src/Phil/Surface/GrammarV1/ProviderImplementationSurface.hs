module Phil.Surface.GrammarV1.ProviderImplementationSurface
  ( GrammarV1CheckedOpaqueProviderImplementationSurface (..)
  , grammarV1CheckedClosedOpaqueProviderImplementationSurface
  ) where

import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1OpaqueProviderImplementationDecl (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked declaration surface for the closed opaque-provider implementation
-- fragment. Stable declaration identity and definition revision are supplied by
-- the lineage/revision authority above Grammar v1; neither is derived from the
-- source display name or location.
--
-- The implemented provider contract remains one unresolved static identity at
-- this seam. Only a bare/qualified unspecialized named type is admitted, using
-- the already-established static-reference carrier. This records what contract
-- the opaque implementation claims to satisfy without asserting that the target
-- exists, has provider kind, is at any particular interface revision, or has
-- actually been qualified.
--
-- This is intentionally not a Core 'ProviderImplementation'. Opaque provider
-- realizations require external/foreign qualification evidence and realization
-- facts; this source declaration cannot manufacture implementation entries,
-- callable semantics, authority confinement, evidence, symbols, or runtime
-- bindings. Generic parameters, generic requirements, specialized references,
-- and structured satisfaction types remain outside this bounded fragment.
data GrammarV1CheckedOpaqueProviderImplementationSurface =
  GrammarV1CheckedOpaqueProviderImplementationSurface
    { checkedOpaqueProviderDeclarationKey :: DeclarationKey
    , checkedOpaqueProviderDefinitionRevision :: DefinitionRevision
    , checkedOpaqueProviderContractReference :: GenericStaticActual
    }
  deriving (Eq, Show)

grammarV1CheckedClosedOpaqueProviderImplementationSurface
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1OpaqueProviderImplementationDecl
  -> Maybe GrammarV1CheckedOpaqueProviderImplementationSurface
grammarV1CheckedClosedOpaqueProviderImplementationSurface
    declarationKey definitionRevision source
  | not (null (grammarV1OpaqueProviderImplementationGenericParams source)) = Nothing
  | not (null (grammarV1OpaqueProviderImplementationRequirements source)) = Nothing
  | otherwise = do
      contractReference <- unresolvedProviderContractReference
        (grammarV1OpaqueProviderImplementationSatisfies source)
      pure GrammarV1CheckedOpaqueProviderImplementationSurface
        { checkedOpaqueProviderDeclarationKey = declarationKey
        , checkedOpaqueProviderDefinitionRevision = definitionRevision
        , checkedOpaqueProviderContractReference = contractReference
        }

unresolvedProviderContractReference
  :: Located GrammarV1Type
  -> Maybe GenericStaticActual
unresolvedProviderContractReference (Located _ sourceType) = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing
