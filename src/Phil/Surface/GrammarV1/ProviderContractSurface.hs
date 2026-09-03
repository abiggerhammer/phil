module Phil.Surface.GrammarV1.ProviderContractSurface
  ( GrammarV1CheckedProviderContractSurface (..)
  , grammarV1CheckedClosedProviderContractSurface
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.ProviderQualification
  ( ProviderOperationKey (..)
  )
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , StaticContext
  )
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProviderContractDecl (..)
  , GrammarV1ProviderContractItem (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked semantic surface of one closed provider contract before callable
-- references have been resolved to concrete 'CallableRefinementSurface' values.
-- Stable declaration lineage and public interface revision are supplied by the
-- lineage/interface authority above Grammar v1; neither is derived from source
-- display spelling or module location.
--
-- Provider operation names become exact contract-local 'ProviderOperationKey's.
-- Their declared callable-contract types remain unresolved static identities at
-- this boundary: only bare/qualified unspecialized named types are admitted, and
-- the existing generic static-reference carrier preserves their exact dotted
-- lookup spelling without asserting existence, kind, interface revision, or
-- qualification. A later competent callable/static resolver must establish the
-- concrete callable public surface before Core 'ProviderContract' construction.
--
-- Named provider laws and lifecycle propositions are checked exactly once through
-- the ordinary Core proposition/focusing path under an empty top-level term
-- scope. Source item order controls failure precedence; successful operation,
-- law, and lifecycle categories preserve their own source order. Generic or
-- requirement-bearing provider contracts and richer/specialized operation type
-- forms remain fail-closed.
data GrammarV1CheckedProviderContractSurface = GrammarV1CheckedProviderContractSurface
  { checkedProviderDeclarationKey :: DeclarationKey
  , checkedProviderInterfaceRevision :: InterfaceRevision
  , checkedProviderOperationReferences
      :: [(ProviderOperationKey, GenericStaticActual)]
  , checkedProviderLaws :: [(Text, Proposition, [FocusStep])]
  , checkedProviderLifecycle :: [(Text, Proposition, [FocusStep])]
  }
  deriving (Eq, Show)

grammarV1CheckedClosedProviderContractSurface
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> GrammarV1ProviderContractDecl
  -> Maybe (Either FocusingError GrammarV1CheckedProviderContractSurface)
grammarV1CheckedClosedProviderContractSurface
    staticContext declarationKey interfaceRevision source
  | not (null (grammarV1ProviderContractGenericParams source)) = Nothing
  | not (null (grammarV1ProviderContractRequirements source)) = Nothing
  | otherwise = go (grammarV1ProviderContractItems source) [] [] []
  where
    go [] operations laws lifecycle = Just (Right GrammarV1CheckedProviderContractSurface
      { checkedProviderDeclarationKey = declarationKey
      , checkedProviderInterfaceRevision = interfaceRevision
      , checkedProviderOperationReferences = reverse operations
      , checkedProviderLaws = reverse laws
      , checkedProviderLifecycle = reverse lifecycle
      })
    go (Located _ item : rest) operations laws lifecycle = case item of
      GrammarV1ProviderContractOperation
          (Located _ operationName)
          (Located _ operationType) -> do
        callableReference <- unresolvedCallableReference operationType
        go
          rest
          ((ProviderOperationKey operationName, callableReference) : operations)
          laws
          lifecycle
      GrammarV1ProviderContractLaw
          (Located _ lawName)
          (Located _ proposition) -> do
        checked <- grammarV1CheckedProposition
          staticContext
          emptySurfaceState
          proposition
        case checked of
          Left err -> Just (Left err)
          Right (accepted, steps) ->
            go rest operations ((lawName, accepted, steps) : laws) lifecycle
      GrammarV1ProviderContractLifecycle
          (Located _ lifecycleName)
          (Located _ proposition) -> do
        checked <- grammarV1CheckedProposition
          staticContext
          emptySurfaceState
          proposition
        case checked of
          Left err -> Just (Left err)
          Right (accepted, steps) ->
            go rest operations laws ((lifecycleName, accepted, steps) : lifecycle)

unresolvedCallableReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedCallableReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing
