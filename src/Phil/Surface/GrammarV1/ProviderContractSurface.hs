module Phil.Surface.GrammarV1.ProviderContractSurface
  ( GrammarV1CheckedProviderContractSurface (..)
  , GrammarV1ResolvedProviderOperation (..)
  , GrammarV1ResolvedProviderContract (..)
  , GrammarV1ProviderContractConstructionError (..)
  , grammarV1CheckedClosedProviderContractSurface
  , grammarV1ConstructClosedProviderContract
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.ProviderQualification
  ( ProviderContract (..)
  , ProviderOperationContract
  , ProviderOperationKey (..)
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

-- | One operation resolution supplied by the competent callable/static layer.
-- The source-facing key and unresolved reference are repeated deliberately so
-- construction can require an exact ordered correspondence before accepting the
-- already-resolved provider operation contract. This type is evidence plumbing;
-- it does not itself prove that a spelling denotes a particular callable.
data GrammarV1ResolvedProviderOperation = GrammarV1ResolvedProviderOperation
  { resolvedProviderOperationKey :: ProviderOperationKey
  , resolvedProviderOperationReference :: GenericStaticActual
  , resolvedProviderOperationContract :: ProviderOperationContract
  }
  deriving (Eq, Show)

-- | Closed provider contract after exact operation-resolution correspondence has
-- been established. Declaration identity and checked law/lifecycle propositions
-- remain alongside Core's provider contract because Core 'ProviderContract'
-- intentionally carries only the public interface revision and operation map.
data GrammarV1ResolvedProviderContract = GrammarV1ResolvedProviderContract
  { resolvedProviderDeclarationKey :: DeclarationKey
  , resolvedProviderCoreContract :: ProviderContract
  , resolvedProviderLaws :: [(Text, Proposition, [FocusStep])]
  , resolvedProviderLifecycle :: [(Text, Proposition, [FocusStep])]
  }
  deriving (Eq, Show)

data GrammarV1ProviderContractConstructionError
  = ProviderOperationResolutionCountMismatch Int Int
  | ProviderOperationResolutionMismatch
      Int
      ProviderOperationKey
      GenericStaticActual
      ProviderOperationKey
      GenericStaticActual
  | ProviderContractDuplicateOperationKey ProviderOperationKey
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

-- | Assemble Core's closed provider-contract carrier only after the competent
-- callable/static layer supplies one resolved operation contract for every exact
-- source operation reference in the same order. No name lookup, callable
-- qualification, effect/resource inference, law discharge, or implementation
-- correspondence occurs here.
--
-- Duplicate source operation keys reject before Map construction so Haskell's
-- finite-map representation cannot silently overwrite one declaration with
-- another. This is the first point at which the source list is intentionally
-- converted to Core's unique operation-key map.
grammarV1ConstructClosedProviderContract
  :: GrammarV1CheckedProviderContractSurface
  -> [GrammarV1ResolvedProviderOperation]
  -> Either GrammarV1ProviderContractConstructionError GrammarV1ResolvedProviderContract
grammarV1ConstructClosedProviderContract surface resolved = do
  checkResolutionShape 0 expected actual
  case firstDuplicateKey Set.empty (map fst expected) of
    Just duplicate -> Left (ProviderContractDuplicateOperationKey duplicate)
    Nothing -> Right GrammarV1ResolvedProviderContract
      { resolvedProviderDeclarationKey = checkedProviderDeclarationKey surface
      , resolvedProviderCoreContract = ProviderContract
          { providerContractInterfaceRevision = checkedProviderInterfaceRevision surface
          , providerContractOperations = Map.fromList
              [ (resolvedProviderOperationKey operation, resolvedProviderOperationContract operation)
              | operation <- resolved
              ]
          }
      , resolvedProviderLaws = checkedProviderLaws surface
      , resolvedProviderLifecycle = checkedProviderLifecycle surface
      }
  where
    expected = checkedProviderOperationReferences surface
    actual =
      [ (resolvedProviderOperationKey operation, resolvedProviderOperationReference operation)
      | operation <- resolved
      ]

checkResolutionShape
  :: Int
  -> [(ProviderOperationKey, GenericStaticActual)]
  -> [(ProviderOperationKey, GenericStaticActual)]
  -> Either GrammarV1ProviderContractConstructionError ()
checkResolutionShape _ expected actual
  | length expected /= length actual =
      Left (ProviderOperationResolutionCountMismatch (length expected) (length actual))
checkResolutionShape _ [] [] = Right ()
checkResolutionShape index ((expectedKey, expectedReference) : expectedRest)
    ((actualKey, actualReference) : actualRest)
  | expectedKey == actualKey && expectedReference == actualReference =
      checkResolutionShape (index + 1) expectedRest actualRest
  | otherwise = Left (ProviderOperationResolutionMismatch
      index expectedKey expectedReference actualKey actualReference)
checkResolutionShape _ _ _ = error "provider resolution length guard failed"

firstDuplicateKey
  :: Set.Set ProviderOperationKey
  -> [ProviderOperationKey]
  -> Maybe ProviderOperationKey
firstDuplicateKey _ [] = Nothing
firstDuplicateKey seen (key : rest)
  | Set.member key seen = Just key
  | otherwise = firstDuplicateKey (Set.insert key seen) rest

unresolvedCallableReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedCallableReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing
