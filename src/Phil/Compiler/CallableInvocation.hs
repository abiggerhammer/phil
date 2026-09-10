{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.CallableInvocation
  ( SourceCallableBinding (..)
  , CallableInvocationCatalog
  , CallableInvocationExpectation (..)
  , ResolvedCallableInvocation (..)
  , CallableInvocationResolutionError (..)
  , buildCallableInvocationCatalog
  , resolveCallableInvocation
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.SourceBundle
  ( CheckedSourceBundle (..)
  , CheckedSourceUnit (..)
  )
import Phil.Core.Callable
  ( CallableContract (..)
  )
import Phil.Core.CallableRefinement
  ( CallableRefinementError
  , CallableRefinementSurface (..)
  , CheckedCallableRefinement
  , checkCallableRefinement
  )
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  )
import Phil.Surface.Syntax
  ( Component (..)
  , Located (..)
  )

-- | Exact ordinary-source callable identity available to an `invoke` expression.
-- The display name is only a lookup spelling. Persisted DeclarationKey and the
-- checked callable surface remain the semantic identity and interface authority.
data SourceCallableBinding = SourceCallableBinding
  { sourceCallableDisplayName :: Text
  , sourceCallableDeclarationKey :: DeclarationKey
  , sourceCallableInterface :: CallableRefinementSurface
  }
  deriving (Eq, Ord, Show)

-- | Closed callable namespace derived from one already-checked SourceBundle.
-- Provider primitive spellings are retained separately so wrong-category lookup
-- can fail explicitly rather than falling through from one namespace to another.
data CallableInvocationCatalog = CallableInvocationCatalog
  { callableCatalogByDisplayName :: Map Text [SourceCallableBinding]
  , callableCatalogPrimitiveNames :: Set Text
  }
  deriving (Eq, Show)

-- | Caller-side exact expectation. Direct named invocation is stricter than
-- higher-order substitution about identity: the declaration key and interface
-- revision must be exact, after which the existing callable refinement kernel
-- checks the semantic surface itself.
data CallableInvocationExpectation = CallableInvocationExpectation
  { callableInvocationExpectedDeclarationKey :: DeclarationKey
  , callableInvocationExpectedInterface :: CallableRefinementSurface
  }
  deriving (Eq, Ord, Show)

data ResolvedCallableInvocation = ResolvedCallableInvocation
  { resolvedCallableBinding :: SourceCallableBinding
  , resolvedCallableRefinement :: CheckedCallableRefinement
  }
  deriving (Eq, Show)

data CallableInvocationResolutionError
  = CallableContractMissing DeclarationKey
  | CallableContractOutsideBundle DeclarationKey
  | CallableNameUnknown Text
  | CallableNameRefersOnlyToProviderPrimitive Text
  | CallableNameAmbiguous Text [DeclarationKey]
  | CallableDeclarationIdentityMismatch
      Text
      DeclarationKey
      DeclarationKey
  | CallableInterfaceRevisionMismatch
      Text
      InterfaceRevision
      InterfaceRevision
  | CallableRefinementRejected Text CallableRefinementError
  deriving (Eq, Ord, Show)

-- | Build the exact callable lookup surface from checked source lineage. Every
-- checked component must have exactly one contract supplied by DeclarationKey,
-- and the contract map may not smuggle in declarations outside the bundle.
-- Duplicate display names remain representable so resolution can reject them as
-- ambiguity at the competent lookup layer.
buildCallableInvocationCatalog
  :: Set Text
  -> Map DeclarationKey CallableRefinementSurface
  -> CheckedSourceBundle
  -> Either CallableInvocationResolutionError CallableInvocationCatalog
buildCallableInvocationCatalog primitiveNames contracts bundle = do
  let units = checkedSourceUnits bundle
      bundleKeys = Set.fromList (map checkedSourceDeclarationKey units)
      contractKeys = Map.keysSet contracts
      missing = Set.difference bundleKeys contractKeys
      extra = Set.difference contractKeys bundleKeys
  case Set.lookupMin missing of
    Just key -> Left (CallableContractMissing key)
    Nothing -> pure ()
  case Set.lookupMin extra of
    Just key -> Left (CallableContractOutsideBundle key)
    Nothing -> pure ()
  bindings <- mapM bindingFor units
  pure CallableInvocationCatalog
    { callableCatalogByDisplayName =
        Map.fromListWith (<>)
          [ (sourceCallableDisplayName binding, [binding])
          | binding <- bindings
          ]
    , callableCatalogPrimitiveNames = primitiveNames
    }
  where
    bindingFor unit = do
      let key = checkedSourceDeclarationKey unit
          name = componentName (locatedValue (checkedSourceComponent unit))
      contract <- maybe
        (Left (CallableContractMissing key))
        Right
        (Map.lookup key contracts)
      pure SourceCallableBinding
        { sourceCallableDisplayName = name
        , sourceCallableDeclarationKey = key
        , sourceCallableInterface = contract
        }

-- | Resolve an explicit source `invoke` through the callable namespace only.
-- A provider primitive with the same spelling never competes with or replaces a
-- callable. If no callable exists but a primitive does, report wrong-category
-- lookup explicitly. Exact declaration and interface revision are then checked
-- before delegating semantic compatibility to the existing refinement kernel.
resolveCallableInvocation
  :: CallableInvocationCatalog
  -> Text
  -> CallableInvocationExpectation
  -> Either CallableInvocationResolutionError ResolvedCallableInvocation
resolveCallableInvocation catalog name expectation = do
  binding <- case Map.lookup name (callableCatalogByDisplayName catalog) of
    Nothing
      | Set.member name (callableCatalogPrimitiveNames catalog) ->
          Left (CallableNameRefersOnlyToProviderPrimitive name)
      | otherwise -> Left (CallableNameUnknown name)
    Just [single] -> Right single
    Just candidates -> Left
      (CallableNameAmbiguous
        name
        (Set.toAscList
          (Set.fromList (map sourceCallableDeclarationKey candidates))))
  let expectedKey = callableInvocationExpectedDeclarationKey expectation
      actualKey = sourceCallableDeclarationKey binding
  if actualKey == expectedKey
    then pure ()
    else Left (CallableDeclarationIdentityMismatch name expectedKey actualKey)
  let expectedInterface = callableInvocationExpectedInterface expectation
      actualInterface = sourceCallableInterface binding
      expectedRevision = interfaceRevision expectedInterface
      actualRevision = interfaceRevision actualInterface
  if actualRevision == expectedRevision
    then pure ()
    else Left
      (CallableInterfaceRevisionMismatch name expectedRevision actualRevision)
  checked <- mapLeft (CallableRefinementRejected name) $
    checkCallableRefinement expectedInterface actualInterface
  pure ResolvedCallableInvocation
    { resolvedCallableBinding = binding
    , resolvedCallableRefinement = checked
    }

interfaceRevision :: CallableRefinementSurface -> InterfaceRevision
interfaceRevision =
  callableContractInterfaceRevision . callableRefinementContract

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
