module Phil.Surface.GrammarV1.GenericProviderImplementationSurface
  ( GrammarV1ResolvedGenericProviderParameter (..)
  , GrammarV1CheckedGenericProviderImplementationSurface (..)
  , GrammarV1GenericProviderImplementationSurfaceError (..)
  , grammarV1CheckedGenericProviderImplementationSurface
  ) where

import qualified Data.Set as Set
import Phil.Core.Generic
  ( GenericRequirement (..)
  , GenericStaticParameterKey
  )
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind
  , GenericStaticParameter (..)
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1GenericKindCategory
  , grammarV1GenericRequirementCategory
  )
import Phil.Surface.GrammarV1.GenericDischarge
  ( GrammarV1CheckedGenericRequirement (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1GenericParam (..)
  , GrammarV1GenericRequirement
  , GrammarV1ProviderImplementationDecl (..)
  )
import Phil.Surface.GrammarV1.ProviderImplementationSurface
  ( GrammarV1CheckedProviderImplementationSurface
  , GrammarV1ProviderImplementationSurfaceError
  , grammarV1CheckedClosedProviderImplementationSurface
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact binder-resolution evidence for one generic parameter on an ordinary
-- provider implementation. The full located source occurrence is repeated so
-- this SURF-008 bridge can verify correspondence without deriving a stable
-- GenericStaticParameterKey from source spelling. SURF-009 owns the resolution
-- that creates this evidence.
data GrammarV1ResolvedGenericProviderParameter =
  GrammarV1ResolvedGenericProviderParameter
    { resolvedGenericProviderSourceParameter :: Located GrammarV1GenericParam
    , resolvedGenericProviderParameter :: GenericStaticParameter
    }
  deriving (Eq, Show)

-- | Intermediate checked generic-provider surface. The ordinary provider body
-- and item semantics are exactly the #637 checked surface; this wrapper adds the
-- already-resolved static parameter schema and already-checked Core-backed
-- generic requirements in source order. It still does not construct or qualify a
-- Core ProviderImplementation.
data GrammarV1CheckedGenericProviderImplementationSurface =
  GrammarV1CheckedGenericProviderImplementationSurface
    { checkedGenericProviderParameters :: [GenericStaticParameter]
    , checkedGenericProviderRequirements :: [GrammarV1CheckedGenericRequirement]
    , checkedGenericProviderOrdinarySurface
        :: GrammarV1CheckedProviderImplementationSurface
    }
  deriving (Eq, Show)

data GrammarV1GenericProviderImplementationSurfaceError
  = GrammarV1GenericProviderParameterEvidenceCountMismatch Int Int
  | GrammarV1GenericProviderParameterSourceMismatch
      Int
      (Located GrammarV1GenericParam)
      (Located GrammarV1GenericParam)
  | GrammarV1GenericProviderParameterKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
      GenericStaticKind
  | GrammarV1DuplicateGenericProviderParameterKey GenericStaticParameterKey
  | GrammarV1GenericProviderRequirementEvidenceCountMismatch Int Int
  | GrammarV1GenericProviderRequirementSourceMismatch
      Int
      (Located GrammarV1GenericRequirement)
      (Located GrammarV1GenericRequirement)
  | GrammarV1GenericProviderRequirementCategoryMismatch
      Int
      GenericRequirementCategory
      GenericRequirementCategory
  | GrammarV1GenericProviderOrdinarySurfaceError
      GrammarV1ProviderImplementationSurfaceError
  deriving (Eq, Show)

-- | Check a generic ordinary provider implementation by composing existing
-- authorities rather than inventing generic/provider semantics.
--
-- At least one generic parameter or requirement must be present; the closed
-- fragment remains owned by grammarV1CheckedClosedProviderImplementationSurface.
-- Every source parameter must have one exact caller-supplied resolution in source
-- order, with the same Core static kind and a distinct stable key. Every source
-- requirement must belong to the concrete Core-backed subset (structural,
-- proposition, provider) and correspond exactly, in source order, to an existing
-- GrammarV1CheckedGenericRequirement produced by the generic requirement bridge.
-- Category agreement is rechecked here so a checked object for another source
-- category cannot be silently attached.
--
-- Once the generic wrapper is checked, a copy of the same source declaration with
-- only its generic parameter/requirement lists cleared is delegated to the #637
-- ordinary-provider surface. Contract references, operation callable references,
-- source item order, proposition focusing and binder-free body checking therefore
-- keep exactly the same semantics and failures as the non-generic path.
--
-- This function does not resolve binders, infer a requirement, discharge one,
-- instantiate a generic application, construct/qualify ProviderImplementation,
-- infer callable outcomes/preconditions, discharge laws/lifecycle obligations,
-- establish authority confinement, or choose realization.
grammarV1CheckedGenericProviderImplementationSurface
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> [GrammarV1ResolvedGenericProviderParameter]
  -> [GrammarV1CheckedGenericRequirement]
  -> GrammarV1ProviderImplementationDecl
  -> Maybe
      (Either
        GrammarV1GenericProviderImplementationSurfaceError
        GrammarV1CheckedGenericProviderImplementationSurface)
grammarV1CheckedGenericProviderImplementationSurface
    staticContext
    declarationKey
    definitionRevision
    parameterEvidence
    requirementEvidence
    source
  | null sourceParameters && null sourceRequirements = Nothing
  | not (all (coreBackedRequirement . locatedValue) sourceRequirements) = Nothing
  | otherwise = do
      ordinary <- grammarV1CheckedClosedProviderImplementationSurface
        staticContext
        declarationKey
        definitionRevision
        closedSource
      pure $ do
        parameters <- validateParameters sourceParameters parameterEvidence
        requirements <- validateRequirements sourceRequirements requirementEvidence
        checkedOrdinary <- mapLeft
          GrammarV1GenericProviderOrdinarySurfaceError
          ordinary
        Right GrammarV1CheckedGenericProviderImplementationSurface
          { checkedGenericProviderParameters = parameters
          , checkedGenericProviderRequirements = requirements
          , checkedGenericProviderOrdinarySurface = checkedOrdinary
          }
  where
    sourceParameters = grammarV1ProviderImplementationGenericParams source
    sourceRequirements = grammarV1ProviderImplementationRequirements source
    closedSource = source
      { grammarV1ProviderImplementationGenericParams = []
      , grammarV1ProviderImplementationRequirements = []
      }

validateParameters
  :: [Located GrammarV1GenericParam]
  -> [GrammarV1ResolvedGenericProviderParameter]
  -> Either
      GrammarV1GenericProviderImplementationSurfaceError
      [GenericStaticParameter]
validateParameters sourceParameters evidence
  | length sourceParameters /= length evidence = Left
      (GrammarV1GenericProviderParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))
  | otherwise = go 0 Set.empty sourceParameters evidence
  where
    go _ _ [] [] = Right []
    go index keys (sourceParameter : sourceRest) (resolved : resolvedRest)
      | sourceParameter /= resolvedGenericProviderSourceParameter resolved = Left
          (GrammarV1GenericProviderParameterSourceMismatch
            index
            sourceParameter
            (resolvedGenericProviderSourceParameter resolved))
      | actualKind /= expectedKind = Left
          (GrammarV1GenericProviderParameterKindMismatch
            key
            expectedKind
            actualKind)
      | Set.member key keys = Left
          (GrammarV1DuplicateGenericProviderParameterKey key)
      | otherwise = do
          rest <- go
            (index + 1)
            (Set.insert key keys)
            sourceRest
            resolvedRest
          Right (parameter : rest)
      where
        parameter = resolvedGenericProviderParameter resolved
        key = genericStaticParameterKey parameter
        expectedKind = grammarV1GenericKindCategory
          (locatedValue (grammarV1GenericParamKind (locatedValue sourceParameter)))
        actualKind = genericStaticParameterKind parameter
    go _ _ _ _ = Left
      (GrammarV1GenericProviderParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))

validateRequirements
  :: [Located GrammarV1GenericRequirement]
  -> [GrammarV1CheckedGenericRequirement]
  -> Either
      GrammarV1GenericProviderImplementationSurfaceError
      [GrammarV1CheckedGenericRequirement]
validateRequirements sourceRequirements evidence
  | length sourceRequirements /= length evidence = Left
      (GrammarV1GenericProviderRequirementEvidenceCountMismatch
        (length sourceRequirements)
        (length evidence))
  | otherwise = go 0 sourceRequirements evidence
  where
    go _ [] [] = Right []
    go index (sourceRequirement : sourceRest) (checked : checkedRest)
      | sourceRequirement /= checkedGenericRequirementSource checked = Left
          (GrammarV1GenericProviderRequirementSourceMismatch
            index
            sourceRequirement
            (checkedGenericRequirementSource checked))
      | actualCategory /= expectedCategory = Left
          (GrammarV1GenericProviderRequirementCategoryMismatch
            index
            expectedCategory
            actualCategory)
      | otherwise = do
          rest <- go (index + 1) sourceRest checkedRest
          Right (checked : rest)
      where
        expectedCategory = grammarV1GenericRequirementCategory
          (locatedValue sourceRequirement)
        actualCategory = coreRequirementCategory
          (checkedGenericRequirementCore checked)
    go _ _ _ = Left
      (GrammarV1GenericProviderRequirementEvidenceCountMismatch
        (length sourceRequirements)
        (length evidence))

coreBackedRequirement :: GrammarV1GenericRequirement -> Bool
coreBackedRequirement requirement =
  grammarV1GenericRequirementCategory requirement `elem`
    [ GenericStructuralCategory
    , GenericPropositionCategory
    , GenericProviderCategory
    ]

coreRequirementCategory :: GenericRequirement -> GenericRequirementCategory
coreRequirementCategory requirement = case requirement of
  GenericStructuralRequirement {} -> GenericStructuralCategory
  GenericProviderContractRequirement {} -> GenericProviderCategory
  GenericPropositionRequirement {} -> GenericPropositionCategory

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
