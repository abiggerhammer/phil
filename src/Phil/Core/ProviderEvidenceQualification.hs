{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderEvidenceQualification
  ( ProviderPropositionFamilyKey (..)
  , ProviderEvidenceSubjectKey (..)
  , ProviderObservationKey (..)
  , EvidenceSubjectMappingRevision (..)
  , EvidenceValidityContractKey (..)
  , ProviderEvidenceObservation (..)
  , EvidenceSubjectMapping (..)
  , ProviderEvidenceProducerRequirement (..)
  , ProviderEvidenceProducerCompetenceClaim (..)
  , CheckedProviderEvidenceProducerCompetence (..)
  , ProviderEvidenceQualificationError (..)
  , instantiateProviderEvidenceProposition
  , checkProviderEvidenceProducerCompetence
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CallableScope (LoanScopeKey)
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification (..)
  , ProviderOperationKey
  )
import Phil.Core.Static (DefinitionRevision, InterfaceRevision)
import Phil.Core.Syntax
  ( Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )

-- | Stable identity of one proposition family a provider operation may establish.
-- The family key is semantic; source function names and backend symbols are not.
newtype ProviderPropositionFamilyKey = ProviderPropositionFamilyKey
  { unProviderPropositionFamilyKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Stable semantic subject named by a persistent provider-produced proposition.
-- This is deliberately a different type from an observation handle or loan token.
newtype ProviderEvidenceSubjectKey = ProviderEvidenceSubjectKey
  { unProviderEvidenceSubjectKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Identity of one observation mechanism or transient observed view.
newtype ProviderObservationKey = ProviderObservationKey
  { unProviderObservationKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact accepted relation that maps a non-stable observation to a stable
-- semantic evidence subject. Truth of the relation is an assurance input; this
-- checker validates exact binding and subject correspondence.
newtype EvidenceSubjectMappingRevision = EvidenceSubjectMappingRevision
  { unEvidenceSubjectMappingRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Public validity contract for one evidence-producing competence. Concrete
-- proof/certificate validity evidence remains a later qualification-closure input.
newtype EvidenceValidityContractKey = EvidenceValidityContractKey
  { unEvidenceValidityContractKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Observation identity is not automatically proposition-subject identity.
-- A scoped borrow in particular is temporary even when the resulting evidence
-- is intentionally persistent and names the stable owner object.
data ProviderEvidenceObservation
  = StableEvidenceObservation ProviderEvidenceSubjectKey
  | ScopedBorrowEvidenceObservation ProviderObservationKey LoanScopeKey
  | OpaqueEvidenceObservation ProviderObservationKey
  deriving (Eq, Ord, Show)

-- | Exact subject mapping used by one competence claim. Direct identity is only
-- legal for an observation already expressed as the same stable semantic subject.
-- Pointer/handle/byte coincidence is represented explicitly so it can fail closed.
data EvidenceSubjectMapping
  = DirectStableEvidenceSubject ProviderEvidenceSubjectKey
  | CheckedObservationToStableSubject
      EvidenceSubjectMappingRevision
      ProviderEvidenceObservation
      ProviderEvidenceSubjectKey
  | RuntimeCoincidenceSubjectMapping Text
  deriving (Eq, Ord, Show)

-- | Public provider requirement for one evidence-producing operation occurrence.
data ProviderEvidenceProducerRequirement = ProviderEvidenceProducerRequirement
  { providerEvidenceRequiredOperation :: ProviderOperationKey
  , providerEvidenceRequiredFamily :: ProviderPropositionFamilyKey
  , providerEvidenceRequiredStableSubject :: ProviderEvidenceSubjectKey
  , providerEvidenceRequiredValidity :: EvidenceValidityContractKey
  }
  deriving (Eq, Ord, Show)

-- | Provider-qualification competence claim. The proposition subject is stated
-- explicitly rather than inferred from what happened to be observed at runtime.
data ProviderEvidenceProducerCompetenceClaim = ProviderEvidenceProducerCompetenceClaim
  { providerEvidenceClaimOperation :: ProviderOperationKey
  , providerEvidenceClaimFamily :: ProviderPropositionFamilyKey
  , providerEvidenceClaimObservation :: ProviderEvidenceObservation
  , providerEvidenceClaimPropositionSubject :: ProviderEvidenceSubjectKey
  , providerEvidenceClaimSubjectMapping :: EvidenceSubjectMapping
  , providerEvidenceClaimValidity :: EvidenceValidityContractKey
  }
  deriving (Eq, Ord, Show)

data CheckedProviderEvidenceProducerCompetence = CheckedProviderEvidenceProducerCompetence
  { checkedProviderEvidenceContractRevision :: InterfaceRevision
  , checkedProviderEvidenceImplementationRevision :: DefinitionRevision
  , checkedProviderEvidenceOperation :: ProviderOperationKey
  , checkedProviderEvidenceFamily :: ProviderPropositionFamilyKey
  , checkedProviderEvidenceObservation :: ProviderEvidenceObservation
  , checkedProviderEvidenceSubject :: ProviderEvidenceSubjectKey
  , checkedProviderEvidenceMapping :: EvidenceSubjectMapping
  , checkedProviderEvidenceValidity :: EvidenceValidityContractKey
  , checkedProviderEvidenceProposition :: Proposition
  }
  deriving (Eq, Ord, Show)

data ProviderEvidenceQualificationError
  = ProviderEvidenceOperationNotQualified ProviderOperationKey
  | ProviderEvidenceOperationMismatch ProviderOperationKey ProviderOperationKey
  | ProviderEvidenceFamilyMismatch
      ProviderPropositionFamilyKey ProviderPropositionFamilyKey
  | ProviderEvidenceStableSubjectMismatch
      ProviderEvidenceSubjectKey ProviderEvidenceSubjectKey
  | ProviderEvidenceValidityMismatch
      EvidenceValidityContractKey EvidenceValidityContractKey
  | ProviderEvidenceDirectMappingRequiresStableObservation
      ProviderEvidenceObservation ProviderEvidenceSubjectKey
  | ProviderEvidenceMappingObservationMismatch
      ProviderEvidenceObservation ProviderEvidenceObservation
  | ProviderEvidenceMappingSubjectMismatch
      ProviderEvidenceSubjectKey ProviderEvidenceSubjectKey
  | ProviderEvidenceRuntimeCoincidenceInsufficient Text
  deriving (Eq, Ord, Show)

-- | Materialize the bounded Core proposition established by one checked provider
-- competence. The exact stable subject is embedded as a stable-id refinement term;
-- observation/loan identity is intentionally absent.
instantiateProviderEvidenceProposition
  :: ProviderPropositionFamilyKey
  -> ProviderEvidenceSubjectKey
  -> Proposition
instantiateProviderEvidenceProposition family subject =
  Atom
    (unProviderPropositionFamilyKey family)
    [ RefOpaque
        (SortStableId "provider-evidence-subject")
        (unProviderEvidenceSubjectKey subject)
    ]

-- | Check PROV-010 over an already accepted provider semantic qualification.
-- This establishes exact operation/family/subject/mapping/validity correspondence;
-- it does not by itself prove the truth of an external observation mapping or the
-- proposition family. Those remain ordinary qualification evidence obligations.
checkProviderEvidenceProducerCompetence
  :: CheckedProviderSemanticQualification
  -> ProviderEvidenceProducerRequirement
  -> ProviderEvidenceProducerCompetenceClaim
  -> Either ProviderEvidenceQualificationError CheckedProviderEvidenceProducerCompetence
checkProviderEvidenceProducerCompetence qualified requirement claim = do
  let requiredOperation = providerEvidenceRequiredOperation requirement
      claimedOperation = providerEvidenceClaimOperation claim
      requiredFamily = providerEvidenceRequiredFamily requirement
      claimedFamily = providerEvidenceClaimFamily claim
      requiredSubject = providerEvidenceRequiredStableSubject requirement
      claimedSubject = providerEvidenceClaimPropositionSubject claim
      requiredValidity = providerEvidenceRequiredValidity requirement
      claimedValidity = providerEvidenceClaimValidity claim
  if Map.notMember requiredOperation (checkedProviderOperations qualified)
    then Left (ProviderEvidenceOperationNotQualified requiredOperation)
    else if claimedOperation /= requiredOperation
      then Left (ProviderEvidenceOperationMismatch requiredOperation claimedOperation)
      else if claimedFamily /= requiredFamily
        then Left (ProviderEvidenceFamilyMismatch requiredFamily claimedFamily)
        else if claimedSubject /= requiredSubject
          then Left (ProviderEvidenceStableSubjectMismatch requiredSubject claimedSubject)
          else if claimedValidity /= requiredValidity
            then Left (ProviderEvidenceValidityMismatch requiredValidity claimedValidity)
            else do
              checkSubjectMapping
                (providerEvidenceClaimObservation claim)
                claimedSubject
                (providerEvidenceClaimSubjectMapping claim)
              Right CheckedProviderEvidenceProducerCompetence
                { checkedProviderEvidenceContractRevision = checkedProviderContractRevision qualified
                , checkedProviderEvidenceImplementationRevision = checkedProviderImplementationRevision qualified
                , checkedProviderEvidenceOperation = requiredOperation
                , checkedProviderEvidenceFamily = requiredFamily
                , checkedProviderEvidenceObservation = providerEvidenceClaimObservation claim
                , checkedProviderEvidenceSubject = claimedSubject
                , checkedProviderEvidenceMapping = providerEvidenceClaimSubjectMapping claim
                , checkedProviderEvidenceValidity = claimedValidity
                , checkedProviderEvidenceProposition =
                    instantiateProviderEvidenceProposition requiredFamily claimedSubject
                }
  where
    checkSubjectMapping observation subject mapping = case mapping of
      DirectStableEvidenceSubject mappedSubject
        | observation == StableEvidenceObservation mappedSubject
            && mappedSubject == subject -> Right ()
        | otherwise -> Left
            (ProviderEvidenceDirectMappingRequiresStableObservation
              observation mappedSubject)
      CheckedObservationToStableSubject _ mappedObservation mappedSubject
        | mappedObservation /= observation -> Left
            (ProviderEvidenceMappingObservationMismatch observation mappedObservation)
        | mappedSubject /= subject -> Left
            (ProviderEvidenceMappingSubjectMismatch subject mappedSubject)
        | otherwise -> Right ()
      RuntimeCoincidenceSubjectMapping reason ->
        Left (ProviderEvidenceRuntimeCoincidenceInsufficient reason)
