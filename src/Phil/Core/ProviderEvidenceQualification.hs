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

newtype ProviderPropositionFamilyKey = ProviderPropositionFamilyKey
  { unProviderPropositionFamilyKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderEvidenceSubjectKey = ProviderEvidenceSubjectKey
  { unProviderEvidenceSubjectKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderObservationKey = ProviderObservationKey
  { unProviderObservationKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype EvidenceSubjectMappingRevision = EvidenceSubjectMappingRevision
  { unEvidenceSubjectMappingRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype EvidenceValidityContractKey = EvidenceValidityContractKey
  { unEvidenceValidityContractKey :: Text
  }
  deriving (Eq, Ord, Show)

data ProviderEvidenceObservation
  = StableEvidenceObservation ProviderEvidenceSubjectKey
  | ScopedBorrowEvidenceObservation ProviderObservationKey LoanScopeKey
  | OpaqueEvidenceObservation ProviderObservationKey
  deriving (Eq, Ord, Show)

data EvidenceSubjectMapping
  = DirectStableEvidenceSubject ProviderEvidenceSubjectKey
  | CheckedObservationToStableSubject
      EvidenceSubjectMappingRevision
      ProviderEvidenceObservation
      ProviderEvidenceSubjectKey
  | RuntimeCoincidenceSubjectMapping Text
  deriving (Eq, Ord, Show)

-- | Public provider requirement for one evidence-producing operation occurrence.
-- Proposition parameters are semantic arguments distinct from the stable subject.
-- For example, DigestMatches(id, object) carries id here while object remains the
-- separately checked stable evidence subject.
data ProviderEvidenceProducerRequirement = ProviderEvidenceProducerRequirement
  { providerEvidenceRequiredOperation :: ProviderOperationKey
  , providerEvidenceRequiredFamily :: ProviderPropositionFamilyKey
  , providerEvidenceRequiredPropositionParameters :: [RefTerm]
  , providerEvidenceRequiredStableSubject :: ProviderEvidenceSubjectKey
  , providerEvidenceRequiredValidity :: EvidenceValidityContractKey
  }
  deriving (Eq, Ord, Show)

data ProviderEvidenceProducerCompetenceClaim = ProviderEvidenceProducerCompetenceClaim
  { providerEvidenceClaimOperation :: ProviderOperationKey
  , providerEvidenceClaimFamily :: ProviderPropositionFamilyKey
  , providerEvidenceClaimPropositionParameters :: [RefTerm]
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
  , checkedProviderEvidencePropositionParameters :: [RefTerm]
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
  | ProviderEvidencePropositionParametersMismatch [RefTerm] [RefTerm]
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

instantiateProviderEvidenceProposition
  :: ProviderPropositionFamilyKey
  -> [RefTerm]
  -> ProviderEvidenceSubjectKey
  -> Proposition
instantiateProviderEvidenceProposition family parameters subject =
  Atom
    (unProviderPropositionFamilyKey family)
    (parameters <>
      [ RefOpaque
          (SortStableId "provider-evidence-subject")
          (unProviderEvidenceSubjectKey subject)
      ])

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
      requiredParameters = providerEvidenceRequiredPropositionParameters requirement
      claimedParameters = providerEvidenceClaimPropositionParameters claim
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
        else if claimedParameters /= requiredParameters
          then Left (ProviderEvidencePropositionParametersMismatch
            requiredParameters claimedParameters)
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
                  , checkedProviderEvidencePropositionParameters = requiredParameters
                  , checkedProviderEvidenceObservation = providerEvidenceClaimObservation claim
                  , checkedProviderEvidenceSubject = claimedSubject
                  , checkedProviderEvidenceMapping = providerEvidenceClaimSubjectMapping claim
                  , checkedProviderEvidenceValidity = claimedValidity
                  , checkedProviderEvidenceProposition =
                      instantiateProviderEvidenceProposition
                        requiredFamily requiredParameters claimedSubject
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
