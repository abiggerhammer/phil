{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderQualification
  ( ProviderOperationKey (..)
  , ProviderImplementationEntryKey (..)
  , ProviderPreconditionKey (..)
  , ProviderOutcomeKey (..)
  , ProviderResourceKey (..)
  , ProviderResourceResidue (..)
  , ProviderOperationContract (..)
  , ProviderContract (..)
  , ProviderImplementationOperation (..)
  , ProviderImplementation (..)
  , ProviderOperationCorrespondence (..)
  , ProviderQualificationClaim (..)
  , CheckedProviderOperationQualification (..)
  , CheckedProviderSemanticQualification (..)
  , ProviderQualificationError (..)
  , checkProviderSemanticQualification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CallableRefinement
  ( CallableRefinementError
  , CallableRefinementSurface
  , CheckedCallableRefinement
  , checkCallableRefinement
  )
import Phil.Core.Static (DefinitionRevision, InterfaceRevision)

newtype ProviderOperationKey = ProviderOperationKey
  { unProviderOperationKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderImplementationEntryKey = ProviderImplementationEntryKey
  { unProviderImplementationEntryKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderPreconditionKey = ProviderPreconditionKey
  { unProviderPreconditionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderOutcomeKey = ProviderOutcomeKey
  { unProviderOutcomeKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderResourceKey = ProviderResourceKey
  { unProviderResourceKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact continuing/outcome-specific resource behavior visible at one provider
-- operation boundary. These categories stay distinct so a nominally equal
-- result cannot hide a borrow/consume/return/successor mismatch.
data ProviderResourceResidue = ProviderResourceResidue
  { providerResidueBorrowedInputs :: Set.Set ProviderResourceKey
  , providerResidueConsumedInputs :: Set.Set ProviderResourceKey
  , providerResidueReturnedPredecessors :: Set.Set ProviderResourceKey
  , providerResidueSuccessors :: Set.Set ProviderResourceKey
  , providerResidueProducedResources :: Set.Set ProviderResourceKey
  }
  deriving (Eq, Ord, Show)

data ProviderOperationContract = ProviderOperationContract
  { providerOperationCallableContract :: CallableRefinementSurface
  , providerOperationPreconditions :: Set.Set ProviderPreconditionKey
  , providerOperationOutcomeResidues
      :: Map.Map ProviderOutcomeKey ProviderResourceResidue
  }
  deriving (Eq, Ord, Show)

data ProviderContract = ProviderContract
  { providerContractInterfaceRevision :: InterfaceRevision
  , providerContractOperations :: Map.Map ProviderOperationKey ProviderOperationContract
  }
  deriving (Eq, Ord, Show)

data ProviderImplementationOperation = ProviderImplementationOperation
  { providerImplementationCallable :: CallableRefinementSurface
  , providerImplementationPreconditions :: Set.Set ProviderPreconditionKey
  , providerImplementationOutcomeResidues
      :: Map.Map ProviderOutcomeKey ProviderResourceResidue
  }
  deriving (Eq, Ord, Show)

data ProviderImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision :: DefinitionRevision
  , providerImplementationEntries
      :: Map.Map ProviderImplementationEntryKey ProviderImplementationOperation
  , providerImplementationSymbols :: Set.Set Text
  }
  deriving (Eq, Ord, Show)

-- | Explicit semantic operation relation. Runtime/source symbol identity is not
-- part of the relation. Every implementation outcome is mapped explicitly to
-- one public contract outcome so residue checking stays branch-sensitive.
data ProviderOperationCorrespondence = ProviderOperationCorrespondence
  { providerCorrespondenceImplementationEntry :: ProviderImplementationEntryKey
  , providerCorrespondenceOutcomes :: Map.Map ProviderOutcomeKey ProviderOutcomeKey
  }
  deriving (Eq, Ord, Show)

data ProviderQualificationClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface :: InterfaceRevision
  , providerQualificationImplementationRevision :: DefinitionRevision
  , providerQualificationOperationCorrespondences
      :: Map.Map ProviderOperationKey ProviderOperationCorrespondence
  }
  deriving (Eq, Ord, Show)

data CheckedProviderOperationQualification = CheckedProviderOperationQualification
  { checkedProviderOperationKey :: ProviderOperationKey
  , checkedProviderImplementationEntry :: ProviderImplementationEntryKey
  , checkedProviderCallableRefinement :: CheckedCallableRefinement
  , checkedProviderOutcomeCorrespondence :: Map.Map ProviderOutcomeKey ProviderOutcomeKey
  }
  deriving (Eq, Ord, Show)

data CheckedProviderSemanticQualification = CheckedProviderSemanticQualification
  { checkedProviderContractRevision :: InterfaceRevision
  , checkedProviderImplementationRevision :: DefinitionRevision
  , checkedProviderOperations
      :: Map.Map ProviderOperationKey CheckedProviderOperationQualification
  }
  deriving (Eq, Ord, Show)

data ProviderQualificationError
  = ProviderQualificationContractRevisionMismatch InterfaceRevision InterfaceRevision
  | ProviderQualificationImplementationRevisionMismatch DefinitionRevision DefinitionRevision
  | ProviderQualificationMissingOperationCorrespondences (Set.Set ProviderOperationKey)
  | ProviderQualificationUnexpectedOperationCorrespondences (Set.Set ProviderOperationKey)
  | ProviderQualificationUnknownImplementationEntry
      ProviderOperationKey ProviderImplementationEntryKey
  | ProviderQualificationCallableRefinementFailed
      ProviderOperationKey CallableRefinementError
  | ProviderQualificationStrongerPreconditions
      ProviderOperationKey (Set.Set ProviderPreconditionKey)
  | ProviderQualificationMissingOutcomeCorrespondences
      ProviderOperationKey (Set.Set ProviderOutcomeKey)
  | ProviderQualificationUnexpectedOutcomeCorrespondences
      ProviderOperationKey (Set.Set ProviderOutcomeKey)
  | ProviderQualificationUnknownContractOutcome
      ProviderOperationKey ProviderOutcomeKey ProviderOutcomeKey
  | ProviderQualificationResourceResidueMismatch
      ProviderOperationKey ProviderOutcomeKey ProviderOutcomeKey
      ProviderResourceResidue ProviderResourceResidue
  deriving (Eq, Ord, Show)

-- | Close the stateless semantic core of one pure-Phil provider qualification.
-- Whole-provider state/laws/lifecycle/authority/evidence obligations are later
-- layers; this checker establishes the exact total operation correspondence and
-- per-operation semantic refinement they depend on.
checkProviderSemanticQualification
  :: ProviderContract
  -> ProviderImplementation
  -> ProviderQualificationClaim
  -> Either ProviderQualificationError CheckedProviderSemanticQualification
checkProviderSemanticQualification contract implementation claim
  | providerQualificationRequiredInterface claim /= providerContractInterfaceRevision contract =
      Left (ProviderQualificationContractRevisionMismatch
        (providerContractInterfaceRevision contract)
        (providerQualificationRequiredInterface claim))
  | providerQualificationImplementationRevision claim /= providerImplementationDefinitionRevision implementation =
      Left (ProviderQualificationImplementationRevisionMismatch
        (providerImplementationDefinitionRevision implementation)
        (providerQualificationImplementationRevision claim))
  | not (Set.null missingOperations) =
      Left (ProviderQualificationMissingOperationCorrespondences missingOperations)
  | not (Set.null unexpectedOperations) =
      Left (ProviderQualificationUnexpectedOperationCorrespondences unexpectedOperations)
  | otherwise = do
      checked <- Map.traverseWithKey checkOperation contractOperations
      Right CheckedProviderSemanticQualification
        { checkedProviderContractRevision = providerContractInterfaceRevision contract
        , checkedProviderImplementationRevision = providerImplementationDefinitionRevision implementation
        , checkedProviderOperations = checked
        }
  where
    contractOperations = providerContractOperations contract
    correspondences = providerQualificationOperationCorrespondences claim
    contractKeys = Map.keysSet contractOperations
    correspondenceKeys = Map.keysSet correspondences
    missingOperations = Set.difference contractKeys correspondenceKeys
    unexpectedOperations = Set.difference correspondenceKeys contractKeys

    checkOperation operationKey operationContract = do
      correspondence <- case Map.lookup operationKey correspondences of
        Just value -> Right value
        Nothing -> Left (ProviderQualificationMissingOperationCorrespondences
          (Set.singleton operationKey))
      let entryKey = providerCorrespondenceImplementationEntry correspondence
      implementationOperation <- case Map.lookup entryKey (providerImplementationEntries implementation) of
        Just value -> Right value
        Nothing -> Left (ProviderQualificationUnknownImplementationEntry operationKey entryKey)
      callableRefinement <- case checkCallableRefinement
          (providerOperationCallableContract operationContract)
          (providerImplementationCallable implementationOperation) of
        Right checked -> Right checked
        Left err -> Left (ProviderQualificationCallableRefinementFailed operationKey err)
      let excessPreconditions = Set.difference
            (providerImplementationPreconditions implementationOperation)
            (providerOperationPreconditions operationContract)
      if not (Set.null excessPreconditions)
        then Left (ProviderQualificationStrongerPreconditions operationKey excessPreconditions)
        else do
          checkOutcomes operationKey operationContract implementationOperation correspondence
          Right CheckedProviderOperationQualification
            { checkedProviderOperationKey = operationKey
            , checkedProviderImplementationEntry = entryKey
            , checkedProviderCallableRefinement = callableRefinement
            , checkedProviderOutcomeCorrespondence = providerCorrespondenceOutcomes correspondence
            }

    checkOutcomes operationKey operationContract implementationOperation correspondence = do
      let implementationOutcomes = providerImplementationOutcomeResidues implementationOperation
          outcomeCorrespondence = providerCorrespondenceOutcomes correspondence
          implementationOutcomeKeys = Map.keysSet implementationOutcomes
          mappedOutcomeKeys = Map.keysSet outcomeCorrespondence
          missingOutcomeMappings = Set.difference implementationOutcomeKeys mappedOutcomeKeys
          unexpectedOutcomeMappings = Set.difference mappedOutcomeKeys implementationOutcomeKeys
      if not (Set.null missingOutcomeMappings)
        then Left (ProviderQualificationMissingOutcomeCorrespondences
          operationKey missingOutcomeMappings)
        else if not (Set.null unexpectedOutcomeMappings)
          then Left (ProviderQualificationUnexpectedOutcomeCorrespondences
            operationKey unexpectedOutcomeMappings)
          else mapM_ (checkOutcome operationKey operationContract implementationOutcomes)
            (Map.toAscList outcomeCorrespondence)

    checkOutcome operationKey operationContract implementationOutcomes
        (implementationOutcomeKey, contractOutcomeKey) = do
      implementationResidue <- case Map.lookup implementationOutcomeKey implementationOutcomes of
        Just value -> Right value
        Nothing -> Left (ProviderQualificationUnexpectedOutcomeCorrespondences
          operationKey (Set.singleton implementationOutcomeKey))
      contractResidue <- case Map.lookup contractOutcomeKey
          (providerOperationOutcomeResidues operationContract) of
        Just value -> Right value
        Nothing -> Left (ProviderQualificationUnknownContractOutcome
          operationKey implementationOutcomeKey contractOutcomeKey)
      if implementationResidue == contractResidue
        then Right ()
        else Left (ProviderQualificationResourceResidueMismatch
          operationKey implementationOutcomeKey contractOutcomeKey
          contractResidue implementationResidue)
