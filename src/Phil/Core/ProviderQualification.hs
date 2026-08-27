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

import qualified ProviderQualificationKernel as Kernel
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
  | ProviderQualificationRepresentationMismatch Text
  deriving (Eq, Ord, Show)

checkProviderSemanticQualification
  :: ProviderContract
  -> ProviderImplementation
  -> ProviderQualificationClaim
  -> Either ProviderQualificationError CheckedProviderSemanticQualification
checkProviderSemanticQualification contract implementation claim
  | not (providerProjectionRoundTrips contract implementation claim) =
      Left (ProviderQualificationRepresentationMismatch
        "provider Map/Set projection failed canonical round-trip")
  | providerKernelAccepts contract implementation claim =
      case checkProviderSemanticQualificationDetailed contract implementation claim of
        Right checked -> Right checked
        Left _ -> Left (ProviderQualificationRepresentationMismatch
          "extracted provider kernel accepted while diagnostic reconstruction rejected")
  | otherwise =
      case checkProviderSemanticQualificationDetailed contract implementation claim of
        Left err -> Left err
        Right _ -> Left (ProviderQualificationRepresentationMismatch
          "extracted provider kernel rejected while diagnostic reconstruction accepted")

checkProviderSemanticQualificationDetailed
  :: ProviderContract
  -> ProviderImplementation
  -> ProviderQualificationClaim
  -> Either ProviderQualificationError CheckedProviderSemanticQualification
checkProviderSemanticQualificationDetailed contract implementation claim
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

providerKernelAccepts
  :: ProviderContract
  -> ProviderImplementation
  -> ProviderQualificationClaim
  -> Bool
providerKernelAccepts contract implementation claim =
  Kernel.decideProviderQualification
    (==)
    (==)
    (==)
    (==)
    operationAccepts
    (providerQualificationRequiredInterface claim ==
      providerContractInterfaceRevision contract)
    (providerQualificationImplementationRevision claim ==
      providerImplementationDefinitionRevision implementation)
    contractProjection
    correspondenceProjection
    implementationProjection
  where
    contractProjection =
      [ (operationKey,
          ( operationContract
          , Map.toAscList (providerOperationOutcomeResidues operationContract)
          ))
      | (operationKey, operationContract) <-
          Map.toAscList (providerContractOperations contract)
      ]
    correspondenceProjection =
      [ (operationKey,
          ( providerCorrespondenceImplementationEntry correspondence
          , Map.toAscList (providerCorrespondenceOutcomes correspondence)
          ))
      | (operationKey, correspondence) <-
          Map.toAscList (providerQualificationOperationCorrespondences claim)
      ]
    implementationProjection =
      [ (entryKey,
          ( implementationOperation
          , Map.toAscList
              (providerImplementationOutcomeResidues implementationOperation)
          ))
      | (entryKey, implementationOperation) <-
          Map.toAscList (providerImplementationEntries implementation)
      ]
    operationAccepts operationContract implementationOperation =
      case checkCallableRefinement
          (providerOperationCallableContract operationContract)
          (providerImplementationCallable implementationOperation) of
        Left _ -> False
        Right _ -> Set.isSubsetOf
          (providerImplementationPreconditions implementationOperation)
          (providerOperationPreconditions operationContract)

providerProjectionRoundTrips
  :: ProviderContract
  -> ProviderImplementation
  -> ProviderQualificationClaim
  -> Bool
providerProjectionRoundTrips contract implementation claim =
  and
    [ mapRoundTrips (providerContractOperations contract)
    , all contractOperationRoundTrips
        (Map.elems (providerContractOperations contract))
    , mapRoundTrips (providerImplementationEntries implementation)
    , all implementationOperationRoundTrips
        (Map.elems (providerImplementationEntries implementation))
    , mapRoundTrips (providerQualificationOperationCorrespondences claim)
    , all correspondenceRoundTrips
        (Map.elems (providerQualificationOperationCorrespondences claim))
    ]
  where
    contractOperationRoundTrips operation =
      setRoundTrips (providerOperationPreconditions operation) &&
      mapRoundTrips (providerOperationOutcomeResidues operation) &&
      all residueRoundTrips
        (Map.elems (providerOperationOutcomeResidues operation))
    implementationOperationRoundTrips operation =
      setRoundTrips (providerImplementationPreconditions operation) &&
      mapRoundTrips (providerImplementationOutcomeResidues operation) &&
      all residueRoundTrips
        (Map.elems (providerImplementationOutcomeResidues operation))
    correspondenceRoundTrips correspondence =
      mapRoundTrips (providerCorrespondenceOutcomes correspondence)

residueRoundTrips :: ProviderResourceResidue -> Bool
residueRoundTrips residue = and
  [ setRoundTrips (providerResidueBorrowedInputs residue)
  , setRoundTrips (providerResidueConsumedInputs residue)
  , setRoundTrips (providerResidueReturnedPredecessors residue)
  , setRoundTrips (providerResidueSuccessors residue)
  , setRoundTrips (providerResidueProducedResources residue)
  ]

mapRoundTrips :: (Ord key, Eq value) => Map.Map key value -> Bool
mapRoundTrips values = Map.fromAscList (Map.toAscList values) == values

setRoundTrips :: Ord value => Set.Set value -> Bool
setRoundTrips values = Set.fromAscList (Set.toAscList values) == values
