{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderLifecycleQualification
  ( ProviderLifecycleRevision (..)
  , ProviderObservationBoundaryKey (..)
  , ProviderInterruptionPointKey (..)
  , ProviderObservableStateKey (..)
  , ProviderRetryDisposition (..)
  , ProviderLifecyclePoint (..)
  , ProviderLifecycleAllowance (..)
  , ProviderInterruptionObservation (..)
  , ProviderLifecycleContract (..)
  , ProviderLifecycleModel (..)
  , CheckedProviderLifecycleQualification (..)
  , ProviderLifecycleQualificationError (..)
  , checkProviderLifecycleQualification
  ) where

import qualified ProviderLifecycleQualificationKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification (..)
  , ProviderOperationKey
  , ProviderResourceResidue (..)
  )
import Phil.Core.Static (DefinitionRevision, InterfaceRevision)

newtype ProviderLifecycleRevision = ProviderLifecycleRevision
  { unProviderLifecycleRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderObservationBoundaryKey = ProviderObservationBoundaryKey
  { unProviderObservationBoundaryKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderInterruptionPointKey = ProviderInterruptionPointKey
  { unProviderInterruptionPointKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderObservableStateKey = ProviderObservableStateKey
  { unProviderObservableStateKey :: Text
  }
  deriving (Eq, Ord, Show)

data ProviderRetryDisposition
  = ProviderRetryForbidden
  | ProviderRetrySameOperation
  | ProviderRetryFromObservableState ProviderObservableStateKey
  deriving (Eq, Ord, Show)

-- | One exact public operation/interruption point at which lifecycle behavior is
-- in scope.  Interruption points are semantic model locations, not source lines
-- or machine addresses.
data ProviderLifecyclePoint = ProviderLifecyclePoint
  { providerLifecyclePointOperation :: ProviderOperationKey
  , providerLifecyclePointInterruption :: ProviderInterruptionPointKey
  }
  deriving (Eq, Ord, Show)

-- | Public lifecycle allowance at one interruption point.  Observable state,
-- cleanup residue, and retry behavior remain separate so normal-return success
-- cannot hide a forbidden partial commit or resource leak.
data ProviderLifecycleAllowance = ProviderLifecycleAllowance
  { providerLifecycleAllowedObservableStates :: Set.Set ProviderObservableStateKey
  , providerLifecycleAllowedCleanupResidues :: Set.Set ProviderResourceResidue
  , providerLifecycleAllowedRetryDispositions :: Set.Set ProviderRetryDisposition
  }
  deriving (Eq, Ord, Show)

-- | One modeled implementation observation at an in-scope interruption point.
data ProviderInterruptionObservation = ProviderInterruptionObservation
  { providerInterruptionObservationBoundary :: ProviderObservationBoundaryKey
  , providerInterruptionObservableState :: ProviderObservableStateKey
  , providerInterruptionCleanupResidue :: ProviderResourceResidue
  , providerInterruptionRetryDisposition :: ProviderRetryDisposition
  }
  deriving (Eq, Ord, Show)

data ProviderLifecycleContract = ProviderLifecycleContract
  { providerLifecycleRevision :: ProviderLifecycleRevision
  , providerLifecycleObservationBoundary :: ProviderObservationBoundaryKey
  , providerLifecycleAllowances
      :: Map.Map ProviderLifecyclePoint ProviderLifecycleAllowance
  }
  deriving (Eq, Ord, Show)

-- | Implementation lifecycle model supplied to qualification.  Every in-scope
-- lifecycle point has an explicit set of reachable modeled observations.  The
-- checker validates the model; completeness of the model is an assurance/evidence
-- obligation and is not inferred from tests alone.
newtype ProviderLifecycleModel = ProviderLifecycleModel
  { providerLifecycleImplementationObservations
      :: Map.Map ProviderLifecyclePoint (Set.Set ProviderInterruptionObservation)
  }
  deriving (Eq, Ord, Show)

data CheckedProviderLifecycleQualification = CheckedProviderLifecycleQualification
  { checkedProviderLifecycleContractRevision :: InterfaceRevision
  , checkedProviderLifecycleImplementationRevision :: DefinitionRevision
  , checkedProviderLifecycleRevision :: ProviderLifecycleRevision
  , checkedProviderLifecycleObservationBoundary :: ProviderObservationBoundaryKey
  , checkedProviderLifecycleObservations
      :: Map.Map ProviderLifecyclePoint (Set.Set ProviderInterruptionObservation)
  }
  deriving (Eq, Ord, Show)

data ProviderLifecycleQualificationError
  = ProviderLifecycleMissingInterruptionPoints (Set.Set ProviderLifecyclePoint)
  | ProviderLifecycleUnexpectedInterruptionPoints (Set.Set ProviderLifecyclePoint)
  | ProviderLifecycleUnqualifiedOperation ProviderLifecyclePoint
  | ProviderLifecycleObservationBoundaryMismatch
      ProviderLifecyclePoint
      ProviderObservationBoundaryKey
      ProviderObservationBoundaryKey
  | ProviderLifecycleForbiddenObservableState
      ProviderLifecyclePoint ProviderObservableStateKey
  | ProviderLifecycleForbiddenCleanupResidue
      ProviderLifecyclePoint ProviderResourceResidue
  | ProviderLifecycleForbiddenRetryDisposition
      ProviderLifecyclePoint ProviderRetryDisposition
  | ProviderLifecycleQualificationRepresentationMismatch Text
  deriving (Eq, Ord, Show)

-- | Check PROV-008 over an already accepted provider semantic qualification.
-- Ordinary returns are irrelevant here: every modeled interruption observation
-- at the declared public boundary must lie inside the lifecycle contract's
-- allowed state/cleanup/retry relation. The extracted kernel owns acceptance;
-- the detailed traversal below is retained only for diagnostics/result
-- reconstruction and must agree with that decision.
checkProviderLifecycleQualification
  :: CheckedProviderSemanticQualification
  -> ProviderLifecycleContract
  -> ProviderLifecycleModel
  -> Either ProviderLifecycleQualificationError CheckedProviderLifecycleQualification
checkProviderLifecycleQualification qualified contract model
  | not (providerLifecycleProjectionRoundTrips qualified contract model) =
      Left (ProviderLifecycleQualificationRepresentationMismatch
        "provider lifecycle Map/Set projection failed canonical round-trip")
  | providerLifecycleKernelAccepts qualified contract model =
      case checkProviderLifecycleQualificationDetailed qualified contract model of
        Right checked -> Right checked
        Left _ -> Left (ProviderLifecycleQualificationRepresentationMismatch
          "extracted provider lifecycle kernel accepted while diagnostic reconstruction rejected")
  | otherwise =
      case checkProviderLifecycleQualificationDetailed qualified contract model of
        Left err -> Left err
        Right _ -> Left (ProviderLifecycleQualificationRepresentationMismatch
          "extracted provider lifecycle kernel rejected while diagnostic reconstruction accepted")

checkProviderLifecycleQualificationDetailed
  :: CheckedProviderSemanticQualification
  -> ProviderLifecycleContract
  -> ProviderLifecycleModel
  -> Either ProviderLifecycleQualificationError CheckedProviderLifecycleQualification
checkProviderLifecycleQualificationDetailed qualified contract model
  | not (Set.null missingPoints) =
      Left (ProviderLifecycleMissingInterruptionPoints missingPoints)
  | not (Set.null unexpectedPoints) =
      Left (ProviderLifecycleUnexpectedInterruptionPoints unexpectedPoints)
  | otherwise = do
      mapM_ checkPoint (Map.toAscList allowances)
      Right CheckedProviderLifecycleQualification
        { checkedProviderLifecycleContractRevision = checkedProviderContractRevision qualified
        , checkedProviderLifecycleImplementationRevision = checkedProviderImplementationRevision qualified
        , checkedProviderLifecycleRevision = providerLifecycleRevision contract
        , checkedProviderLifecycleObservationBoundary = providerLifecycleObservationBoundary contract
        , checkedProviderLifecycleObservations = observations
        }
  where
    allowances = providerLifecycleAllowances contract
    observations = providerLifecycleImplementationObservations model
    allowancePoints = Map.keysSet allowances
    observationPoints = Map.keysSet observations
    missingPoints = Set.difference allowancePoints observationPoints
    unexpectedPoints = Set.difference observationPoints allowancePoints

    checkPoint (point, allowance) = do
      if Map.member (providerLifecyclePointOperation point) (checkedProviderOperations qualified)
        then Right ()
        else Left (ProviderLifecycleUnqualifiedOperation point)
      let pointObservations = Map.findWithDefault Set.empty point observations
      mapM_ (checkObservation point allowance) (Set.toAscList pointObservations)

    checkObservation point allowance observation
      | providerInterruptionObservationBoundary observation
          /= providerLifecycleObservationBoundary contract =
          Left (ProviderLifecycleObservationBoundaryMismatch
            point
            (providerLifecycleObservationBoundary contract)
            (providerInterruptionObservationBoundary observation))
      | not (Set.member
          (providerInterruptionObservableState observation)
          (providerLifecycleAllowedObservableStates allowance)) =
          Left (ProviderLifecycleForbiddenObservableState
            point (providerInterruptionObservableState observation))
      | not (Set.member
          (providerInterruptionCleanupResidue observation)
          (providerLifecycleAllowedCleanupResidues allowance)) =
          Left (ProviderLifecycleForbiddenCleanupResidue
            point (providerInterruptionCleanupResidue observation))
      | not (Set.member
          (providerInterruptionRetryDisposition observation)
          (providerLifecycleAllowedRetryDispositions allowance)) =
          Left (ProviderLifecycleForbiddenRetryDisposition
            point (providerInterruptionRetryDisposition observation))
      | otherwise = Right ()

providerLifecycleKernelAccepts
  :: CheckedProviderSemanticQualification
  -> ProviderLifecycleContract
  -> ProviderLifecycleModel
  -> Bool
providerLifecycleKernelAccepts qualified contract model =
  Kernel.decideProviderLifecycleQualification
    (==)
    (==)
    (==)
    (==)
    (==)
    (==)
    qualifiedOperations
    (providerLifecycleObservationBoundary contract)
    allowanceProjection
    observationProjection
  where
    qualifiedOperations = Map.keys (checkedProviderOperations qualified)
    allowanceProjection =
      [ ( lifecyclePointProjection point
        , ( Set.toAscList (providerLifecycleAllowedObservableStates allowance)
          , ( Set.toAscList (providerLifecycleAllowedCleanupResidues allowance)
            , Set.toAscList (providerLifecycleAllowedRetryDispositions allowance)
            )
          )
        )
      | (point, allowance) <- Map.toAscList (providerLifecycleAllowances contract)
      ]
    observationProjection =
      [ ( lifecyclePointProjection point
        , [ ( providerInterruptionObservationBoundary observation
            , ( providerInterruptionObservableState observation
              , ( providerInterruptionCleanupResidue observation
                , providerInterruptionRetryDisposition observation
                )
              )
            )
          | observation <- Set.toAscList pointObservations
          ]
        )
      | (point, pointObservations) <-
          Map.toAscList (providerLifecycleImplementationObservations model)
      ]

lifecyclePointProjection
  :: ProviderLifecyclePoint
  -> (ProviderOperationKey, ProviderInterruptionPointKey)
lifecyclePointProjection point =
  ( providerLifecyclePointOperation point
  , providerLifecyclePointInterruption point
  )

providerLifecycleProjectionRoundTrips
  :: CheckedProviderSemanticQualification
  -> ProviderLifecycleContract
  -> ProviderLifecycleModel
  -> Bool
providerLifecycleProjectionRoundTrips qualified contract model =
  and
    [ mapRoundTrips (checkedProviderOperations qualified)
    , mapRoundTrips allowances
    , all allowanceRoundTrips (Map.elems allowances)
    , mapRoundTrips observations
    , all observationSetRoundTrips (Map.elems observations)
    ]
  where
    allowances = providerLifecycleAllowances contract
    observations = providerLifecycleImplementationObservations model

    allowanceRoundTrips allowance = and
      [ setRoundTrips (providerLifecycleAllowedObservableStates allowance)
      , setRoundTrips (providerLifecycleAllowedCleanupResidues allowance)
      , all residueRoundTrips
          (Set.toAscList (providerLifecycleAllowedCleanupResidues allowance))
      , setRoundTrips (providerLifecycleAllowedRetryDispositions allowance)
      ]

    observationSetRoundTrips pointObservations =
      setRoundTrips pointObservations &&
      all observationRoundTrips (Set.toAscList pointObservations)

    observationRoundTrips observation =
      residueRoundTrips (providerInterruptionCleanupResidue observation)

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
