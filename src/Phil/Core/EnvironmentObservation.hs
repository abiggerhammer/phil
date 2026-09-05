{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.EnvironmentObservation
  ( EnvironmentObservationRelationKey (..)
  , EnvironmentObservationKind (..)
  , EnvironmentObservationProvenance (..)
  , EnvironmentObservationContext
  , EnvironmentObservationSource (..)
  , CheckedEnvironmentObservation
  , checkedEnvironmentObservationRelationKey
  , checkedEnvironmentObservationKind
  , checkedEnvironmentObservationProvenance
  , EnvironmentObservationError (..)
  , emptyEnvironmentObservationContext
  , registerEntryEnvironmentObservation
  , registerProviderEnvironmentObservation
  , registerCapabilityEnvironmentObservation
  , registerProtocolEnvironmentObservation
  , registerBoundaryEnvironmentObservation
  , registerAssumptionEnvironmentObservation
  , registerDeploymentEnvironmentObservation
  , checkEnvironmentObservation
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityContractKey
  , AuthorityOperationKey
  , AuthorityRequirement (..)
  , AuthoritySubjectKey
  , CheckedAuthorityExercise (..)
  )
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification (..)
  , ProviderOperationKey
  )
import Phil.Core.Static
  ( DefinitionRevision
  , InterfaceRevision
  )

-- | Stable semantic identity for one explicitly admitted environmental
-- observation relation. This is not a runtime handle, symbol, registry key, or
-- ambient service name.
newtype EnvironmentObservationRelationKey = EnvironmentObservationRelationKey
  { unEnvironmentObservationRelationKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Runtime facts which would make ordinary computation nondeterministic or
-- host-dependent if they could be observed implicitly. The open-ended case
-- keeps the competence boundary general rather than turning this into a finite
-- blacklist of today's host APIs.
data EnvironmentObservationKind
  = EnvironmentClockTime
  | EnvironmentRandomness
  | EnvironmentVariable Text
  | EnvironmentLocale
  | EnvironmentHostIdentity
  | EnvironmentProcessIdentity
  | EnvironmentThreadIdentity
  | EnvironmentWorkerIdentity
  | EnvironmentSchedulerState
  | EnvironmentFilesystemState Text
  | EnvironmentDeviceState Text
  | EnvironmentOtherObservation Text
  deriving (Eq, Ord, Show)

-- | The exact semantic route by which an environmental observation entered
-- Phil. These are source/architecture contract categories, not target
-- mechanisms. Provider and capability provenance retain checked semantic
-- identity from the existing Phase-1 authorities.
data EnvironmentObservationProvenance
  = EnvironmentEntryProvenance Text
  | EnvironmentProviderProvenance
      InterfaceRevision
      DefinitionRevision
      ProviderOperationKey
  | EnvironmentCapabilityProvenance
      AuthorityContractKey
      AuthoritySubjectKey
      AuthorityOperationKey
  | EnvironmentProtocolProvenance Text
  | EnvironmentBoundaryProvenance Text
  | EnvironmentAssumptionProvenance Text
  | EnvironmentDeploymentProvenance Text
  deriving (Eq, Ord, Show)

data EnvironmentObservationRelation = EnvironmentObservationRelation
  { environmentObservationRelationKey :: EnvironmentObservationRelationKey
  , environmentObservationRelationKind :: EnvironmentObservationKind
  , environmentObservationRelationProvenance :: EnvironmentObservationProvenance
  }
  deriving (Eq, Ord, Show)

newtype EnvironmentObservationContext = EnvironmentObservationContext
  { environmentObservationRelations
      :: Map.Map EnvironmentObservationRelationKey EnvironmentObservationRelation
  }
  deriving (Eq, Show)

-- | A runtime or backend object is deliberately not an observation relation.
-- Only a key already present in EnvironmentObservationContext can authorize the
-- observation. There is no fallback from any ambient form to a matching name.
data EnvironmentObservationSource
  = ExplicitEnvironmentObservation EnvironmentObservationRelationKey
  | AmbientEnvironmentObservation EnvironmentObservationKind
  | RuntimeEnvironmentHandle Text
  | BackendEnvironmentSymbol Text
  | AmbientEnvironmentRegistryEntry Text
  deriving (Eq, Ord, Show)

data CheckedEnvironmentObservation = CheckedEnvironmentObservation
  { checkedEnvironmentObservationRelationKey :: EnvironmentObservationRelationKey
  , checkedEnvironmentObservationKind :: EnvironmentObservationKind
  , checkedEnvironmentObservationProvenance :: EnvironmentObservationProvenance
  }
  deriving (Eq, Ord, Show)

data EnvironmentObservationError
  = DuplicateEnvironmentObservationRelation EnvironmentObservationRelationKey
  | UnknownEnvironmentObservationRelation EnvironmentObservationRelationKey
  | EnvironmentObservationSourceNotExplicit EnvironmentObservationSource
  | EnvironmentObservationKindMismatch
      EnvironmentObservationKind
      EnvironmentObservationKind
  | EnvironmentObservationProviderOperationNotQualified ProviderOperationKey
  deriving (Eq, Show)

emptyEnvironmentObservationContext :: EnvironmentObservationContext
emptyEnvironmentObservationContext = EnvironmentObservationContext Map.empty

registerEntryEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> Text
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerEntryEnvironmentObservation key kind entryIdentity =
  registerRelation key kind (EnvironmentEntryProvenance entryIdentity)

-- | Provider observations may be registered only from an already checked
-- provider semantic qualification and an operation actually present in that
-- exact qualification. Runtime symbols cannot substitute for this relation.
registerProviderEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> CheckedProviderSemanticQualification
  -> ProviderOperationKey
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerProviderEnvironmentObservation key kind checkedProvider operation context =
  if Map.member operation (checkedProviderOperations checkedProvider)
    then registerRelation key kind
      (EnvironmentProviderProvenance
        (checkedProviderContractRevision checkedProvider)
        (checkedProviderImplementationRevision checkedProvider)
        operation)
      context
    else Left (EnvironmentObservationProviderOperationNotQualified operation)

-- | Capability observations similarly consume an already checked authority
-- exercise. Possessing a runtime handle or finding an ambient registry entry is
-- not enough; PHIL-AUTH-POSSESS-001 must already have accepted the exact
-- contract/subject/operation relation.
registerCapabilityEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> CheckedAuthorityExercise
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerCapabilityEnvironmentObservation key kind checkedExercise =
  let requirement = checkedAuthorityRequirement checkedExercise
  in registerRelation key kind
      (EnvironmentCapabilityProvenance
        (requiredAuthorityContract requirement)
        (requiredAuthoritySubject requirement)
        (requiredAuthorityOperation requirement))

registerProtocolEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> Text
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerProtocolEnvironmentObservation key kind protocolIdentity =
  registerRelation key kind (EnvironmentProtocolProvenance protocolIdentity)

registerBoundaryEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> Text
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerBoundaryEnvironmentObservation key kind boundaryIdentity =
  registerRelation key kind (EnvironmentBoundaryProvenance boundaryIdentity)

registerAssumptionEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> Text
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerAssumptionEnvironmentObservation key kind assumptionIdentity =
  registerRelation key kind (EnvironmentAssumptionProvenance assumptionIdentity)

registerDeploymentEnvironmentObservation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> Text
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerDeploymentEnvironmentObservation key kind deploymentIdentity =
  registerRelation key kind (EnvironmentDeploymentProvenance deploymentIdentity)

-- | Admit one environmental observation only through an exact relation already
-- installed by a competent explicit source/architecture boundary. Ordinary Phil
-- therefore has no ambient clock, randomness, process identity, filesystem, or
-- similar observation primitive merely because a target runtime exposes one.
checkEnvironmentObservation
  :: EnvironmentObservationKind
  -> EnvironmentObservationSource
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError CheckedEnvironmentObservation
checkEnvironmentObservation requested source context = case source of
  ExplicitEnvironmentObservation key -> do
    relation <- maybe
      (Left (UnknownEnvironmentObservationRelation key))
      Right
      (Map.lookup key (environmentObservationRelations context))
    let actual = environmentObservationRelationKind relation
    if actual == requested
      then Right CheckedEnvironmentObservation
        { checkedEnvironmentObservationRelationKey =
            environmentObservationRelationKey relation
        , checkedEnvironmentObservationKind = actual
        , checkedEnvironmentObservationProvenance =
            environmentObservationRelationProvenance relation
        }
      else Left (EnvironmentObservationKindMismatch requested actual)
  _ -> Left (EnvironmentObservationSourceNotExplicit source)

registerRelation
  :: EnvironmentObservationRelationKey
  -> EnvironmentObservationKind
  -> EnvironmentObservationProvenance
  -> EnvironmentObservationContext
  -> Either EnvironmentObservationError EnvironmentObservationContext
registerRelation key kind provenance (EnvironmentObservationContext relations)
  | Map.member key relations = Left (DuplicateEnvironmentObservationRelation key)
  | otherwise = Right (EnvironmentObservationContext
      (Map.insert key EnvironmentObservationRelation
        { environmentObservationRelationKey = key
        , environmentObservationRelationKind = kind
        , environmentObservationRelationProvenance = provenance
        }
        relations))
