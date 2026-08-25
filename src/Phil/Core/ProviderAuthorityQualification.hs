{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderAuthorityQualification
  ( OpaqueProviderBoundaryKey (..)
  , ProviderAuthorityInventoryRevision (..)
  , ProviderAuthorityConfinementEvidenceKey (..)
  , ProviderAuthorityAssumptionKey (..)
  , ProviderAuthorityTcbBoundaryKey (..)
  , ProviderAuthorityAbiShapeKey (..)
  , ProviderAuthoritySubject (..)
  , ProviderAuthorityInventoryBasis (..)
  , ProviderExtraAuthorityDisposition (..)
  , ProviderAuthorityQualificationSpec (..)
  , CheckedProviderAuthorityQualification (..)
  , ProviderAuthorityQualificationError (..)
  , semanticProviderAuthoritySubject
  , checkProviderAuthorityQualification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.AuthorityConfinement
  ( AuthorityUse
  , CheckedClosureAuthorityConfinement (..)
  )
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification (..)
  )
import Phil.Core.Static (DefinitionRevision, InterfaceRevision)

newtype OpaqueProviderBoundaryKey = OpaqueProviderBoundaryKey
  { unOpaqueProviderBoundaryKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderAuthorityInventoryRevision = ProviderAuthorityInventoryRevision
  { unProviderAuthorityInventoryRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderAuthorityConfinementEvidenceKey = ProviderAuthorityConfinementEvidenceKey
  { unProviderAuthorityConfinementEvidenceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderAuthorityAssumptionKey = ProviderAuthorityAssumptionKey
  { unProviderAuthorityAssumptionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderAuthorityTcbBoundaryKey = ProviderAuthorityTcbBoundaryKey
  { unProviderAuthorityTcbBoundaryKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderAuthorityAbiShapeKey = ProviderAuthorityAbiShapeKey
  { unProviderAuthorityAbiShapeKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact implementation subject for the provider-authority qualification layer.
-- Pure semantic implementations are tied to the provider contract and definition
-- revisions already accepted by PROV-001--005. Opaque/foreign implementations
-- instead bind the authority claim directly to one exact runtime/service boundary.
data ProviderAuthoritySubject
  = SemanticProviderAuthoritySubject InterfaceRevision DefinitionRevision
  | OpaqueForeignProviderAuthoritySubject InterfaceRevision OpaqueProviderBoundaryKey
  deriving (Eq, Ord, Show)

-- | Justification for treating the declared internal-authority set as complete
-- enough for this conditional qualification claim. ABI shape is deliberately a
-- represented-but-invalid option so AUTH-006 can reject that inference exactly.
data ProviderAuthorityInventoryBasis
  = CheckedPurePhilAuthorityInventory ProviderAuthorityInventoryRevision
  | ForeignAuthorityInventoryByEvidence ProviderAuthorityConfinementEvidenceKey
  | ForeignAuthorityInventoryAssumption ProviderAuthorityAssumptionKey
  | ForeignAuthorityInventoryTcbBoundary ProviderAuthorityTcbBoundaryKey
  | ForeignAuthorityInventoryFromAbiShape ProviderAuthorityAbiShapeKey
  deriving (Eq, Ord, Show)

-- | Exact disposition for one authority grant present internally but absent from
-- the client-visible provider authority surface.
data ProviderExtraAuthorityDisposition
  = ExtraAuthorityStaticallyConfined
  | ExtraAuthorityExternallyConfined ProviderAuthorityConfinementEvidenceKey
  | ExtraAuthorityAssumptionDependent ProviderAuthorityAssumptionKey
  | ExtraAuthorityTcbBoundary ProviderAuthorityTcbBoundaryKey
  | ExtraAuthorityAssertedAbsentFromAbi ProviderAuthorityAbiShapeKey
  deriving (Eq, Ord, Show)

data ProviderAuthorityQualificationSpec = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject :: ProviderAuthoritySubject
  , providerAuthorityInventoryBasis :: ProviderAuthorityInventoryBasis
  , providerAuthorityClientVisible :: Set.Set AuthorityUse
  , providerAuthorityInternal :: Set.Set AuthorityUse
  , providerAuthorityPurePhilConfinements :: [CheckedClosureAuthorityConfinement]
  , providerAuthorityExtraDispositions
      :: Map.Map AuthorityUse ProviderExtraAuthorityDisposition
  }
  deriving (Eq, Ord, Show)

data CheckedProviderAuthorityQualification = CheckedProviderAuthorityQualification
  { checkedProviderAuthoritySubject :: ProviderAuthoritySubject
  , checkedProviderAuthorityInventoryBasis :: ProviderAuthorityInventoryBasis
  , checkedProviderAuthorityClientVisible :: Set.Set AuthorityUse
  , checkedProviderAuthorityInternal :: Set.Set AuthorityUse
  , checkedProviderAuthorityExtra :: Set.Set AuthorityUse
  , checkedProviderAuthorityStaticReachable :: Set.Set AuthorityUse
  , checkedProviderAuthorityStaticPublic :: Set.Set AuthorityUse
  , checkedProviderAuthorityDispositions
      :: Map.Map AuthorityUse ProviderExtraAuthorityDisposition
  }
  deriving (Eq, Ord, Show)

data ProviderAuthorityQualificationError
  = ProviderAuthoritySemanticSubjectRevisionMismatch
      ProviderAuthoritySubject InterfaceRevision DefinitionRevision
  | ProviderAuthorityPurePhilInventoryRequired ProviderAuthorityInventoryBasis
  | ProviderAuthorityForeignInventoryRequiresEvidenceOrBoundary
      ProviderAuthorityInventoryBasis
  | ProviderAuthorityAbiInventoryIsNotEvidence ProviderAuthorityAbiShapeKey
  | ProviderAuthorityStaticReachabilityUnderreported (Set.Set AuthorityUse)
  | ProviderAuthorityStaticPublicEscape (Set.Set AuthorityUse)
  | ProviderAuthorityStaticExerciseOutsidePublic (Set.Set AuthorityUse)
  | ProviderAuthorityMissingExtraDispositions (Set.Set AuthorityUse)
  | ProviderAuthorityUnexpectedExtraDispositions (Set.Set AuthorityUse)
  | ProviderAuthorityStaticConfinementUnavailable AuthorityUse
  | ProviderAuthorityStaticConfinementInvalidForOpaque AuthorityUse
  | ProviderAuthorityAbiAbsenceIsNotConfinement
      AuthorityUse ProviderAuthorityAbiShapeKey
  deriving (Eq, Ord, Show)

semanticProviderAuthoritySubject
  :: CheckedProviderSemanticQualification
  -> ProviderAuthoritySubject
semanticProviderAuthoritySubject checked = SemanticProviderAuthoritySubject
  (checkedProviderContractRevision checked)
  (checkedProviderImplementationRevision checked)

-- | Check the PROV-009 / AUTH-006 authority layer of one provider qualification.
--
-- The declared internal-authority inventory and every extra internal grant are
-- separate obligations. Pure Phil may justify an extra grant through an already
-- checked closure confinement relation. Opaque foreign code must not use static
-- Phil confinement to justify ambient authority and must not infer absence from
-- ABI shape. External evidence, assumptions, and TCB boundaries remain explicit
-- conditional qualification facts whose later build admission is policy-owned.
checkProviderAuthorityQualification
  :: Maybe CheckedProviderSemanticQualification
  -> ProviderAuthorityQualificationSpec
  -> Either ProviderAuthorityQualificationError CheckedProviderAuthorityQualification
checkProviderAuthorityQualification maybeSemantic spec = do
  checkSubject
  checkInventoryBasis
  checkStaticSummaries
  checkDispositionDomain
  mapM_ checkDisposition (Map.toAscList dispositions)
  Right CheckedProviderAuthorityQualification
    { checkedProviderAuthoritySubject = subject
    , checkedProviderAuthorityInventoryBasis = inventoryBasis
    , checkedProviderAuthorityClientVisible = clientVisible
    , checkedProviderAuthorityInternal = internal
    , checkedProviderAuthorityExtra = extra
    , checkedProviderAuthorityStaticReachable = staticReachable
    , checkedProviderAuthorityStaticPublic = staticPublic
    , checkedProviderAuthorityDispositions = dispositions
    }
  where
    subject = providerAuthoritySubject spec
    inventoryBasis = providerAuthorityInventoryBasis spec
    clientVisible = providerAuthorityClientVisible spec
    internal = providerAuthorityInternal spec
    dispositions = providerAuthorityExtraDispositions spec
    extra = Set.difference internal clientVisible

    staticReachable = foldr
      (Set.union . checkedClosureReachableAuthority)
      Set.empty
      (providerAuthorityPurePhilConfinements spec)
    staticPublic = foldr
      (Set.union . checkedClosurePublicMediatedAuthority)
      Set.empty
      (providerAuthorityPurePhilConfinements spec)
    staticExercised = foldr
      (Set.union . checkedClosureExercisedAuthority)
      Set.empty
      (providerAuthorityPurePhilConfinements spec)

    checkSubject = case (subject, maybeSemantic) of
      (SemanticProviderAuthoritySubject required actual, Just checked)
        | required == checkedProviderContractRevision checked
          && actual == checkedProviderImplementationRevision checked -> Right ()
        | otherwise -> Left (ProviderAuthoritySemanticSubjectRevisionMismatch
            subject
            (checkedProviderContractRevision checked)
            (checkedProviderImplementationRevision checked))
      (SemanticProviderAuthoritySubject required actual, Nothing) ->
        Left (ProviderAuthoritySemanticSubjectRevisionMismatch subject required actual)
      (OpaqueForeignProviderAuthoritySubject _ _, _) -> Right ()

    checkInventoryBasis = case subject of
      SemanticProviderAuthoritySubject _ _ -> case inventoryBasis of
        CheckedPurePhilAuthorityInventory _ -> Right ()
        _ -> Left (ProviderAuthorityPurePhilInventoryRequired inventoryBasis)
      OpaqueForeignProviderAuthoritySubject _ _ -> case inventoryBasis of
        ForeignAuthorityInventoryByEvidence _ -> Right ()
        ForeignAuthorityInventoryAssumption _ -> Right ()
        ForeignAuthorityInventoryTcbBoundary _ -> Right ()
        ForeignAuthorityInventoryFromAbiShape abi ->
          Left (ProviderAuthorityAbiInventoryIsNotEvidence abi)
        _ -> Left (ProviderAuthorityForeignInventoryRequiresEvidenceOrBoundary inventoryBasis)

    checkStaticSummaries
      | not (Set.null underreported) =
          Left (ProviderAuthorityStaticReachabilityUnderreported underreported)
      | not (Set.null publicEscape) =
          Left (ProviderAuthorityStaticPublicEscape publicEscape)
      | not (Set.null exercisedEscape) =
          Left (ProviderAuthorityStaticExerciseOutsidePublic exercisedEscape)
      | otherwise = Right ()
      where
        underreported = Set.difference staticReachable internal
        publicEscape = Set.difference staticPublic clientVisible
        exercisedEscape = Set.difference staticExercised clientVisible

    checkDispositionDomain
      | not (Set.null missing) =
          Left (ProviderAuthorityMissingExtraDispositions missing)
      | not (Set.null unexpected) =
          Left (ProviderAuthorityUnexpectedExtraDispositions unexpected)
      | otherwise = Right ()
      where
        dispositionKeys = Map.keysSet dispositions
        missing = Set.difference extra dispositionKeys
        unexpected = Set.difference dispositionKeys extra

    checkDisposition (authority, disposition) = case disposition of
      ExtraAuthorityStaticallyConfined -> case subject of
        OpaqueForeignProviderAuthoritySubject _ _ ->
          Left (ProviderAuthorityStaticConfinementInvalidForOpaque authority)
        SemanticProviderAuthoritySubject _ _
          | Set.member authority staticReachable
              && not (Set.member authority staticPublic)
              && not (Set.member authority staticExercised) -> Right ()
          | otherwise -> Left (ProviderAuthorityStaticConfinementUnavailable authority)
      ExtraAuthorityExternallyConfined _ -> Right ()
      ExtraAuthorityAssumptionDependent _ -> Right ()
      ExtraAuthorityTcbBoundary _ -> Right ()
      ExtraAuthorityAssertedAbsentFromAbi abi ->
        Left (ProviderAuthorityAbiAbsenceIsNotConfinement authority abi)
