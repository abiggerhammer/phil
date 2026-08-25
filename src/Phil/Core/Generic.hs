module Phil.Core.Generic
  ( GenericValueParameterKey (..)
  , GenericStaticParameterKey (..)
  , StructuralPermission (..)
  , GenericStructuralUse (..)
  , GenericStructuralRequirements (..)
  , CheckedGenericStructuralInterface (..)
  , GenericStructuralError (..)
  , GenericRequirement (..)
  , CheckedProviderRefinement (..)
  , GenericEvidence (..)
  , GenericRequirementDisposition (..)
  , GenericInstantiationPolicy (..)
  , GenericInstantiationRecord (..)
  , GenericInstantiationError (..)
  , strictGenericInstantiationPolicy
  , inferGenericStructuralRequirements
  , checkGenericStructuralInterface
  , publishedStructuralRequirements
  , modeAllowsStructuralPermission
  , checkGenericStructuralActual
  , checkGenericInstantiation
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (InterfaceRevision)
import Phil.Core.Syntax (Mode (..), Proposition)

-- | Stable checked identity for one abstract value parameter in the bounded
-- Phase 1 generic structural checker. Surface spelling is deliberately absent.
newtype GenericValueParameterKey = GenericValueParameterKey
  { unGenericValueParameterKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Stable checked identity for a non-term static generic parameter such as an
-- abstract provider contract. This is semantic parameter identity, not the
-- human-facing source spelling used to locate it.
newtype GenericStaticParameterKey = GenericStaticParameterKey
  { unGenericStaticParameterKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | ADR-002 structural permissions induced by a generic body. These are not a
-- parallel Copy/Drop trait system: they are the existing structural rules made
-- explicit as generic requirements.
data StructuralPermission
  = WeakeningPermission
  | ContractionPermission
  deriving (Eq, Ord, Show)

-- | Checked semantic use events emitted by generic body checking. A transfer
-- moves the unique occurrence and needs no extra structural permission.
-- Discarding requires weakening; duplicating requires contraction.
data GenericStructuralUse
  = TransferGenericValue GenericValueParameterKey
  | DiscardGenericValue GenericValueParameterKey
  | DuplicateGenericValue GenericValueParameterKey
  deriving (Eq, Ord, Show)

newtype GenericStructuralRequirements = GenericStructuralRequirements
  { genericStructuralPermissions :: Set.Set StructuralPermission
  }
  deriving (Eq, Ord, Show)

-- | The two requirement views that Phase 1 must keep distinct. The induced set
-- is the minimum justified by the current checked body. The published set is
-- the stable interface contract callers must satisfy. Published requirements
-- may deliberately be stronger, but never weaker, than the induced set.
data CheckedGenericStructuralInterface = CheckedGenericStructuralInterface
  { genericInducedStructuralRequirements
      :: Map.Map GenericValueParameterKey GenericStructuralRequirements
  , genericPublishedStructuralRequirements
      :: Map.Map GenericValueParameterKey GenericStructuralRequirements
  }
  deriving (Eq, Ord, Show)

data GenericStructuralError
  = DuplicateGenericValueParameter GenericValueParameterKey
  | UnknownGenericValueParameter GenericValueParameterKey
  | DuplicatePublishedStructuralRequirement GenericValueParameterKey
  | UnknownPublishedGenericValueParameter GenericValueParameterKey
  | PublishedStructuralRequirementTooWeak
      GenericValueParameterKey
      StructuralPermission
  | MissingStructuralPermission
      GenericValueParameterKey
      StructuralPermission
      Mode
  deriving (Eq, Ord, Show)

-- | Canonical public requirement forms for the first Phase 1 instantiation
-- tranche. Provider and proposition requirements are exact semantic objects;
-- nominal operation supersets or merely available operations do not satisfy
-- them without an explicit checked relation/evidence disposition.
data GenericRequirement
  = GenericStructuralRequirement
      GenericValueParameterKey
      StructuralPermission
  | GenericProviderContractRequirement
      GenericStaticParameterKey
      InterfaceRevision
  | GenericPropositionRequirement Proposition
  deriving (Eq, Ord, Show)

-- | An already checked provider refinement/projection supplied by the competent
-- provider layer. This checker verifies that it connects the exact actual and
-- required interface revisions; proving the refinement itself remains an
-- ADR-021/provider-qualification responsibility.
data CheckedProviderRefinement = CheckedProviderRefinement
  { checkedProviderRefinementActual :: InterfaceRevision
  , checkedProviderRefinementRequired :: InterfaceRevision
  , checkedProviderRefinementWitness :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact proposition evidence accepted by the assurance layer. The bounded
-- tranche records the proposition and evidence lineage identity; wider
-- subject/context validity remains the assurance checker's competence boundary.
data GenericEvidence = GenericEvidence
  { genericEvidenceProposition :: Proposition
  , genericEvidenceIdentity :: Text
  }
  deriving (Eq, Ord, Show)

-- | Requirement-discharge metadata. These dispositions explain why one exact
-- public requirement is closed in the current context; they do not redefine
-- requirement identity and are not yet generic semantic-application identity.
data GenericRequirementDisposition
  = GenericSatisfiedByStructuralMode Mode
  | GenericSatisfiedByExactProvider InterfaceRevision
  | GenericSatisfiedByCheckedProviderRefinement CheckedProviderRefinement
  | GenericSatisfiedByEvidence GenericEvidence
  | GenericAssumptionDependent Text
  | GenericExported Text
  deriving (Eq, Ord, Show)

-- | Boundary policy controls whether explicit assumption/export dispositions
-- are admissible here. Missing requirements never become assumptions by default.
data GenericInstantiationPolicy = GenericInstantiationPolicy
  { genericPolicyAllowsAssumptions :: Bool
  , genericPolicyAllowsExports :: Bool
  }
  deriving (Eq, Ord, Show)

strictGenericInstantiationPolicy :: GenericInstantiationPolicy
strictGenericInstantiationPolicy = GenericInstantiationPolicy
  { genericPolicyAllowsAssumptions = False
  , genericPolicyAllowsExports = False
  }

newtype GenericInstantiationRecord = GenericInstantiationRecord
  { genericInstantiationDispositions
      :: Map.Map GenericRequirement GenericRequirementDisposition
  }
  deriving (Eq, Ord, Show)

data GenericInstantiationError
  = DuplicateGenericRequirementDisposition GenericRequirement
  | MissingGenericRequirementDisposition GenericRequirement
  | UnexpectedGenericRequirementDisposition GenericRequirement
  | GenericRequirementDispositionKindMismatch
      GenericRequirement
      GenericRequirementDisposition
  | GenericProviderInterfaceMismatch
      GenericStaticParameterKey
      InterfaceRevision
      InterfaceRevision
  | GenericProviderRefinementMismatch
      GenericStaticParameterKey
      InterfaceRevision
      InterfaceRevision
      InterfaceRevision
  | GenericPropositionEvidenceMismatch Proposition Proposition
  | GenericAssumptionNotPermitted GenericRequirement
  | GenericExportNotPermitted GenericRequirement
  | GenericStructuralInstantiationError GenericStructuralError
  deriving (Eq, Ord, Show)

-- | Infer the canonical minimum structural requirements induced by the checked
-- use events for every declared abstract value parameter. The resulting map
-- contains every parameter, including those with the empty requirement set.
inferGenericStructuralRequirements
  :: [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
inferGenericStructuralRequirements parameters uses = do
  requirements <- initialRequirements parameters
  foldl addUse (Right requirements) uses
  where
    addUse accumulated use = do
      current <- accumulated
      let key = useParameter use
      existing <- maybe
        (Left (UnknownGenericValueParameter key))
        Right
        (Map.lookup key current)
      let permission = case use of
            TransferGenericValue _ -> Nothing
            DiscardGenericValue _ -> Just WeakeningPermission
            DuplicateGenericValue _ -> Just ContractionPermission
          updated = case permission of
            Nothing -> existing
            Just required -> GenericStructuralRequirements
              (Set.insert required (genericStructuralPermissions existing))
      Right (Map.insert key updated current)

-- | Check the current body-induced minimum against an optional explicitly
-- stabilized public contract. With no explicit declaration, the public
-- requirement set is exactly the inferred minimum. With an explicit contract,
-- omitted parameters mean an empty published set; declared requirements may be
-- stronger than the current body but cannot omit any induced permission.
checkGenericStructuralInterface
  :: [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> Maybe [(GenericValueParameterKey, GenericStructuralRequirements)]
  -> Either GenericStructuralError CheckedGenericStructuralInterface
checkGenericStructuralInterface parameters uses explicitPublished = do
  induced <- inferGenericStructuralRequirements parameters uses
  published <- case explicitPublished of
    Nothing -> Right induced
    Just declarations -> normalizePublishedRequirements parameters declarations
  ensurePublishedCoversInduced induced published
  Right CheckedGenericStructuralInterface
    { genericInducedStructuralRequirements = induced
    , genericPublishedStructuralRequirements = published
    }

-- | Lift the stabilized structural interface into the canonical generic
-- requirement vocabulary used by instantiation. Empty per-parameter requirement
-- sets contribute no external requirement.
publishedStructuralRequirements
  :: CheckedGenericStructuralInterface
  -> Set.Set GenericRequirement
publishedStructuralRequirements interface = Set.fromList
  [ GenericStructuralRequirement key permission
  | (key, requirements) <-
      Map.toAscList (genericPublishedStructuralRequirements interface)
  , permission <- Set.toAscList (genericStructuralPermissions requirements)
  ]

-- | Structural mode satisfaction relation inherited directly from ADR-002:
-- unrestricted permits contraction and weakening, affine permits weakening,
-- and linear permits neither.
modeAllowsStructuralPermission :: Mode -> StructuralPermission -> Bool
modeAllowsStructuralPermission mode permission = case (mode, permission) of
  (Unrestricted, _) -> True
  (Affine, WeakeningPermission) -> True
  (Affine, ContractionPermission) -> False
  (Linear, _) -> False

-- | Check one concrete actual against the exact inferred or published
-- structural requirement set supplied by the caller. Failure identifies the
-- first missing canonical permission.
checkGenericStructuralActual
  :: GenericValueParameterKey
  -> Mode
  -> GenericStructuralRequirements
  -> Either GenericStructuralError ()
checkGenericStructuralActual key mode requirements =
  case
    [ permission
    | permission <- Set.toAscList (genericStructuralPermissions requirements)
    , not (modeAllowsStructuralPermission mode permission)
    ] of
      [] -> Right ()
      permission : _ -> Left (MissingStructuralPermission key permission mode)

-- | Check exact public requirement discharge for one generic instantiation.
-- Requirements are canonicalized as a set; duplicate disposition entries fail
-- closed, every requirement needs exactly one explicit disposition, and extra
-- dispositions for requirements the generic interface did not expose reject.
checkGenericInstantiation
  :: GenericInstantiationPolicy
  -> Set.Set GenericRequirement
  -> [(GenericRequirement, GenericRequirementDisposition)]
  -> Either GenericInstantiationError GenericInstantiationRecord
checkGenericInstantiation policy requirements dispositionEntries = do
  dispositions <- normalizeDispositions dispositionEntries
  case
    [ requirement
    | requirement <- Set.toAscList requirements
    , not (Map.member requirement dispositions)
    ] of
      requirement : _ -> Left (MissingGenericRequirementDisposition requirement)
      [] -> pure ()
  case
    [ requirement
    | requirement <- Map.keys dispositions
    , not (Set.member requirement requirements)
    ] of
      requirement : _ -> Left (UnexpectedGenericRequirementDisposition requirement)
      [] -> pure ()
  mapM_
    (checkRequirementDisposition policy)
    (Map.toAscList dispositions)
  Right (GenericInstantiationRecord dispositions)

normalizeDispositions
  :: [(GenericRequirement, GenericRequirementDisposition)]
  -> Either GenericInstantiationError
      (Map.Map GenericRequirement GenericRequirementDisposition)
normalizeDispositions = go Map.empty
  where
    go result [] = Right result
    go result ((requirement, disposition) : rest)
      | Map.member requirement result =
          Left (DuplicateGenericRequirementDisposition requirement)
      | otherwise = go (Map.insert requirement disposition result) rest

checkRequirementDisposition
  :: GenericInstantiationPolicy
  -> (GenericRequirement, GenericRequirementDisposition)
  -> Either GenericInstantiationError ()
checkRequirementDisposition policy (requirement, disposition) =
  case disposition of
    GenericAssumptionDependent _
      | not (genericPolicyAllowsAssumptions policy) ->
          Left (GenericAssumptionNotPermitted requirement)
    GenericExported _
      | not (genericPolicyAllowsExports policy) ->
          Left (GenericExportNotPermitted requirement)
    _ -> checkRequirementSpecific requirement disposition

checkRequirementSpecific
  :: GenericRequirement
  -> GenericRequirementDisposition
  -> Either GenericInstantiationError ()
checkRequirementSpecific requirement disposition = case (requirement, disposition) of
  (GenericStructuralRequirement key permission, GenericSatisfiedByStructuralMode mode) ->
    mapLeft GenericStructuralInstantiationError
      (checkGenericStructuralActual
        key
        mode
        (GenericStructuralRequirements (Set.singleton permission)))
  ( GenericProviderContractRequirement key required
    , GenericSatisfiedByExactProvider actual )
      | actual == required -> Right ()
      | otherwise -> Left (GenericProviderInterfaceMismatch key required actual)
  ( GenericProviderContractRequirement key required
    , GenericSatisfiedByCheckedProviderRefinement refinement )
      | checkedProviderRefinementRequired refinement == required -> Right ()
      | otherwise -> Left
          (GenericProviderRefinementMismatch
            key
            required
            (checkedProviderRefinementActual refinement)
            (checkedProviderRefinementRequired refinement))
  (GenericPropositionRequirement expected, GenericSatisfiedByEvidence evidence)
      | genericEvidenceProposition evidence == expected -> Right ()
      | otherwise -> Left
          (GenericPropositionEvidenceMismatch
            expected
            (genericEvidenceProposition evidence))
  (_, GenericAssumptionDependent _) -> Right ()
  (_, GenericExported _) -> Right ()
  _ -> Left (GenericRequirementDispositionKindMismatch requirement disposition)

initialRequirements
  :: [GenericValueParameterKey]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
initialRequirements = go Set.empty Map.empty
  where
    go _ result [] = Right result
    go seen result (key : rest)
      | Set.member key seen = Left (DuplicateGenericValueParameter key)
      | otherwise = go
          (Set.insert key seen)
          (Map.insert key (GenericStructuralRequirements Set.empty) result)
          rest

normalizePublishedRequirements
  :: [GenericValueParameterKey]
  -> [(GenericValueParameterKey, GenericStructuralRequirements)]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
normalizePublishedRequirements parameters declarations = do
  initial <- initialRequirements parameters
  go Set.empty initial declarations
  where
    go _ result [] = Right result
    go seen result ((key, requirements) : rest)
      | Set.member key seen = Left (DuplicatePublishedStructuralRequirement key)
      | not (Map.member key result) = Left (UnknownPublishedGenericValueParameter key)
      | otherwise = go
          (Set.insert key seen)
          (Map.insert key requirements result)
          rest

ensurePublishedCoversInduced
  :: Map.Map GenericValueParameterKey GenericStructuralRequirements
  -> Map.Map GenericValueParameterKey GenericStructuralRequirements
  -> Either GenericStructuralError ()
ensurePublishedCoversInduced induced published =
  mapM_ checkOne (Map.toAscList induced)
  where
    checkOne (key, inducedRequirements) =
      let publishedRequirements = Map.findWithDefault
            (GenericStructuralRequirements Set.empty)
            key
            published
          missing = Set.difference
            (genericStructuralPermissions inducedRequirements)
            (genericStructuralPermissions publishedRequirements)
      in case Set.toAscList missing of
          [] -> Right ()
          permission : _ -> Left
            (PublishedStructuralRequirementTooWeak key permission)

useParameter :: GenericStructuralUse -> GenericValueParameterKey
useParameter use = case use of
  TransferGenericValue key -> key
  DiscardGenericValue key -> key
  DuplicateGenericValue key -> key

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
