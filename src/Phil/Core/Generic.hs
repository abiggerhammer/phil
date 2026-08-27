{-# LANGUAGE OverloadedStrings #-}

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
  , GenericApplicationIdentity (..)
  , GenericApplicationIdentityError (..)
  , GenericDischargeLineage (..)
  , strictGenericInstantiationPolicy
  , inferGenericStructuralRequirements
  , checkGenericStructuralInterface
  , publishedStructuralRequirements
  , modeAllowsStructuralPermission
  , checkGenericStructuralActual
  , checkGenericInstantiation
  , deriveGenericApplicationIdentity
  , genericApplicationSemanticForm
  , deriveGenericDischargeLineage
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified GenericStructuralKernel as Kernel
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax (Mode (..), Proposition)

newtype GenericValueParameterKey = GenericValueParameterKey
  { unGenericValueParameterKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype GenericStaticParameterKey = GenericStaticParameterKey
  { unGenericStaticParameterKey :: Text
  }
  deriving (Eq, Ord, Show)

data StructuralPermission
  = WeakeningPermission
  | ContractionPermission
  deriving (Eq, Ord, Show)

data GenericStructuralUse
  = TransferGenericValue GenericValueParameterKey
  | DiscardGenericValue GenericValueParameterKey
  | DuplicateGenericValue GenericValueParameterKey
  deriving (Eq, Ord, Show)

newtype GenericStructuralRequirements = GenericStructuralRequirements
  { genericStructuralPermissions :: Set.Set StructuralPermission
  }
  deriving (Eq, Ord, Show)

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
  | GenericStructuralKernelBridgeMismatch GenericValueParameterKey
  deriving (Eq, Ord, Show)

data GenericRequirement
  = GenericStructuralRequirement
      GenericValueParameterKey
      StructuralPermission
  | GenericProviderContractRequirement
      GenericStaticParameterKey
      InterfaceRevision
  | GenericPropositionRequirement Proposition
  deriving (Eq, Ord, Show)

data CheckedProviderRefinement = CheckedProviderRefinement
  { checkedProviderRefinementActual :: InterfaceRevision
  , checkedProviderRefinementRequired :: InterfaceRevision
  , checkedProviderRefinementWitness :: Text
  }
  deriving (Eq, Ord, Show)

data GenericEvidence = GenericEvidence
  { genericEvidenceProposition :: Proposition
  , genericEvidenceIdentity :: Text
  }
  deriving (Eq, Ord, Show)

data GenericRequirementDisposition
  = GenericSatisfiedByStructuralMode Mode
  | GenericSatisfiedByExactProvider InterfaceRevision
  | GenericSatisfiedByCheckedProviderRefinement CheckedProviderRefinement
  | GenericSatisfiedByEvidence GenericEvidence
  | GenericAssumptionDependent Text
  | GenericExported Text
  deriving (Eq, Ord, Show)

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

data GenericApplicationIdentity = GenericApplicationIdentity
  { genericApplicationDeclarationKey :: DeclarationKey
  , genericApplicationInterfaceRevision :: InterfaceRevision
  , genericApplicationSemanticArguments
      :: Map.Map GenericStaticParameterKey SemanticForm
  }
  deriving (Eq, Ord, Show)

data GenericApplicationIdentityError
  = DuplicateGenericSemanticArgument GenericStaticParameterKey
  deriving (Eq, Ord, Show)

data GenericDischargeLineage = GenericDischargeLineage
  { genericDischargeApplicationIdentity :: GenericApplicationIdentity
  , genericDischargeDefinitionRevision :: DefinitionRevision
  , genericDischargeDispositions
      :: Map.Map GenericRequirement GenericRequirementDisposition
  }
  deriving (Eq, Ord, Show)

inferGenericStructuralRequirements
  :: [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
inferGenericStructuralRequirements parameters uses = do
  initial <- initialRequirements parameters
  grouped <- foldl groupUse (Right (Map.map (const []) initial)) uses
  Map.traverseWithKey materialize grouped
  where
    groupUse accumulated use = do
      current <- accumulated
      let key = useParameter use
      if Map.member key current
        then Right (Map.adjust (toKernelUse use :) key current)
        else Left (UnknownGenericValueParameter key)

    materialize key reversedUses =
      requirementsFromKernel key
        (Kernel.inferGenericStructuralRequirements (reverse reversedUses))

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

publishedStructuralRequirements
  :: CheckedGenericStructuralInterface
  -> Set.Set GenericRequirement
publishedStructuralRequirements interface = Set.fromList
  [ GenericStructuralRequirement key permission
  | (key, requirements) <-
      Map.toAscList (genericPublishedStructuralRequirements interface)
  , permission <- Set.toAscList (genericStructuralPermissions requirements)
  ]

modeAllowsStructuralPermission :: Mode -> StructuralPermission -> Bool
modeAllowsStructuralPermission mode permission =
  Kernel.modeAllowsStructuralPermission
    (toKernelMode mode)
    (toKernelPermission permission)

checkGenericStructuralActual
  :: GenericValueParameterKey
  -> Mode
  -> GenericStructuralRequirements
  -> Either GenericStructuralError ()
checkGenericStructuralActual key mode requirements = do
  kernelRequirements <- requirementsToKernel key requirements
  case Kernel.decideGenericStructuralActual
      (toKernelMode mode) kernelRequirements of
    Kernel.GenericStructuralActualAccepted -> Right ()
    Kernel.GenericStructuralActualMissingWeakening ->
      Left (MissingStructuralPermission key WeakeningPermission mode)
    Kernel.GenericStructuralActualMissingContraction ->
      Left (MissingStructuralPermission key ContractionPermission mode)

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

deriveGenericApplicationIdentity
  :: DeclarationKey
  -> InterfaceRevision
  -> [(GenericStaticParameterKey, SemanticForm)]
  -> Either GenericApplicationIdentityError GenericApplicationIdentity
deriveGenericApplicationIdentity declarationKey interfaceRevision arguments = do
  argumentMap <- normalizeGenericSemanticArguments arguments
  Right GenericApplicationIdentity
    { genericApplicationDeclarationKey = declarationKey
    , genericApplicationInterfaceRevision = interfaceRevision
    , genericApplicationSemanticArguments = argumentMap
    }

genericApplicationSemanticForm :: GenericApplicationIdentity -> SemanticForm
genericApplicationSemanticForm identity = SemanticRecord (Map.fromList
  [ ("declaration_key", SemanticAtom
      (unDeclarationKey (genericApplicationDeclarationKey identity)))
  , ("interface_revision", SemanticAtom
      (unInterfaceRevision (genericApplicationInterfaceRevision identity)))
  , ("arguments", SemanticRecord (Map.fromList
      [ (unGenericStaticParameterKey key, value)
      | (key, value) <- Map.toAscList
          (genericApplicationSemanticArguments identity)
      ]))
  ])

deriveGenericDischargeLineage
  :: GenericApplicationIdentity
  -> DefinitionRevision
  -> GenericInstantiationRecord
  -> GenericDischargeLineage
deriveGenericDischargeLineage application definitionRevision instantiation =
  GenericDischargeLineage
    { genericDischargeApplicationIdentity = application
    , genericDischargeDefinitionRevision = definitionRevision
    , genericDischargeDispositions = genericInstantiationDispositions instantiation
    }

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

normalizeGenericSemanticArguments
  :: [(GenericStaticParameterKey, SemanticForm)]
  -> Either GenericApplicationIdentityError
      (Map.Map GenericStaticParameterKey SemanticForm)
normalizeGenericSemanticArguments = go Map.empty
  where
    go result [] = Right result
    go result ((key, value) : rest)
      | Map.member key result = Left (DuplicateGenericSemanticArgument key)
      | otherwise = go (Map.insert key value result) rest

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

toKernelUse :: GenericStructuralUse -> Kernel.GenericStructuralUse
toKernelUse use = case use of
  TransferGenericValue _ -> Kernel.TransferGenericValue
  DiscardGenericValue _ -> Kernel.DiscardGenericValue
  DuplicateGenericValue _ -> Kernel.DuplicateGenericValue

toKernelMode :: Mode -> Kernel.Mode
toKernelMode mode = case mode of
  Unrestricted -> Kernel.Unrestricted
  Affine -> Kernel.Affine
  Linear -> Kernel.Linear

toKernelPermission :: StructuralPermission -> Kernel.StructuralPermission
toKernelPermission permission = case permission of
  WeakeningPermission -> Kernel.WeakeningPermission
  ContractionPermission -> Kernel.ContractionPermission

toKernelRequirements
  :: GenericStructuralRequirements
  -> Kernel.GenericStructuralRequirements
toKernelRequirements requirements = Kernel.MkRequirements
  (Set.member WeakeningPermission permissions)
  (Set.member ContractionPermission permissions)
  where
    permissions = genericStructuralPermissions requirements

fromKernelRequirements
  :: Kernel.GenericStructuralRequirements
  -> GenericStructuralRequirements
fromKernelRequirements kernelRequirements =
  case kernelRequirements of
    Kernel.MkRequirements weakening contraction ->
      GenericStructuralRequirements (Set.fromList
        ([WeakeningPermission | weakening]
          ++ [ContractionPermission | contraction]))

sameKernelRequirements
  :: Kernel.GenericStructuralRequirements
  -> Kernel.GenericStructuralRequirements
  -> Bool
sameKernelRequirements left right =
  case (left, right) of
    (Kernel.MkRequirements leftWeakening leftContraction,
     Kernel.MkRequirements rightWeakening rightContraction) ->
      leftWeakening == rightWeakening
        && leftContraction == rightContraction

requirementsToKernel
  :: GenericValueParameterKey
  -> GenericStructuralRequirements
  -> Either GenericStructuralError Kernel.GenericStructuralRequirements
requirementsToKernel key requirements =
  let kernelRequirements = toKernelRequirements requirements
  in if fromKernelRequirements kernelRequirements == requirements
      then Right kernelRequirements
      else Left (GenericStructuralKernelBridgeMismatch key)

requirementsFromKernel
  :: GenericValueParameterKey
  -> Kernel.GenericStructuralRequirements
  -> Either GenericStructuralError GenericStructuralRequirements
requirementsFromKernel key kernelRequirements =
  let requirements = fromKernelRequirements kernelRequirements
      roundTrip = toKernelRequirements requirements
  in if sameKernelRequirements roundTrip kernelRequirements
      then Right requirements
      else Left (GenericStructuralKernelBridgeMismatch key)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
