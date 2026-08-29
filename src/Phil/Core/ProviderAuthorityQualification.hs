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

import qualified AuthorityConfinementKernel as AuthorityConfinementKernel
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
  = ProviderAuthorityKernelBridgeMismatch
  | ProviderAuthoritySemanticSubjectRevisionMismatch
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
-- Native Set/Map/revision/evidence facts remain representation foundations. The
-- extracted PHIL-AUTH-CONFINE-001 kernel owns each semantic acceptance decision
-- and the final conjunction; native diagnostics may only explain rejection or
-- fail closed on impossible disagreement.
checkProviderAuthorityQualification
  :: Maybe CheckedProviderSemanticQualification
  -> ProviderAuthorityQualificationSpec
  -> Either ProviderAuthorityQualificationError CheckedProviderAuthorityQualification
checkProviderAuthorityQualification maybeSemantic spec = do
  checkSubject
  checkInventoryBasis
  checkExtraClassification
  checkStaticSummaries
  checkDispositionDomain
  mapM_ checkDisposition dispositionEntries
  case finalDecision of
    True
      | finalFacts -> Right CheckedProviderAuthorityQualification
          { checkedProviderAuthoritySubject = subject
          , checkedProviderAuthorityInventoryBasis = inventoryBasis
          , checkedProviderAuthorityClientVisible = clientVisible
          , checkedProviderAuthorityInternal = internal
          , checkedProviderAuthorityExtra = extra
          , checkedProviderAuthorityStaticReachable = staticReachable
          , checkedProviderAuthorityStaticPublic = staticPublic
          , checkedProviderAuthorityDispositions = dispositions
          }
      | otherwise -> Left ProviderAuthorityKernelBridgeMismatch
    False -> Left ProviderAuthorityKernelBridgeMismatch
  where
    subject = providerAuthoritySubject spec
    inventoryBasis = providerAuthorityInventoryBasis spec
    clientVisible = providerAuthorityClientVisible spec
    internal = providerAuthorityInternal spec
    dispositions = providerAuthorityExtraDispositions spec
    dispositionEntries = Map.toAscList dispositions
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

    subjectKind = case subject of
      SemanticProviderAuthoritySubject _ _ ->
        AuthorityConfinementKernel.SemanticProviderAuthoritySubjectKind
      OpaqueForeignProviderAuthoritySubject _ _ ->
        AuthorityConfinementKernel.OpaqueForeignProviderAuthoritySubjectKind

    (interfaceMatches, definitionMatches) = case (subject, maybeSemantic) of
      (SemanticProviderAuthoritySubject required actual, Just checked) ->
        ( required == checkedProviderContractRevision checked
        , actual == checkedProviderImplementationRevision checked
        )
      _ -> (False, False)

    subjectAccepted = AuthorityConfinementKernel.decideProviderAuthoritySubject
      subjectKind interfaceMatches definitionMatches

    checkSubject = case (subject, maybeSemantic, subjectAccepted) of
      (SemanticProviderAuthoritySubject _ _, Just _, True)
        | interfaceMatches && definitionMatches -> Right ()
        | otherwise -> Left ProviderAuthorityKernelBridgeMismatch
      (SemanticProviderAuthoritySubject _ _, Just checked, False)
        | not interfaceMatches || not definitionMatches ->
            Left (ProviderAuthoritySemanticSubjectRevisionMismatch
              subject
              (checkedProviderContractRevision checked)
              (checkedProviderImplementationRevision checked))
        | otherwise -> Left ProviderAuthorityKernelBridgeMismatch
      (SemanticProviderAuthoritySubject required actual, Nothing, False) ->
        Left (ProviderAuthoritySemanticSubjectRevisionMismatch subject required actual)
      (SemanticProviderAuthoritySubject _ _, Nothing, True) ->
        Left ProviderAuthorityKernelBridgeMismatch
      (OpaqueForeignProviderAuthoritySubject _ _, _, True) -> Right ()
      (OpaqueForeignProviderAuthoritySubject _ _, _, False) ->
        Left ProviderAuthorityKernelBridgeMismatch

    basisKind = case inventoryBasis of
      CheckedPurePhilAuthorityInventory _ ->
        AuthorityConfinementKernel.CheckedPurePhilAuthorityInventoryKind
      ForeignAuthorityInventoryByEvidence _ ->
        AuthorityConfinementKernel.ForeignAuthorityInventoryByEvidenceKind
      ForeignAuthorityInventoryAssumption _ ->
        AuthorityConfinementKernel.ForeignAuthorityInventoryAssumptionKind
      ForeignAuthorityInventoryTcbBoundary _ ->
        AuthorityConfinementKernel.ForeignAuthorityInventoryTcbBoundaryKind
      ForeignAuthorityInventoryFromAbiShape _ ->
        AuthorityConfinementKernel.ForeignAuthorityInventoryFromAbiShapeKind

    inventoryBasisAccepted =
      AuthorityConfinementKernel.decideProviderAuthorityInventoryBasis
        subjectKind basisKind

    checkInventoryBasis = case inventoryBasisAccepted of
      True
        | nativeInventoryBasisAccepted -> Right ()
        | otherwise -> Left ProviderAuthorityKernelBridgeMismatch
      False -> case subject of
        SemanticProviderAuthoritySubject _ _ -> case inventoryBasis of
          CheckedPurePhilAuthorityInventory _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          _ -> Left (ProviderAuthorityPurePhilInventoryRequired inventoryBasis)
        OpaqueForeignProviderAuthoritySubject _ _ -> case inventoryBasis of
          ForeignAuthorityInventoryByEvidence _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          ForeignAuthorityInventoryAssumption _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          ForeignAuthorityInventoryTcbBoundary _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          ForeignAuthorityInventoryFromAbiShape abi ->
            Left (ProviderAuthorityAbiInventoryIsNotEvidence abi)
          _ -> Left (ProviderAuthorityForeignInventoryRequiresEvidenceOrBoundary inventoryBasis)

    nativeInventoryBasisAccepted = case subject of
      SemanticProviderAuthoritySubject _ _ -> case inventoryBasis of
        CheckedPurePhilAuthorityInventory _ -> True
        _ -> False
      OpaqueForeignProviderAuthoritySubject _ _ -> case inventoryBasis of
        ForeignAuthorityInventoryByEvidence _ -> True
        ForeignAuthorityInventoryAssumption _ -> True
        ForeignAuthorityInventoryTcbBoundary _ -> True
        _ -> False

    kernelExtra = Set.filter kernelClassifiesExtra (Set.union internal clientVisible)
    kernelClassifiesExtra authority =
      AuthorityConfinementKernel.decideProviderExtraAuthority
        (Set.member authority internal)
        (Set.member authority clientVisible)

    checkExtraClassification
      | kernelExtra == extra = Right ()
      | otherwise = Left ProviderAuthorityKernelBridgeMismatch

    underreported = Set.difference staticReachable internal
    publicEscape = Set.difference staticPublic clientVisible
    exercisedEscape = Set.difference staticExercised clientVisible
    staticReachableSubsetInternal = Set.null underreported
    staticPublicSubsetClientVisible = Set.null publicEscape
    staticExercisedSubsetClientVisible = Set.null exercisedEscape
    staticFacts = and
      [ staticReachableSubsetInternal
      , staticPublicSubsetClientVisible
      , staticExercisedSubsetClientVisible
      ]
    staticSummariesAccepted = AuthorityConfinementKernel.decideProviderStaticSummaries
      staticReachableSubsetInternal
      staticPublicSubsetClientVisible
      staticExercisedSubsetClientVisible

    checkStaticSummaries = case staticSummariesAccepted of
      True
        | staticFacts -> Right ()
        | otherwise -> Left ProviderAuthorityKernelBridgeMismatch
      False
        | not staticReachableSubsetInternal ->
            Left (ProviderAuthorityStaticReachabilityUnderreported underreported)
        | not staticPublicSubsetClientVisible ->
            Left (ProviderAuthorityStaticPublicEscape publicEscape)
        | not staticExercisedSubsetClientVisible ->
            Left (ProviderAuthorityStaticExerciseOutsidePublic exercisedEscape)
        | otherwise -> Left ProviderAuthorityKernelBridgeMismatch

    dispositionKeys = Map.keysSet dispositions
    missingDispositions = Set.difference extra dispositionKeys
    unexpectedDispositions = Set.difference dispositionKeys extra
    dispositionDomainExactAccepted =
      Set.null missingDispositions && Set.null unexpectedDispositions

    checkDispositionDomain
      | not (Set.null missingDispositions) =
          Left (ProviderAuthorityMissingExtraDispositions missingDispositions)
      | not (Set.null unexpectedDispositions) =
          Left (ProviderAuthorityUnexpectedExtraDispositions unexpectedDispositions)
      | otherwise = Right ()

    dispositionKind disposition = case disposition of
      ExtraAuthorityStaticallyConfined ->
        AuthorityConfinementKernel.ExtraAuthorityStaticallyConfinedKind
      ExtraAuthorityExternallyConfined _ ->
        AuthorityConfinementKernel.ExtraAuthorityExternallyConfinedKind
      ExtraAuthorityAssumptionDependent _ ->
        AuthorityConfinementKernel.ExtraAuthorityAssumptionDependentKind
      ExtraAuthorityTcbBoundary _ ->
        AuthorityConfinementKernel.ExtraAuthorityTcbBoundaryKind
      ExtraAuthorityAssertedAbsentFromAbi _ ->
        AuthorityConfinementKernel.ExtraAuthorityAssertedAbsentFromAbiKind

    dispositionAccepted authority disposition =
      AuthorityConfinementKernel.decideProviderExtraDisposition
        subjectKind
        (dispositionKind disposition)
        (Set.member authority staticReachable)
        (Set.member authority staticPublic)
        (Set.member authority staticExercised)

    checkDisposition (authority, disposition) =
      case dispositionAccepted authority disposition of
        True
          | nativeDispositionAccepted authority disposition -> Right ()
          | otherwise -> Left ProviderAuthorityKernelBridgeMismatch
        False -> case disposition of
          ExtraAuthorityStaticallyConfined -> case subject of
            OpaqueForeignProviderAuthoritySubject _ _ ->
              Left (ProviderAuthorityStaticConfinementInvalidForOpaque authority)
            SemanticProviderAuthoritySubject _ _
              | nativeDispositionAccepted authority disposition ->
                  Left ProviderAuthorityKernelBridgeMismatch
              | otherwise -> Left (ProviderAuthorityStaticConfinementUnavailable authority)
          ExtraAuthorityExternallyConfined _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          ExtraAuthorityAssumptionDependent _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          ExtraAuthorityTcbBoundary _ ->
            Left ProviderAuthorityKernelBridgeMismatch
          ExtraAuthorityAssertedAbsentFromAbi abi ->
            Left (ProviderAuthorityAbiAbsenceIsNotConfinement authority abi)

    nativeDispositionAccepted authority disposition = case disposition of
      ExtraAuthorityStaticallyConfined -> case subject of
        OpaqueForeignProviderAuthoritySubject _ _ -> False
        SemanticProviderAuthoritySubject _ _ ->
          Set.member authority staticReachable
            && not (Set.member authority staticPublic)
            && not (Set.member authority staticExercised)
      ExtraAuthorityExternallyConfined _ -> True
      ExtraAuthorityAssumptionDependent _ -> True
      ExtraAuthorityTcbBoundary _ -> True
      ExtraAuthorityAssertedAbsentFromAbi _ -> False

    dispositionValuesAllowedAccepted = all
      (uncurry dispositionAccepted)
      dispositionEntries

    finalFacts = and
      [ subjectAccepted
      , inventoryBasisAccepted
      , staticSummariesAccepted
      , dispositionDomainExactAccepted
      , dispositionValuesAllowedAccepted
      ]

    finalDecision = AuthorityConfinementKernel.decideProviderAuthorityQualificationFacts
      subjectAccepted
      inventoryBasisAccepted
      staticSummariesAccepted
      dispositionDomainExactAccepted
      dispositionValuesAllowedAccepted
