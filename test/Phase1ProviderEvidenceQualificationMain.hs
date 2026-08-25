{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.CallableScope (LoanScopeKey (..))
import Phil.Core.ProviderEvidenceQualification
import Phil.Core.ProviderQualification
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import Phil.Core.Syntax (Proposition (..), RefSort (..), RefTerm (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-010 scoped borrow maps to stable proof subject" scopedBorrowAccepted
    , test "PROV-010 temporary borrow token cannot substitute for owner subject" borrowTokenSubjectRejected
    , test "PROV-010 checked mapping must target exact stable subject" wrongMappingTargetRejected
    , test "PROV-010 direct mapping is illegal for scoped borrow" directBorrowMappingRejected
    , test "PROV-010 runtime coincidence is not subject competence" runtimeCoincidenceRejected
    , test "PROV-010 exact proposition family is required" wrongFamilyRejected
    , test "PROV-010 evidence operation must already be provider-qualified" unqualifiedOperationRejected
    , test "PROV-010 exact validity contract is preserved" wrongValidityRejected
    , test "PROV-010 stable subject may be observed directly" stableObservationAccepted
    , test "PROV-010 distinct borrows of same owner yield same proposition identity" borrowIdentityIsNonsemantic
    , test "PROV-010 checked result retains exact provider lineage" providerLineageRetained
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

scopedBorrowAccepted :: Either String ()
scopedBorrowAccepted = do
  qualified <- qualifiedDigestProvider
  checked <- mapLeft show $ checkProviderEvidenceProducerCompetence
    qualified digestRequirement (borrowClaim borrowObservationA ownerSubject)
  assert (checkedProviderEvidenceSubject checked == ownerSubject)
    "checked competence lost stable owner subject"
  assert (checkedProviderEvidenceProposition checked == expectedDigestProposition)
    "checked competence materialized wrong proposition"

borrowTokenSubjectRejected :: Either String ()
borrowTokenSubjectRejected = do
  qualified <- qualifiedDigestProvider
  let loanAsSubject = ProviderEvidenceSubjectKey "loan.digest.a"
      claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimPropositionSubject = loanAsSubject
        , providerEvidenceClaimSubjectMapping = CheckedObservationToStableSubject
            mappingRevision borrowObservationA loanAsSubject
        }
  case checkProviderEvidenceProducerCompetence qualified digestRequirement claim of
    Left (ProviderEvidenceStableSubjectMismatch expected actual) -> do
      assert (expected == ownerSubject) "wrong expected stable subject"
      assert (actual == loanAsSubject) "wrong rejected loan subject"
    other -> Left ("borrow token was accepted as proof subject: " <> show other)

wrongMappingTargetRejected :: Either String ()
wrongMappingTargetRejected = do
  qualified <- qualifiedDigestProvider
  let otherOwner = ProviderEvidenceSubjectKey "bytes.object.other"
      claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimSubjectMapping = CheckedObservationToStableSubject
            mappingRevision borrowObservationA otherOwner
        }
  case checkProviderEvidenceProducerCompetence qualified digestRequirement claim of
    Left (ProviderEvidenceMappingSubjectMismatch expected actual) -> do
      assert (expected == ownerSubject) "wrong expected mapping target"
      assert (actual == otherOwner) "wrong actual mapping target"
    other -> Left ("wrong observation mapping target was accepted: " <> show other)

directBorrowMappingRejected :: Either String ()
directBorrowMappingRejected = do
  qualified <- qualifiedDigestProvider
  let claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimSubjectMapping = DirectStableEvidenceSubject ownerSubject }
  case checkProviderEvidenceProducerCompetence qualified digestRequirement claim of
    Left (ProviderEvidenceDirectMappingRequiresStableObservation observation subject) -> do
      assert (observation == borrowObservationA) "wrong observation in direct-mapping failure"
      assert (subject == ownerSubject) "wrong subject in direct-mapping failure"
    other -> Left ("scoped borrow was treated as direct stable subject: " <> show other)

runtimeCoincidenceRejected :: Either String ()
runtimeCoincidenceRejected = do
  qualified <- qualifiedDigestProvider
  let claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimSubjectMapping =
            RuntimeCoincidenceSubjectMapping "same pointer / same bytes" }
  case checkProviderEvidenceProducerCompetence qualified digestRequirement claim of
    Left (ProviderEvidenceRuntimeCoincidenceInsufficient _) -> Right ()
    other -> Left ("runtime coincidence was accepted as subject mapping: " <> show other)

wrongFamilyRejected :: Either String ()
wrongFamilyRejected = do
  qualified <- qualifiedDigestProvider
  let wrongFamily = ProviderPropositionFamilyKey "OtherDigestClaim"
      claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimFamily = wrongFamily }
  case checkProviderEvidenceProducerCompetence qualified digestRequirement claim of
    Left (ProviderEvidenceFamilyMismatch expected actual) -> do
      assert (expected == digestFamily) "wrong required proposition family"
      assert (actual == wrongFamily) "wrong rejected proposition family"
    other -> Left ("wrong proposition family was accepted: " <> show other)

unqualifiedOperationRejected :: Either String ()
unqualifiedOperationRejected = do
  qualified <- qualifiedDigestProvider
  let unknownOperation = ProviderOperationKey "provider.op.sign"
      requirement = digestRequirement { providerEvidenceRequiredOperation = unknownOperation }
      claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimOperation = unknownOperation }
  case checkProviderEvidenceProducerCompetence qualified requirement claim of
    Left (ProviderEvidenceOperationNotQualified operation) ->
      assert (operation == unknownOperation) "wrong unqualified operation diagnostic"
    other -> Left ("unqualified evidence-producing operation was accepted: " <> show other)

wrongValidityRejected :: Either String ()
wrongValidityRejected = do
  qualified <- qualifiedDigestProvider
  let wrongValidity = EvidenceValidityContractKey "validity.loan-only.v1"
      claim = (borrowClaim borrowObservationA ownerSubject)
        { providerEvidenceClaimValidity = wrongValidity }
  case checkProviderEvidenceProducerCompetence qualified digestRequirement claim of
    Left (ProviderEvidenceValidityMismatch expected actual) -> do
      assert (expected == persistentValidity) "wrong required validity contract"
      assert (actual == wrongValidity) "wrong rejected validity contract"
    other -> Left ("wrong evidence validity contract was accepted: " <> show other)

stableObservationAccepted :: Either String ()
stableObservationAccepted = do
  qualified <- qualifiedDigestProvider
  let claim = ProviderEvidenceProducerCompetenceClaim
        { providerEvidenceClaimOperation = digestOperation
        , providerEvidenceClaimFamily = digestFamily
        , providerEvidenceClaimObservation = StableEvidenceObservation ownerSubject
        , providerEvidenceClaimPropositionSubject = ownerSubject
        , providerEvidenceClaimSubjectMapping = DirectStableEvidenceSubject ownerSubject
        , providerEvidenceClaimValidity = persistentValidity
        }
  checked <- mapLeft show $ checkProviderEvidenceProducerCompetence
    qualified digestRequirement claim
  assert (checkedProviderEvidenceProposition checked == expectedDigestProposition)
    "stable observation produced wrong proposition"

borrowIdentityIsNonsemantic :: Either String ()
borrowIdentityIsNonsemantic = do
  qualified <- qualifiedDigestProvider
  checkedA <- mapLeft show $ checkProviderEvidenceProducerCompetence
    qualified digestRequirement (borrowClaim borrowObservationA ownerSubject)
  checkedB <- mapLeft show $ checkProviderEvidenceProducerCompetence
    qualified digestRequirement (borrowClaim borrowObservationB ownerSubject)
  assert
    (checkedProviderEvidenceObservation checkedA /= checkedProviderEvidenceObservation checkedB)
    "fixture borrows unexpectedly share observation identity"
  assert
    (checkedProviderEvidenceProposition checkedA == checkedProviderEvidenceProposition checkedB)
    "temporary borrow identity leaked into persistent proposition identity"

providerLineageRetained :: Either String ()
providerLineageRetained = do
  qualified <- qualifiedDigestProvider
  checked <- mapLeft show $ checkProviderEvidenceProducerCompetence
    qualified digestRequirement (borrowClaim borrowObservationA ownerSubject)
  assert
    (checkedProviderEvidenceContractRevision checked == digestProviderInterface)
    "provider contract revision not retained"
  assert
    (checkedProviderEvidenceImplementationRevision checked == digestProviderDefinition)
    "provider implementation revision not retained"

qualifiedDigestProvider :: Either String CheckedProviderSemanticQualification
qualifiedDigestProvider = mapLeft show $
  checkProviderSemanticQualification digestProviderContract digestProviderImplementation digestProviderClaim

digestProviderContract :: ProviderContract
digestProviderContract = ProviderContract
  { providerContractInterfaceRevision = digestProviderInterface
  , providerContractOperations = Map.singleton digestOperation ProviderOperationContract
      { providerOperationCallableContract = callableSurface digestCallableInterface
      , providerOperationPreconditions = Set.empty
      , providerOperationOutcomeResidues = Map.singleton digestSuccess emptyResidue
      }
  }

digestProviderImplementation :: ProviderImplementation
digestProviderImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision = digestProviderDefinition
  , providerImplementationEntries = Map.singleton digestEntry ProviderImplementationOperation
      { providerImplementationCallable = callableSurface digestImplCallableInterface
      , providerImplementationPreconditions = Set.empty
      , providerImplementationOutcomeResidues = Map.singleton implDigestSuccess emptyResidue
      }
  , providerImplementationSymbols = Set.singleton "sha256_digest"
  }

digestProviderClaim :: ProviderQualificationClaim
digestProviderClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface = digestProviderInterface
  , providerQualificationImplementationRevision = digestProviderDefinition
  , providerQualificationOperationCorrespondences = Map.singleton digestOperation
      ProviderOperationCorrespondence
        { providerCorrespondenceImplementationEntry = digestEntry
        , providerCorrespondenceOutcomes = Map.singleton implDigestSuccess digestSuccess
        }
  }

callableSurface :: InterfaceRevision -> CallableRefinementSurface
callableSurface revision = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "bytes->digest"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = revision
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.empty
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

borrowClaim
  :: ProviderEvidenceObservation
  -> ProviderEvidenceSubjectKey
  -> ProviderEvidenceProducerCompetenceClaim
borrowClaim observation subject = ProviderEvidenceProducerCompetenceClaim
  { providerEvidenceClaimOperation = digestOperation
  , providerEvidenceClaimFamily = digestFamily
  , providerEvidenceClaimObservation = observation
  , providerEvidenceClaimPropositionSubject = subject
  , providerEvidenceClaimSubjectMapping = CheckedObservationToStableSubject
      mappingRevision observation subject
  , providerEvidenceClaimValidity = persistentValidity
  }

digestRequirement :: ProviderEvidenceProducerRequirement
digestRequirement = ProviderEvidenceProducerRequirement
  { providerEvidenceRequiredOperation = digestOperation
  , providerEvidenceRequiredFamily = digestFamily
  , providerEvidenceRequiredStableSubject = ownerSubject
  , providerEvidenceRequiredValidity = persistentValidity
  }

expectedDigestProposition :: Proposition
expectedDigestProposition = Atom "DigestMatches"
  [RefOpaque (SortStableId "provider-evidence-subject") "bytes.object.001"]

digestFamily :: ProviderPropositionFamilyKey
digestFamily = ProviderPropositionFamilyKey "DigestMatches"

ownerSubject :: ProviderEvidenceSubjectKey
ownerSubject = ProviderEvidenceSubjectKey "bytes.object.001"

borrowObservationA, borrowObservationB :: ProviderEvidenceObservation
borrowObservationA = ScopedBorrowEvidenceObservation
  (ProviderObservationKey "borrow.digest.a") (LoanScopeKey "loan.scope.a")
borrowObservationB = ScopedBorrowEvidenceObservation
  (ProviderObservationKey "borrow.digest.b") (LoanScopeKey "loan.scope.b")

mappingRevision :: EvidenceSubjectMappingRevision
mappingRevision = EvidenceSubjectMappingRevision "subject-map.borrow-to-owner.v1"

persistentValidity :: EvidenceValidityContractKey
persistentValidity = EvidenceValidityContractKey "validity.stable-owner.v1"

digestProviderInterface, digestCallableInterface, digestImplCallableInterface :: InterfaceRevision
digestProviderInterface = InterfaceRevision "provider.digest.v1"
digestCallableInterface = InterfaceRevision "call.digest.contract.v1"
digestImplCallableInterface = InterfaceRevision "call.digest.impl.v1"

digestProviderDefinition :: DefinitionRevision
digestProviderDefinition = DefinitionRevision "provider.digest.impl.v1"

digestOperation :: ProviderOperationKey
digestOperation = ProviderOperationKey "provider.op.digest"

digestEntry :: ProviderImplementationEntryKey
digestEntry = ProviderImplementationEntryKey "impl.entry.digest"

digestSuccess, implDigestSuccess :: ProviderOutcomeKey
digestSuccess = ProviderOutcomeKey "contract.digest-success"
implDigestSuccess = ProviderOutcomeKey "impl.digest-success"

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue Set.empty Set.empty Set.empty Set.empty Set.empty

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
