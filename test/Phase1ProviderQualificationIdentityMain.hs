{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-011 different evidence bundles preserve claim revision" evidenceReplacementPreservesClaim
    , test "PROV-011 different evidence bundles change evidence revision" evidenceReplacementChangesEvidence
    , test "PROV-011 evidence references never enter claim identity" evidenceRefsDoNotAffectClaim
    , test "PROV-011 semantic claim change revises claim identity" semanticClaimChangeRevisesClaim
    , test "PROV-011 evidence ordering is nonsemantic" evidenceOrderingIsCanonical
    , test "PROV-011 evidence content change revises evidence identity" evidenceContentChangesRevision
    , test "PROV-011 policy change preserves claim and evidence identity" policyChangePreservesUpstreamIdentity
    , test "PROV-011 policy change revises admission identity" policyChangeRevisesAdmission
    , test "PROV-011 decision change revises admission identity" decisionChangeRevisesAdmission
    , test "PROV-011 admission ordering is nonsemantic" admissionOrderingIsCanonical
    , test "PROV-011 evidence cannot bind a different claim" mismatchedEvidenceClaimRejected
    , test "PROV-011 admission cannot bind a different evidence bundle" mismatchedAdmissionEvidenceRejected
    , test "PROV-011 admission interface must match semantic claim" mismatchedAdmissionInterfaceRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

evidenceReplacementPreservesClaim :: Either String ()
evidenceReplacementPreservesClaim = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidenceA = evidenceBundleA claimRevision
      evidenceB = evidenceBundleB claimRevision
  checkedA <- mapLeft show $ checkQualificationEvidenceIdentity baseClaim evidenceA
  checkedB <- mapLeft show $ checkQualificationEvidenceIdentity baseClaim evidenceB
  assert
    (checkedQualificationEvidenceClaimRevision checkedA ==
      checkedQualificationEvidenceClaimRevision checkedB)
    "replacing evidence changed semantic claim revision"

evidenceReplacementChangesEvidence :: Either String ()
evidenceReplacementChangesEvidence = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
  checkedA <- mapLeft show $ checkQualificationEvidenceIdentity
    baseClaim (evidenceBundleA claimRevision)
  checkedB <- mapLeft show $ checkQualificationEvidenceIdentity
    baseClaim (evidenceBundleB claimRevision)
  assert
    (checkedQualificationEvidenceRevision checkedA /=
      checkedQualificationEvidenceRevision checkedB)
    "different proof bundles shared an evidence revision"

evidenceRefsDoNotAffectClaim :: Either String ()
evidenceRefsDoNotAffectClaim = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidenceA = evidenceBundleA claimRevision
      evidenceChanged = evidenceA
        { qualificationEvidenceRefs = Set.singleton "artifact:evidence:replacement" }
  _ <- mapLeft show $ checkQualificationEvidenceIdentity baseClaim evidenceA
  _ <- mapLeft show $ checkQualificationEvidenceIdentity baseClaim evidenceChanged
  assert (deriveQualificationClaimRevision baseClaim == claimRevision)
    "evidence refs leaked into claim identity"

semanticClaimChangeRevisesClaim :: Either String ()
semanticClaimChangeRevisesClaim = do
  let changed = baseClaim
        { qualificationClaimConditions = Set.insert "filesystem.atomic-rename"
            (qualificationClaimConditions baseClaim)
        }
  assert
    (deriveQualificationClaimRevision changed /= deriveQualificationClaimRevision baseClaim)
    "semantic condition change failed to revise claim identity"

evidenceOrderingIsCanonical :: Either String ()
evidenceOrderingIsCanonical = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      left = (evidenceBundleA claimRevision)
        { qualificationEvidenceRefs = Set.fromList ["evidence:b", "evidence:a"]
        , qualificationEvidenceObligationDispositions = Map.fromList
            [ ("obligation.b", SemanticAtom "proof:b")
            , ("obligation.a", SemanticAtom "proof:a")
            ]
        }
      right = (evidenceBundleA claimRevision)
        { qualificationEvidenceRefs = Set.fromList ["evidence:a", "evidence:b"]
        , qualificationEvidenceObligationDispositions = Map.fromList
            [ ("obligation.a", SemanticAtom "proof:a")
            , ("obligation.b", SemanticAtom "proof:b")
            ]
        }
  assert
    (deriveQualificationEvidenceRevision left == deriveQualificationEvidenceRevision right)
    "map/set insertion order changed evidence identity"

evidenceContentChangesRevision :: Either String ()
evidenceContentChangesRevision = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      original = evidenceBundleA claimRevision
      changed = original
        { qualificationEvidenceProofRefs = Set.insert "proof:new"
            (qualificationEvidenceProofRefs original)
        }
  assert
    (deriveQualificationEvidenceRevision original /=
      deriveQualificationEvidenceRevision changed)
    "new proof reference did not revise evidence identity"

policyChangePreservesUpstreamIdentity :: Either String ()
policyChangePreservesUpstreamIdentity = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidence = evidenceBundleA claimRevision
      evidenceRevision = deriveQualificationEvidenceRevision evidence
      permissive = admissionInput claimRevision evidenceRevision
        "assurance.policy.permissive.v1" QualificationAdmitted
      strict = admissionInput claimRevision evidenceRevision
        "assurance.policy.strict.v1"
        (QualificationRejected (Set.singleton "assumption-not-permitted"))
  checkedPermissive <- mapLeft show $
    checkQualificationAdmissionIdentity baseClaim evidence permissive
  checkedStrict <- mapLeft show $
    checkQualificationAdmissionIdentity baseClaim evidence strict
  assert
    (checkedQualificationAdmissionClaimRevision checkedPermissive ==
      checkedQualificationAdmissionClaimRevision checkedStrict
      && checkedQualificationAdmissionEvidenceRevision checkedPermissive ==
         checkedQualificationAdmissionEvidenceRevision checkedStrict)
    "policy change mutated claim or evidence identity"

policyChangeRevisesAdmission :: Either String ()
policyChangeRevisesAdmission = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidence = evidenceBundleA claimRevision
      evidenceRevision = deriveQualificationEvidenceRevision evidence
      permissive = admissionInput claimRevision evidenceRevision
        "assurance.policy.permissive.v1" QualificationAdmitted
      strict = admissionInput claimRevision evidenceRevision
        "assurance.policy.strict.v1"
        (QualificationRejected (Set.singleton "assumption-not-permitted"))
  checkedPermissive <- mapLeft show $
    checkQualificationAdmissionIdentity baseClaim evidence permissive
  checkedStrict <- mapLeft show $
    checkQualificationAdmissionIdentity baseClaim evidence strict
  assert
    (checkedQualificationAdmissionRevision checkedPermissive /=
      checkedQualificationAdmissionRevision checkedStrict)
    "policy change failed to revise admission identity"

decisionChangeRevisesAdmission :: Either String ()
decisionChangeRevisesAdmission = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidence = evidenceBundleA claimRevision
      evidenceRevision = deriveQualificationEvidenceRevision evidence
      accepted = admissionInput claimRevision evidenceRevision
        "assurance.policy.same.v1" QualificationAdmitted
      rejected = admissionInput claimRevision evidenceRevision
        "assurance.policy.same.v1"
        (QualificationRejected (Set.singleton "target-condition-failed"))
  assert
    (deriveQualificationAdmissionRevision accepted /=
      deriveQualificationAdmissionRevision rejected)
    "admission decision failed to revise admission identity"

admissionOrderingIsCanonical :: Either String ()
admissionOrderingIsCanonical = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidence = evidenceBundleA claimRevision
      evidenceRevision = deriveQualificationEvidenceRevision evidence
      left = (admissionInput claimRevision evidenceRevision
        "assurance.policy.v1" QualificationAdmitted)
          { qualificationAdmissionDependencyAdmissions = Set.fromList ["dep:b", "dep:a"]
          , qualificationAdmissionConditionDispositions = Map.fromList
              [ ("condition.b", SemanticAtom "accepted")
              , ("condition.a", SemanticAtom "accepted")
              ]
          }
      right = left
          { qualificationAdmissionDependencyAdmissions = Set.fromList ["dep:a", "dep:b"]
          , qualificationAdmissionConditionDispositions = Map.fromList
              [ ("condition.a", SemanticAtom "accepted")
              , ("condition.b", SemanticAtom "accepted")
              ]
          }
  assert
    (deriveQualificationAdmissionRevision left == deriveQualificationAdmissionRevision right)
    "map/set insertion order changed admission identity"

mismatchedEvidenceClaimRejected :: Either String ()
mismatchedEvidenceClaimRejected = do
  let expectedClaim = deriveQualificationClaimRevision baseClaim
      wrongClaim = QualificationClaimRevision "claim:wrong"
      evidence = evidenceBundleA wrongClaim
  case checkQualificationEvidenceIdentity baseClaim evidence of
    Left (QualificationEvidenceClaimRevisionMismatch expected actual) -> do
      assert (expected == expectedClaim) "wrong expected claim revision"
      assert (actual == wrongClaim) "wrong mismatched claim revision"
    other -> Left ("mismatched evidence claim accepted: " <> show other)

mismatchedAdmissionEvidenceRejected :: Either String ()
mismatchedAdmissionEvidenceRejected = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidence = evidenceBundleA claimRevision
      evidenceRevision = deriveQualificationEvidenceRevision evidence
      wrongEvidence = QualificationEvidenceRevision "evidence:wrong"
      admission = (admissionInput claimRevision wrongEvidence
        "assurance.policy.v1" QualificationAdmitted)
  case checkQualificationAdmissionIdentity baseClaim evidence admission of
    Left (QualificationAdmissionEvidenceRevisionMismatch expected actual) -> do
      assert (expected == evidenceRevision) "wrong expected evidence revision"
      assert (actual == wrongEvidence) "wrong mismatched admission evidence"
    other -> Left ("mismatched admission evidence accepted: " <> show other)

mismatchedAdmissionInterfaceRejected :: Either String ()
mismatchedAdmissionInterfaceRejected = do
  let claimRevision = deriveQualificationClaimRevision baseClaim
      evidence = evidenceBundleA claimRevision
      evidenceRevision = deriveQualificationEvidenceRevision evidence
      wrongInterface = InterfaceRevision "provider.other.v1"
      admission = (admissionInput claimRevision evidenceRevision
        "assurance.policy.v1" QualificationAdmitted)
          { qualificationAdmissionRequiredInterface = wrongInterface }
  case checkQualificationAdmissionIdentity baseClaim evidence admission of
    Left (QualificationAdmissionInterfaceMismatch expected actual) -> do
      assert (expected == providerInterface) "wrong expected provider interface"
      assert (actual == wrongInterface) "wrong mismatched provider interface"
    other -> Left ("mismatched admission interface accepted: " <> show other)

baseClaim :: ProviderQualificationClaimIdentityInput
baseClaim = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = providerInterface
  , qualificationClaimSubject = SemanticProviderImplementation providerDefinition
  , qualificationClaimLayer = SemanticImplementationQualification
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operations", SemanticAtom "qualified:PROV-001-005")
      , ("state", SemanticAtom "relation:blob-state-v1")
      , ("laws", SemanticAtom "law:no-replace-v1")
      , ("authority", SemanticAtom "confinement:provider-authority-v1")
      , ("evidence_competence", SemanticAtom "digest-subject:v1")
      ]
  , qualificationClaimConditions = Set.fromList
      [ "filesystem.no-out-of-band-mutation"
      , "runtime.sha256-profile-v1"
      ]
  , qualificationClaimValidityScope = SemanticRecord (Map.fromList
      [ ("provider_contract", SemanticAtom "provider.blob.v1")
      , ("implementation", SemanticAtom "provider.blob.impl.v1")
      ])
  }

evidenceBundleA :: QualificationClaimRevision -> ProviderQualificationEvidenceIdentityInput
evidenceBundleA claimRevision = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision = claimRevision
  , qualificationEvidenceObligationDispositions = Map.fromList
      [ ("operation-refinement", SemanticAtom "discharged:callable-refinement")
      , ("state-simulation", SemanticAtom "discharged:model-check")
      , ("authority-confinement", SemanticAtom "discharged:static")
      ]
  , qualificationEvidenceRefs = Set.singleton "evidence:bundle:a"
  , qualificationEvidenceProofRefs = Set.singleton "proof:provider-law:a"
  , qualificationEvidenceTranslationValidationRefs = Set.empty
  , qualificationEvidenceRuntimeEnforcementRefs = Set.empty
  , qualificationEvidenceAssumptionRefs = Set.singleton "assumption:filesystem-exclusive"
  , qualificationEvidenceValidityDependencies = Set.singleton "profile:linux-fs-v1"
  }

evidenceBundleB :: QualificationClaimRevision -> ProviderQualificationEvidenceIdentityInput
evidenceBundleB claimRevision = (evidenceBundleA claimRevision)
  { qualificationEvidenceRefs = Set.singleton "evidence:bundle:b"
  , qualificationEvidenceProofRefs = Set.singleton "proof:provider-law:b"
  }

admissionInput
  :: QualificationClaimRevision
  -> QualificationEvidenceRevision
  -> String
  -> ProviderQualificationAdmissionDecision
  -> ProviderQualificationAdmissionIdentityInput
admissionInput claimRevision evidenceRevision policy decision =
  ProviderQualificationAdmissionIdentityInput
    { qualificationAdmissionClaimRevision = claimRevision
    , qualificationAdmissionEvidenceRevision = evidenceRevision
    , qualificationAdmissionProviderOccurrence = "architecture.provider.blob.001"
    , qualificationAdmissionRequiredInterface = providerInterface
    , qualificationAdmissionRealizationContextRevision = "realization-context.host.v1"
    , qualificationAdmissionAssurancePolicyRevision = fromString policy
    , qualificationAdmissionConditionDispositions = Map.fromList
        [ ("filesystem.no-out-of-band-mutation", SemanticAtom "accepted")
        , ("runtime.sha256-profile-v1", SemanticAtom "accepted")
        ]
    , qualificationAdmissionDependencyAdmissions = Set.singleton "admission:sha256-provider:v1"
    , qualificationAdmissionSelectedArtifactRuntimeAbi = Just "artifact:blob-host-v1/abi:host-v1"
    , qualificationAdmissionExportedRuntimeObligations = Set.empty
    , qualificationAdmissionExportedDeploymentRequirements = Set.singleton "deploy:exclusive-store-root"
    , qualificationAdmissionDecision = decision
    }

providerInterface :: InterfaceRevision
providerInterface = InterfaceRevision "provider.blob.v1"

providerDefinition :: DefinitionRevision
providerDefinition = DefinitionRevision "provider.blob.impl.v1"

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
