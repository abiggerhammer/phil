{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericStaticParameterKey (..)
  , GenericDischargeLineage (..)
  , checkGenericInstantiation
  , deriveGenericApplicationIdentity
  , deriveGenericDischargeLineage
  , strictGenericInstantiationPolicy
  )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity (..)
  , DeclarationIdentity (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , RealizationRevision (..)
  , SemanticForm (..)
  , deriveArchitectureInstanceIdentity
  , DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  )
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  , certifiedApplicationSourceAssurance
  , certifiedApplicationStageClosure
  , certifyApplicationArtifact
  )
import Phil.Verification.FinalAuthorityAdapter
import Phil.Verification.SourceManifestBinding
import Phil.Verification.NativeFinalInstanceCorrespondence
import Phil.Verification.Bundle
  ( VerificationBundle (..)
  , buildVerificationBundle
  , verificationBundleArchitectureDigest
  )
import Phil.Verification.ManifestClosure
  ( ManifestClosureSelection (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , buildVerificationRevisionGraph
  )
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance
  , composeGenericApplicationAssurance
  , genericApplicationAssuranceLineage
  , prepareReusableGenericBodyAssurance
  )
import Phil.Assurance.Types
  ( ArtifactIdentity (..)
  , ArtifactRef (..)
  , AssuranceLedger
  , AssuranceManifest (..)
  , Digest (..)
  , VerificationContext (..)
  , deriveManifestId
  , digestText
  , emptyLedger
  , emptyManifest
  , emptyVerificationContext
  )
import Phil.Examples.Phase1.StageClosureWitnesses
  ( steveStageClosureBundle
  , uploadStageClosureBundle
  )
import Phil.LLVM.IR
  ( LLVMArtifact (..)
  , LLVMEmissionContract (..)
  , LLVMTargetProfile (..)
  )
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.Systems.IR
  ( SystemsArtifact
  , loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , SystemsArtifactRevision (..)
  , Phase1StageContractRevision (..)
  )
import Phil.Systems.StageClosure
  ( ClosedStageContractRevision (..)
  , StageClosureBundle (..)
  , StageClosureVerificationError (..)
  , concreteSubjectStage
  , deriveClosedStageContractRevision
  , verifyStageClosureBundle
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  , SubjectStageRevision (..)
  )
import Phil.Verification.CertifiedRelease
import System.Exit (exitFailure)

main :: IO ()
main = do
  uploadStage <- requireStage "Upload" uploadStageClosureBundle
  steveStage <- requireStage "Steve" steveStageClosureBundle
  source <- case nativeAdapterSourceAssurance of
    Left detail -> putStrLn ("FAIL: final-native-adapter source fixture: " <> detail) >> exitFailure
    Right value -> pure value
  let upload = releaseFixture "upload" uploadStage
      steve = releaseFixture "steve" steveStage
      checks =
        [ ( "INT-005 Upload exact certified-release envelope closes"
          , releaseCloses upload)
        , ( "INT-005 Steve exact certified-release envelope closes"
          , releaseCloses steve)
        , ( "INT-005 emitted LLVM cannot be rebound to another Systems artifact"
          , wrongLLVMSourceRejected upload)
        , ( "INT-005 changed lowering lineage cannot hide behind a self-consistent manifest"
          , wrongLoweringRootRejected upload)
        , ( "INT-005 canonical emitted LLVM text is release identity"
          , noncanonicalLLVMTextRejected upload)
        , ( "INT-005 selected LLVM target profile is exact"
          , wrongLLVMProfileRejected upload)
        , ( "INT-005 residual TCB kind omission rejects"
          , missingTrustKindRejected upload)
        , ( "INT-005 duplicate residual TCB identity rejects"
          , duplicateTrustIdentityRejected upload)
        , ( "INT-005 residual TCB entries must name their trusted basis"
          , blankTrustBasisRejected upload)
        , ( "Native final-authority adapter binds Upload source, manifest and exact stage"
          , nativeAdapterAccepts source upload)
        , ( "Native final-authority adapter binds Steve source, manifest and exact stage"
          , nativeAdapterAccepts source steve)
        , ( "Native adapter rejects a swapped certified release stage"
          , nativeAdapterSwappedStageRejects source upload steve)
        , ( "Native adapter rejects a wrong independent source identity"
          , nativeAdapterWrongSourceRejects source upload)
        , ( "Native adapter rejects a wrong independent manifest identity"
          , nativeAdapterWrongManifestRejects source upload steve)
        , ( "Source-manifest producer closes Upload from checked declaration and bundle"
          , producedBindingAccepted source upload)
        , ( "Source-manifest producer closes Steve from checked declaration and bundle"
          , producedBindingAccepted source steve)
        , ( "Checked Upload source-manifest token retains exact semantic descriptor"
          , checkedDescriptorRetained source upload)
        , ( "Checked Steve source-manifest token retains exact semantic descriptor"
          , checkedDescriptorRetained source steve)
        , ( "Upload final witness retains exact checked-instance source-manifest token"
          , finalWitnessRetainsCheckedSourceManifestBinding source upload)
        , ( "Steve final witness retains exact checked-instance source-manifest token"
          , finalWitnessRetainsCheckedSourceManifestBinding source steve)
        , ( "Upload accepted manifest-stage replay preserves distinct digest and revision domains"
          , nativeManifestStageReplayAccepts source upload)
        , ( "Steve accepted manifest-stage replay preserves distinct digest and revision domains"
          , nativeManifestStageReplayAccepts source steve)
        , ( "Upload real accepted digest roles survive exact reversible tagged wire"
          , nativeDigestRoleWireReplayAccepts source upload)
        , ( "Steve real accepted digest roles survive exact reversible tagged wire"
          , nativeDigestRoleWireReplayAccepts source steve)
        , ( "Upload accepted normalized/common/closed stage revisions roundtrip through disjoint role wires"
          , nativeRevisionRoleWireReplayAccepts source upload)
        , ( "Steve accepted normalized/common/closed stage revisions roundtrip through disjoint role wires"
          , nativeRevisionRoleWireReplayAccepts source steve)
        , ( "Upload equal-payload revision and digest role substitutions fail closed"
          , nativeRevisionRoleEqualPayloadSubstitutionsReject source upload)
        , ( "Steve equal-payload revision and digest role substitutions fail closed"
          , nativeRevisionRoleEqualPayloadSubstitutionsReject source steve)
        , ( "Upload accepted subject/instance/realization revision roles roundtrip through disjoint wires"
          , nativeStageIdentityRoleReplayAccepts source upload)
        , ( "Steve accepted subject/instance/realization revision roles roundtrip through disjoint wires"
          , nativeStageIdentityRoleReplayAccepts source steve)
        , ( "Upload equal-payload subject/instance/realization substitutions reject by role"
          , nativeStageIdentityEqualPayloadRejects source upload)
        , ( "Steve equal-payload subject/instance/realization substitutions reject by role"
          , nativeStageIdentityEqualPayloadRejects source steve)
        , ( "Upload accepted verifier-profile Text replays through isolated P-role wire"
          , nativeVerifierProfileWireReplayAccepts source upload)
        , ( "Steve accepted verifier-profile Text replays through isolated P-role wire"
          , nativeVerifierProfileWireReplayAccepts source steve)
        , ( "Upload same-payload forged profile versus eight other roles decodes fail closed"
          , nativeVerifierProfileSamePayloadRejects source upload)
        , ( "Steve same-payload forged profile versus eight other roles decodes fail closed"
          , nativeVerifierProfileSamePayloadRejects source steve)
        , ( "Upload checked occurrence InstanceKey uses a disjoint K-role wire"
          , nativeOccurrenceKeyWireReplayAccepts source upload)
        , ( "Steve checked occurrence InstanceKey uses a disjoint K-role wire"
          , nativeOccurrenceKeyWireReplayAccepts source steve)
        , ( "Upload checked occurrence (InstanceKey, InstanceRevision) pair roundtrips without stage-origin authority"
          , nativeCheckedOccurrenceIdentityPairReplayAccepts source upload)
        , ( "Steve checked occurrence (InstanceKey, InstanceRevision) pair roundtrips without stage-origin authority"
          , nativeCheckedOccurrenceIdentityPairReplayAccepts source steve)
        , ( "Upload accepted generic declaration/interface D/V scalars replay; forged actuals cannot identify application"
          , nativeGenericApplicationScalarReplayAccepts source upload)
        , ( "Steve accepted generic declaration/interface D/V scalars replay; forged actuals cannot identify application"
          , nativeGenericApplicationScalarReplayAccepts source steve)
        , ( "Upload checked semantic-actuals Q-key domain replays; value changes and duplicate keys never become authority"
          , nativeGenericActualsKeyDomainReplayAccepts source upload)
        , ( "Steve checked semantic-actuals Q-key domain replays; value changes and duplicate keys never become authority"
          , nativeGenericActualsKeyDomainReplayAccepts source steve)
        , ( "Upload checked generic SemanticAtom M-only value wire; structured forms and foreign roles fail closed"
          , nativeGenericSemanticAtomReplayAccepts source upload)
        , ( "Steve checked generic SemanticAtom M-only value wire; structured forms and foreign roles fail closed"
          , nativeGenericSemanticAtomReplayAccepts source steve)
        , ( "Upload checked SemanticOrdered atom-only vector preserves order; nesting and foreign roles fail closed"
          , nativeGenericOrderedAtomVectorReplayAccepts source upload)
        , ( "Steve checked SemanticOrdered atom-only vector preserves order; nesting and foreign roles fail closed"
          , nativeGenericOrderedAtomVectorReplayAccepts source steve)
        , ( "Upload checked Q/M atom-only generic actuals preserve association; duplicates and swapped roles reject"
          , nativeGenericAtomActualPairsReplayAccepts source upload)
        , ( "Steve checked Q/M atom-only generic actuals preserve association; duplicates and swapped roles reject"
          , nativeGenericAtomActualPairsReplayAccepts source steve)
        , ( "Upload changed raw Systems digest cannot pass exact manifest-stage replay"
          , nativeManifestStageReplayRejectsChangedDigests source upload)
        , ( "Steve changed raw Systems digest cannot pass exact manifest-stage replay"
          , nativeManifestStageReplayRejectsChangedDigests source steve)
        , ( "Upload exact accepted full-object replay retains checked producer and both envelopes"
          , exactAcceptedConsumerReplayAccepts source upload)
        , ( "Steve exact accepted full-object replay retains checked producer and both envelopes"
          , exactAcceptedConsumerReplayAccepts source steve)
        , ( "Upload declaration-only same-manifest producer cannot replace exact replay token"
          , exactAcceptedConsumerReplayRejectsWeakProducer source upload)
        , ( "Steve declaration-only same-manifest producer cannot replace exact replay token"
          , exactAcceptedConsumerReplayRejectsWeakProducer source steve)
        , ( "Upload independently accepted alternative source envelope cannot replace replay consumer"
          , exactAcceptedConsumerReplayRejectsOtherSource source upload steve)
        , ( "Steve independently accepted alternative source envelope cannot replace replay consumer"
          , exactAcceptedConsumerReplayRejectsOtherSource source steve upload)
        , ( "Upload independently accepted same-coordinate different-trust release rejects"
          , exactAcceptedConsumerReplayRejectsOtherReleaseTrust source upload)
        , ( "Steve independently accepted same-coordinate different-trust release rejects"
          , exactAcceptedConsumerReplayRejectsOtherReleaseTrust source steve)
        , ( "Upload declaration-only token cannot replace final checked producer token"
          , declarationOnlyTokenCannotReplaceFinalProducer source upload)
        , ( "Steve declaration-only token cannot replace final checked producer token"
          , declarationOnlyTokenCannotReplaceFinalProducer source steve)
        , ( "Declaration-only Upload producer cannot bind a certified release"
          , declarationOnlyBindingRejected source upload)
        , ( "Declaration-only Steve producer cannot bind a certified release"
          , declarationOnlyBindingRejected source steve)
        , ( "Low-level manifest binder rejects same-identity distinct source proof for Upload"
          , producedBindingDifferentAcceptedSourceRejects source upload)
        , ( "Low-level manifest binder rejects same-identity distinct source proof for Steve"
          , producedBindingDifferentAcceptedSourceRejects source steve)
        , ( "Generic actuals match canonical Upload architecture-instance binding"
          , producedBindingAccepted source upload)
        , ( "Typed native final instance witness closes Upload accepted consumer"
          , nativeFinalInstanceAccepts source upload)
        , ( "Typed native final instance witness closes Steve accepted consumer"
          , nativeFinalInstanceAccepts source steve)
        , ( "Upload final witness exports complete checked producer descriptor"
          , finalWitnessRetainsProducerDescriptor source upload)
        , ( "Steve final witness exports complete checked producer descriptor"
          , finalWitnessRetainsProducerDescriptor source steve)
        , ( "Upload final witness retains full source producer assurance"
          , finalWitnessRetainsProducedSource source upload)
        , ( "Steve final witness retains full source producer assurance"
          , finalWitnessRetainsProducedSource source steve)
        , ( "Upload final witness retains exact checked and accepted full manifest"
          , finalWitnessRetainsProducedManifest source upload)
        , ( "Steve final witness retains exact checked and accepted full manifest"
          , finalWitnessRetainsProducedManifest source steve)
        , ( "Upload final witness retains exact accepted full StageClosure"
          , finalWitnessRetainsAcceptedStage source upload)
        , ( "Steve final witness retains exact accepted full StageClosure"
          , finalWitnessRetainsAcceptedStage source steve)
        , ( "Upload final witness retains complete independently accepted source envelope"
          , finalWitnessRetainsAcceptedSource source upload)
        , ( "Steve final witness retains complete independently accepted source envelope"
          , finalWitnessRetainsAcceptedSource source steve)
        , ( "Upload accepted same-source alternative StageClosure cannot replace source envelope"
          , sameSourceDifferentStageCannotReplaceSourceEnvelope source upload steve)
        , ( "Steve accepted same-source alternative StageClosure cannot replace source envelope"
          , sameSourceDifferentStageCannotReplaceSourceEnvelope source steve upload)
        , ( "Upload final witness preserves exact independently accepted release envelope"
          , finalWitnessRetainsAcceptedRelease source upload)
        , ( "Steve final witness preserves exact independently accepted release envelope"
          , finalWitnessRetainsAcceptedRelease source steve)
        , ( "Upload same manifest/stage/LLVM do not identify complete trusted release"
          , equalReleaseCoordinatesCanHideDifferentTrust source upload)
        , ( "Steve same manifest/stage/LLVM do not identify complete trusted release"
          , equalReleaseCoordinatesCanHideDifferentTrust source steve)
        , ( "Upload same closed revision cannot replace exact final StageClosure"
          , finalWitnessStageRevisionOnlyRejects source upload)
        , ( "Steve same closed revision cannot replace exact final StageClosure"
          , finalWitnessStageRevisionOnlyRejects source steve)
        , ( "Upload altered full manifest with same ID cannot replace final witness"
          , finalWitnessManifestIdCollisionRejects source upload)
        , ( "Steve altered full manifest with same ID cannot replace final witness"
          , finalWitnessManifestIdCollisionRejects source steve)
        , ( "Upload substituted same-identity source proof cannot replace final witness"
          , finalWitnessSourceProofSubstitutionRejects source upload)
        , ( "Steve substituted same-identity source proof cannot replace final witness"
          , finalWitnessSourceProofSubstitutionRejects source steve)
        , ( "Upload substituted descriptor cannot replace exported checked descriptor"
          , finalWitnessDescriptorSubstitutionRejects source upload)
        , ( "Steve substituted descriptor cannot replace exported checked descriptor"
          , finalWitnessDescriptorSubstitutionRejects source steve)
        , ( "Same application identity with different accepted source assurance rejects Upload"
          , nativeFinalInstanceDifferentAcceptedSourceRejects source upload)
        , ( "Same application identity with different accepted source assurance rejects Steve"
          , nativeFinalInstanceDifferentAcceptedSourceRejects source steve)
        , ( "Stage revision gate rejects unrelated Upload source occurrence"
          , nativeStageRevisionGateRejectsUnrelated source upload)
        , ( "Stage revision gate rejects unrelated Steve source occurrence"
          , nativeStageRevisionGateRejectsUnrelated source steve)
        , ( "Matching instance revision alone does not identify occurrence key"
          , sameInstanceRevisionDifferentOccurrenceKey source)
        , ( "Typed native final instance rejects modified semantic actuals"
          , nativeFinalInstanceWrongActualRejects source upload)
        , ( "Typed native final instance rejects a different certified manifest"
          , nativeFinalInstanceOtherReleaseRejects source upload steve)
        , ( "Typed native final instance rejects a different StageClosure"
          , nativeFinalInstanceWrongStageRejects source upload steve)
        , ( "Generic actuals reject changed static instance binding"
          , instanceRejectsWrongStaticArgument source upload)
        , ( "Generic actuals reject missing static instance binding"
          , instanceRejectsMissingStaticArgument source upload)
        , ( "Generic actuals reject unregistered architecture instance"
          , instanceRejectsUnregisteredIdentity source upload)
        , ( "Generic actuals reject substituted declaration lineage"
          , instanceRejectsWrongDeclaration source upload)
        , ( "Source-manifest producer rejects unlisted source declaration"
          , producerRejectsUnlistedDeclaration source upload)
        , ( "Source-manifest producer rejects unbound architecture digest"
          , producerRejectsWrongArchitecture source upload)
        , ( "Produced binding rejects a release not carrying its exact closed manifest"
          , producedBindingRejectsOtherRelease source upload steve)
        , ( "NR-D06 stale stored Systems revision fails through certified-release caller"
          , staleStageSystemsRejected upload)
        , ( "NR-D06 stale closed-stage revision fails through certified-release caller"
          , staleClosedStageRejected upload)
        , ( "NR-D06 rehashed independently supplied manifest cannot retarget stage Systems digest"
          , independentlyRehashedSystemsManifestRejected upload)
        , ( "NR-D06 Steve stage closure retains same fail-closed release boundary"
          , staleStageSystemsRejected steve && staleClosedStageRejected steve)
        ]
  results <- mapM (uncurry report) checks
  if and results then pure () else exitFailure

requireStage :: String -> Either String StageClosureBundle -> IO StageClosureBundle
requireStage label result = case result of
  Left detail -> putStrLn ("FAIL: INT-005 " <> label <> " stage fixture -- " <> detail) >> exitFailure
  Right stage -> pure stage

report :: String -> Bool -> IO Bool
report label result = do
  putStrLn ((if result then "PASS: " else "FAIL: ") <> label)
  pure result

releaseCloses :: ReleaseFixture -> Bool
releaseCloses fixture =
  case runRelease fixture of
    Right release ->
      certifiedReleaseManifest release == fixtureManifest fixture
        && certifiedReleaseStageClosure release == fixtureStage fixture
        && certifiedReleaseLLVMArtifact release == fixtureLLVM fixture
        && Map.size (certifiedReleaseTrustBoundaries release) == 6
    Left _ -> False

wrongLLVMSourceRejected :: ReleaseFixture -> Bool
wrongLLVMSourceRejected fixture =
  let artifact = fixtureLLVM fixture
      contract = llvmArtifactContract artifact
      wrongDigest = digestText "int005.unrelated.systems"
      changed = artifact
        { llvmArtifactContract = contract
            { llvmContractSourceDigest = wrongDigest }
        }
      expected = stageSystemsDigest (fixtureStage fixture)
  in case runReleaseWith fixture
      (fixtureContext fixture)
      (fixtureManifest fixture)
      changed
      (fixtureTrust fixture) of
      Left (CertifiedReleaseLLVMSourceDigestMismatch expected' actual') ->
        expected' == expected && actual' == wrongDigest
      _ -> False

wrongLoweringRootRejected :: ReleaseFixture -> Bool
wrongLoweringRootRejected fixture =
  let wrongRoot = digestText "int005.unrelated.lowering-lineage"
      context = (fixtureContext fixture)
        { verificationLoweringLedgerRoot = wrongRoot }
      provisional = (fixtureManifest fixture)
        { manifestId = digestText "pending"
        , manifestLoweringLedgerRoot = wrongRoot
        }
      manifest = provisional
        { manifestId = deriveManifestId (fixtureLedger fixture) provisional }
      expected = stageLoweringRoot (fixtureStage fixture)
  in case runReleaseWith fixture context manifest
      (fixtureLLVM fixture) (fixtureTrust fixture) of
      Left (CertifiedReleaseManifestLoweringLedgerRootMismatch expected' actual') ->
        expected' == expected && actual' == wrongRoot
      _ -> False

noncanonicalLLVMTextRejected :: ReleaseFixture -> Bool
noncanonicalLLVMTextRejected fixture =
  let artifact = fixtureLLVM fixture
      changed = artifact
        { llvmArtifactText = llvmArtifactText artifact <> "; not canonical\n" }
  in case runReleaseWith fixture
      (fixtureContext fixture)
      (fixtureManifest fixture)
      changed
      (fixtureTrust fixture) of
      Left CertifiedReleaseLLVMTextMismatch -> True
      _ -> False

wrongLLVMProfileRejected :: ReleaseFixture -> Bool
wrongLLVMProfileRejected fixture =
  let expected = releaseProfileLLVMTarget (fixtureProfile fixture)
      changedTarget = expected
        { llvmTargetTripleName = "aarch64-unknown-linux-gnu" }
      profile = (fixtureProfile fixture)
        { releaseProfileLLVMTarget = changedTarget }
  in case certifyReleaseArtifact
      profile
      (fixtureContext fixture)
      (fixtureLedger fixture)
      (fixtureManifest fixture)
      (fixtureStage fixture)
      (fixtureLLVM fixture)
      (fixtureTrust fixture) of
      Left (CertifiedReleaseLLVMTargetProfileMismatch expected' actual') ->
        expected' == changedTarget && actual' == expected
      _ -> False

missingTrustKindRejected :: ReleaseFixture -> Bool
missingTrustKindRejected fixture =
  let reduced = filter
        ((/= TargetAssumptionTrust) . releaseTrustKind)
        (fixtureTrust fixture)
      expected = releaseProfileRequiredTrustKinds (fixtureProfile fixture)
      actual = Set.delete TargetAssumptionTrust expected
  in case runReleaseWith fixture
      (fixtureContext fixture)
      (fixtureManifest fixture)
      (fixtureLLVM fixture)
      reduced of
      Left (CertifiedReleaseTrustKindDomainMismatch expected' actual') ->
        expected' == expected && actual' == actual
      _ -> False

duplicateTrustIdentityRejected :: ReleaseFixture -> Bool
duplicateTrustIdentityRejected fixture =
  case fixtureTrust fixture of
    [] -> False
    first : _ ->
      case runReleaseWith fixture
          (fixtureContext fixture)
          (fixtureManifest fixture)
          (fixtureLLVM fixture)
          (fixtureTrust fixture <> [first]) of
        Left (CertifiedReleaseDuplicateTrustBoundary duplicateId) ->
          duplicateId == releaseTrustBoundaryId first
        _ -> False

blankTrustBasisRejected :: ReleaseFixture -> Bool
blankTrustBasisRejected fixture =
  case fixtureTrust fixture of
    [] -> False
    first : rest ->
      let changed = first { releaseTrustBasis = "   " }
      in case runReleaseWith fixture
          (fixtureContext fixture)
          (fixtureManifest fixture)
          (fixtureLLVM fixture)
          (changed : rest) of
          Left (CertifiedReleaseEmptyTrustBasis boundaryId) ->
            boundaryId == releaseTrustBoundaryId first
          _ -> False

-- NR-D06: accepted source and manifest fixtures do not authorize a stale
-- realization. Preserve the original supplied manifest and emitted LLVM while
-- changing only a StageClosure identity.
staleStageSystemsRejected :: ReleaseFixture -> Bool
staleStageSystemsRejected fixture =
  let stage = fixtureStage fixture
      corrupted = stage
        { stageClosureSystemsArtifactRevision =
            SystemsArtifactRevision "nr-d06.stale-systems-revision" }
      independentlyRejected = case verifyStageClosureBundle corrupted of
        Left (StageClosureStoredSystemsRevisionMismatch _ actual) ->
          actual == SystemsArtifactRevision "nr-d06.stale-systems-revision"
        _ -> False
  in independentlyRejected
      && case certifyReleaseArtifact
          (fixtureProfile fixture)
          (fixtureContext fixture)
          (fixtureLedger fixture)
          (fixtureManifest fixture)
          corrupted
          (fixtureLLVM fixture)
          (fixtureTrust fixture) of
        Left (CertifiedReleaseStageClosureRejected
          (StageClosureStoredSystemsRevisionMismatch _ actual)) ->
            actual == SystemsArtifactRevision "nr-d06.stale-systems-revision"
        _ -> False

staleClosedStageRejected :: ReleaseFixture -> Bool
staleClosedStageRejected fixture =
  let stage = fixtureStage fixture
      stale = ClosedStageContractRevision "nr-d06.stale-closed-stage"
      corrupted = stage { stageClosureContractRevision = stale }
  in case (verifyStageClosureBundle corrupted,
           certifyReleaseArtifact
             (fixtureProfile fixture)
             (fixtureContext fixture)
             (fixtureLedger fixture)
             (fixtureManifest fixture)
             corrupted
             (fixtureLLVM fixture)
             (fixtureTrust fixture)) of
      ( Left (StageClosureContractRevisionMismatch _ actual1)
        , Left (CertifiedReleaseStageClosureRejected
            (StageClosureContractRevisionMismatch _ actual2)) ) ->
          actual1 == stale
            && actual2 == stale
            && deriveClosedStageContractRevision stage
              == stageClosureContractRevision stage
      _ -> False

-- An attacker can form an internally consistent manifest and VerificationContext
-- with a different raw Systems digest. Acceptance still requires comparison to
-- the independently verified StageClosure's real Systems artifact.
independentlyRehashedSystemsManifestRejected :: ReleaseFixture -> Bool
independentlyRehashedSystemsManifestRejected fixture =
  let wrong = digestText "nr-d06.independent-but-wrong-systems"
      context = (fixtureContext fixture)
        { verificationImplementationDigest = wrong }
      proposed = (fixtureManifest fixture)
        { manifestId = digestText "pending"
        , manifestImplementationDigest = wrong }
      manifest = proposed
        { manifestId = deriveManifestId (fixtureLedger fixture) proposed }
  in case runReleaseWith fixture context manifest
        (fixtureLLVM fixture) (fixtureTrust fixture) of
      Left (CertifiedReleaseManifestImplementationDigestMismatch expected actual) ->
        expected == stageSystemsDigest (fixtureStage fixture)
          && actual == wrong
      _ -> False

-- The application is genuinely composed through the checked VER-009
-- constructors, rather than inventing GenericApplicationAssurance internals.
nativeAdapterSourceAssurance
  :: Either String GenericApplicationAssurance
nativeAdapterSourceAssurance = nativeAdapterSourceAssuranceWithEvidence
  (ArtifactIdentity
    (ArtifactRef "nr-d06.accepted-source-proof")
    (digestText "nr-d06.content-checked-source-evidence"))

nativeAdapterSourceAssuranceWithEvidence
  :: ArtifactIdentity -> Either String GenericApplicationAssurance
nativeAdapterSourceAssuranceWithEvidence sourceEvidence = do
  let declaration = DeclarationKey "nr-d06.generic.map"
      interface = InterfaceRevision "nr-d06.interface.v1"
      definition = DefinitionRevision "nr-d06.definition.v1"
      requirements = Set.empty
  body <- mapLeft show (prepareReusableGenericBodyAssurance
    declaration interface definition requirements sourceEvidence)
  application <- mapLeft show (deriveGenericApplicationIdentity declaration interface
    [(GenericStaticParameterKey "T", SemanticAtom "Blob")])
  disposition <- mapLeft show (checkGenericInstantiation
    strictGenericInstantiationPolicy requirements [])
  mapLeft show (composeGenericApplicationAssurance
    body requirements (deriveGenericDischargeLineage application definition disposition))

nativeAdapterSourceId :: GenericApplicationAssurance -> GenericApplicationIdentity
nativeAdapterSourceId source =
  genericDischargeApplicationIdentity (genericApplicationAssuranceLineage source)

nativeAdapterPair
  :: GenericApplicationAssurance
  -> ReleaseFixture
  -> Maybe (CertifiedApplicationArtifact, CertifiedReleaseArtifact)
nativeAdapterPair source fixture =
  case (certifyApplicationArtifact source (fixtureStage fixture), runRelease fixture) of
    (Right sourceArtifact, Right release) -> Just (sourceArtifact, release)
    _ -> Nothing

nativeAdapterAssociation
  :: GenericApplicationAssurance -> ReleaseFixture -> ExpectedSourceManifestAssociation
nativeAdapterAssociation source fixture = ExpectedSourceManifestAssociation
  (nativeAdapterSourceId source) (manifestId (fixtureManifest fixture))

nativeAdapterAccepts :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeAdapterAccepts source fixture = case nativeAdapterPair source fixture of
  Nothing -> False
  Just (sourceArtifact, release) ->
    case bindNativeFinalAuthority
        (nativeAdapterAssociation source fixture) sourceArtifact release of
      Left _ -> False
      Right native ->
        let stage = fixtureStage fixture
            subject = concreteSubjectStage (stageClosureConcrete stage)
            common = subjectStageBase subject
        in nativeFinalSourceIdentity native == nativeAdapterSourceId source
          && nativeFinalManifestId native == manifestId (fixtureManifest fixture)
          && nativeFinalRawSystemsDigest native == stageSystemsDigest stage
          && nativeFinalLoweringRoot native == stageLoweringRoot stage
          && nativeFinalSubjectRevision native == subjectStageRevision subject
          && nativeFinalInstanceRevision native == phase1StageInstanceRevision common
          && nativeFinalRealizationRevision native == phase1StageRealizationRevision common
          && nativeFinalSystemsRevision native == phase1StageSystemsArtifactRevision common
          && nativeFinalCommonContractRevision native == phase1StageContractRevision common
          && nativeFinalClosedContractRevision native == stageClosureContractRevision stage
          && nativeFinalVerifierProfile native == phase1StageVerifierProfileRevision common

nativeAdapterSwappedStageRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
nativeAdapterSwappedStageRejects source sourceFixture releaseFixtureValue =
  case ( certifyApplicationArtifact source (fixtureStage sourceFixture)
       , runRelease releaseFixtureValue ) of
    (Right sourceArtifact, Right release) ->
      case bindNativeFinalAuthority
          (nativeAdapterAssociation source releaseFixtureValue) sourceArtifact release of
        Left NativeFinalStageMismatch -> True
        _ -> False
    _ -> False

nativeAdapterWrongSourceRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeAdapterWrongSourceRejects source fixture =
  case ( nativeAdapterPair source fixture
       , deriveGenericApplicationIdentity
           (DeclarationKey "nr-d06.other.source")
           (InterfaceRevision "nr-d06.interface.v1") [] ) of
    (Just (sourceArtifact, release), Right other) ->
      let association = (nativeAdapterAssociation source fixture)
            { expectedSourceApplicationIdentity = other }
      in case bindNativeFinalAuthority association sourceArtifact release of
          Left (NativeFinalSourceMismatch expected actual) ->
            expected == other && actual == nativeAdapterSourceId source
          _ -> False
    _ -> False

nativeAdapterWrongManifestRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
nativeAdapterWrongManifestRejects source fixture otherFixture =
  case nativeAdapterPair source fixture of
    Nothing -> False
    Just (sourceArtifact, release) ->
      let wrong = manifestId (fixtureManifest otherFixture)
          association = (nativeAdapterAssociation source fixture)
            { expectedSourceManifestId = wrong }
      in wrong /= manifestId (fixtureManifest fixture)
         && case bindNativeFinalAuthority association sourceArtifact release of
              Left (NativeFinalManifestMismatch expected actual) ->
                expected == wrong && actual == manifestId (fixtureManifest fixture)
              _ -> False

-- Producer tests distinguish the checked VER-012/INT-002 source manifest
-- closure from a caller-created pair of source and manifest identifiers.
producerInputs
  :: GenericApplicationAssurance
  -> Either String (VerificationBundle, ApplicationAssurancePolicy)
producerInputs source = do
  graph <- mapLeft show (buildVerificationRevisionGraph [] Set.empty)
  let lineage = genericApplicationAssuranceLineage source
      application = genericDischargeApplicationIdentity lineage
      declaration = DeclarationIdentity
        { identityDeclarationKey = genericApplicationDeclarationKey application
        , identityInterfaceRevision = genericApplicationInterfaceRevision application
        , identityDefinitionRevision = genericDischargeDefinitionRevision lineage
        }
      policy = ApplicationAssurancePolicy
        (AssurancePolicyRevision "audit.source-manifest-binding.v1") Set.empty
  bundle <- mapLeft show (buildVerificationBundle
    (digestText "audit.accepted.source.revision")
    [declaration] [deriveArchitectureInstanceIdentity (sourceInstanceDescriptor source)] [] graph policy [])
  Right (bundle, policy)

sourceInstanceDescriptor :: GenericApplicationAssurance -> ArchitectureInstanceDescriptor
sourceInstanceDescriptor source =
  let lineage = genericApplicationAssuranceLineage source
      application = genericDischargeApplicationIdentity lineage
      declaration = DeclarationIdentity
        { identityDeclarationKey = genericApplicationDeclarationKey application
        , identityInterfaceRevision = genericApplicationInterfaceRevision application
        , identityDefinitionRevision = genericDischargeDefinitionRevision lineage }
  in ArchitectureInstanceDescriptor
    { architectureInstanceKey = InstanceKey "audit.generic.actual.instance"
    , architectureParentInstanceKey = Nothing
    , architectureDeclarationIdentity = declaration
    , architectureStaticBindings = Map.fromList
        [ (unGenericStaticParameterKey key, value)
        | (key,value) <- Map.toAscList (genericApplicationSemanticArguments application)
        ]
    }

emptyProducerSelection :: ManifestClosureSelection
emptyProducerSelection = ManifestClosureSelection
  { manifestClosureEvidence = Set.empty
  , manifestClosureAssumptions = Set.empty
  , manifestClosureExports = Map.empty
  , manifestClosureUses = Set.empty
  }

produceFixture
  :: GenericApplicationAssurance
  -> ReleaseFixture
  -> Either String (CertifiedSourceManifestBinding, ReleaseFixture)
produceFixture source fixture = do
  (bundle, policy) <- producerInputs source
  let context = (fixtureContext fixture)
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle }
  binding <- mapLeft show (closeSourceManifestBindingForInstance
    source (sourceInstanceDescriptor source) bundle policy
    context (fixtureLedger fixture) emptyProducerSelection)
  let updated = fixture
        { fixtureContext = context
        , fixtureManifest = sourceManifestBindingManifest binding }
  Right (binding, updated)

-- This checks the *complete* producer-verified semantic descriptor, rather
-- than treating its derived architecture identity as a substitute.
checkedDescriptorRetained
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
checkedDescriptorRetained source fixture =
  case produceFixture source fixture of
    Left _ -> False
    Right (binding, _) ->
      let descriptor = sourceInstanceDescriptor source
      in sourceManifestBindingArchitectureDescriptor binding == Just descriptor
          && sourceManifestBindingArchitectureInstance binding
               == Just (deriveArchitectureInstanceIdentity descriptor)

producedBindingAccepted
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
producedBindingAccepted source fixture = case produceFixture source fixture of
  Left _ -> False
  Right (binding, producedFixture) ->
    case nativeAdapterPair source producedFixture of
      Nothing -> False
      Just (sourceArtifact, release) ->
        case bindProducedFinalAuthority binding sourceArtifact release of
          Left _ -> False
          Right native ->
            sourceManifestBindingArchitectureInstance binding
                == Just (deriveArchitectureInstanceIdentity (sourceInstanceDescriptor source))
              && nativeFinalSourceIdentity native == nativeAdapterSourceId source
              && nativeFinalManifestId native
                == manifestId (fixtureManifest producedFixture)
              && nativeFinalRawSystemsDigest native
                == stageSystemsDigest (fixtureStage fixture)


-- | The declaration-only producer can close the exact same manifest, but
-- cannot issue final authority even with matching independently accepted
-- source artifact and release. Only the checked-instance path may do so.
declarationOnlyBindingRejected
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
declarationOnlyBindingRejected source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (checked, produced)) ->
      case closeSourceManifestBinding source bundle policy
          (fixtureContext produced) (fixtureLedger produced)
          emptyProducerSelection of
        Left _ -> False
        Right weak ->
          sourceManifestBindingManifest weak == sourceManifestBindingManifest checked
            && sourceManifestBindingArchitectureInstance weak == Nothing
            && sourceManifestBindingArchitectureDescriptor weak == Nothing
            && case nativeAdapterPair source produced of
              Nothing -> False
              Just (sourceArtifact, release) ->
                case bindProducedFinalAuthority weak sourceArtifact release of
                  Left SourceManifestInstanceNotBound -> True
                  _ -> False
    _ -> False


-- | The final opaque witness retains the exact checked-instance producer token,
-- not just separately copied source/manifest/descriptor projections.
finalWitnessRetainsCheckedSourceManifestBinding
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsCheckedSourceManifestBinding source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (checked, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let exported = nativeCorrespondenceSourceManifestBinding witness
              in exported == checked
                && sourceManifestBindingSourceAssurance exported
                    == nativeCorrespondenceSourceAssurance witness
                && sourceManifestBindingManifest exported
                    == nativeCorrespondenceManifest witness
                && sourceManifestBindingArchitectureDescriptor exported
                    == Just (nativeCorrespondenceArchitectureDescriptor witness)
    _ -> False

-- | Declaration-only closure can carry the exact same source assurance and
-- manifest as the checked-instance producer while lacking its descriptor.
-- Those equal projections must not identify the producer token: the real
-- low-level final binder rejects the weak token, and the final witness retains
-- the checked token that actually passed.
declarationOnlyTokenCannotReplaceFinalProducer
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
declarationOnlyTokenCannotReplaceFinalProducer source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (checked, produced)) ->
      case closeSourceManifestBinding source bundle policy
          (fixtureContext produced) (fixtureLedger produced)
          emptyProducerSelection of
        Left _ -> False
        Right weak ->
          case nativeAdapterPair source produced of
            Nothing -> False
            Just (sourceArtifact, release) ->
              case closeNativeFinalInstanceCorrespondence
                  source (sourceInstanceDescriptor source) bundle policy
                  (fixtureContext produced) (fixtureLedger produced)
                  emptyProducerSelection sourceArtifact release of
                Left _ -> False
                Right witness ->
                  sourceManifestBindingSourceAssurance weak
                      == sourceManifestBindingSourceAssurance checked
                    && sourceManifestBindingManifest weak
                      == sourceManifestBindingManifest checked
                    && sourceManifestBindingArchitectureDescriptor weak == Nothing
                    && weak /= checked
                    && nativeCorrespondenceSourceManifestBinding witness == checked
                    && nativeCorrespondenceSourceManifestBinding witness /= weak
                    && case bindProducedFinalAuthority weak sourceArtifact release of
                        Left SourceManifestInstanceNotBound -> True
                        _ -> False
    _ -> False

-- | Replay the original independently accepted source/release stage and
-- producer manifest through the concrete native projections. Revisions and
-- raw digests remain separate *types* and are checked against the actual
-- accepted StageClosure, not a synthetic Rocq nat representation.
nativeManifestStageReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeManifestStageReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let stage = nativeCorrespondenceStageClosure witness
                  authority = nativeCorrespondenceAuthority witness
              in case replayNativeManifestStageCoordinates witness
                    (nativeCorrespondenceManifest witness) stage of
                Left _ -> False
                Right view ->
                  nativeReplayRawDigest view
                      == NativeRawSystemsDigest (stageSystemsDigest stage)
                    && nativeReplayLoweringRoot view
                      == NativeLoweringRootDigest (stageLoweringRoot stage)
                    && nativeReplaySubjectRevision view == nativeFinalSubjectRevision authority
                    && nativeReplayInstanceRevision view == nativeFinalInstanceRevision authority
                    && nativeReplayRealizationRevision view == nativeFinalRealizationRevision authority
                    && nativeReplaySystemsRevision view == nativeFinalSystemsRevision authority
                    && nativeReplayCommonRevision view == nativeFinalCommonContractRevision authority
                    && nativeReplayClosedRevision view == nativeFinalClosedContractRevision authority
                    && nativeReplayVerifierProfile view == nativeFinalVerifierProfile authority
    _ -> False

-- | Strict executable transport check over actual independently accepted
-- Upload/Steve objects, not caller-invented revision values. Exact reversible
-- Text payloads and disjoint R/L role tags are tested in both directions.
-- This is a bounded native wire property, not a native-to-Rocq Unicode proof.
nativeDigestRoleWireReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeDigestRoleWireReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeManifestStageCoordinates witness
                (nativeCorrespondenceManifest witness)
                (nativeCorrespondenceStageClosure witness) of
                Left _ -> False
                Right view ->
                  let raw = nativeReplayRawDigest view
                      root = nativeReplayLoweringRoot view
                      rawWire = encodeNativeRawSystemsDigestWire raw
                      rootWire = encodeNativeLoweringRootWire root
                      acceptedManifest = nativeCorrespondenceManifest witness
                  in raw == NativeRawSystemsDigest
                        (manifestImplementationDigest acceptedManifest)
                    && root == NativeLoweringRootDigest
                        (manifestLoweringLedgerRoot acceptedManifest)
                    && decodeNativeRawSystemsDigestWire rawWire == Just raw
                    && decodeNativeLoweringRootWire rootWire == Just root
                    && rawWire /= rootWire
                    && decodeNativeRawSystemsDigestWire rootWire == Nothing
                    && decodeNativeLoweringRootWire rawWire == Nothing
    _ -> False


-- | The three distinct normalized/common/closed revision values are read
-- from the actual accepted StageClosure through the existing whole-object
-- replay, never reconstructed as unaccepted stage authority. Exact payload
-- roundtrips must reject even valid wires with the wrong revision role.
nativeRevisionRoleWireReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeRevisionRoleWireReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeManifestStageCoordinates witness
                (nativeCorrespondenceManifest witness)
                (nativeCorrespondenceStageClosure witness) of
                Left _ -> False
                Right view ->
                  let systems = nativeReplaySystemsRevision view
                      common = nativeReplayCommonRevision view
                      closed = nativeReplayClosedRevision view
                      systemsWire = encodeNativeSystemsRevisionWire systems
                      commonWire = encodeNativeCommonContractRevisionWire common
                      closedWire = encodeNativeClosedContractRevisionWire closed
                      rawWire = encodeNativeRawSystemsDigestWire
                        (nativeReplayRawDigest view)
                      rootWire = encodeNativeLoweringRootWire
                        (nativeReplayLoweringRoot view)
                      authority = nativeCorrespondenceAuthority witness
                  in systems == nativeFinalSystemsRevision authority
                    && common == nativeFinalCommonContractRevision authority
                    && closed == nativeFinalClosedContractRevision authority
                    && decodeNativeSystemsRevisionWire systemsWire == Just systems
                    && decodeNativeCommonContractRevisionWire commonWire == Just common
                    && decodeNativeClosedContractRevisionWire closedWire == Just closed
                    && systemsWire /= commonWire
                    && systemsWire /= closedWire
                    && commonWire /= closedWire
                    && systemsWire /= rawWire
                    && systemsWire /= rootWire
                    && commonWire /= rawWire
                    && commonWire /= rootWire
                    && closedWire /= rawWire
                    && closedWire /= rootWire
                    && decodeNativeSystemsRevisionWire commonWire == Nothing
                    && decodeNativeSystemsRevisionWire closedWire == Nothing
                    && decodeNativeCommonContractRevisionWire systemsWire == Nothing
                    && decodeNativeCommonContractRevisionWire closedWire == Nothing
                    && decodeNativeClosedContractRevisionWire systemsWire == Nothing
                    && decodeNativeClosedContractRevisionWire commonWire == Nothing
                    && decodeNativeRawSystemsDigestWire systemsWire == Nothing
                    && decodeNativeLoweringRootWire closedWire == Nothing
    _ -> False

-- | Genuine accepted replay provides a payload, but the other wrappers
-- below are explicitly UNACCEPTED role-collision probes. Equal underlying
-- Text never upgrades one stage revision or manifest digest into another.
nativeRevisionRoleEqualPayloadSubstitutionsReject
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeRevisionRoleEqualPayloadSubstitutionsReject source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeManifestStageCoordinates witness
                (nativeCorrespondenceManifest witness)
                (nativeCorrespondenceStageClosure witness) of
                Left _ -> False
                Right view ->
                  let payload = unSystemsArtifactRevision
                        (nativeReplaySystemsRevision view)
                      systemsWire = encodeNativeSystemsRevisionWire
                        (SystemsArtifactRevision payload)
                      commonWire = encodeNativeCommonContractRevisionWire
                        (Phase1StageContractRevision payload)
                      closedWire = encodeNativeClosedContractRevisionWire
                        (ClosedStageContractRevision payload)
                      rawWire = encodeNativeRawSystemsDigestWire
                        (NativeRawSystemsDigest (Digest payload))
                      rootWire = encodeNativeLoweringRootWire
                        (NativeLoweringRootDigest (Digest payload))
                  in systemsWire /= commonWire
                    && systemsWire /= closedWire
                    && commonWire /= closedWire
                    && systemsWire /= rawWire
                    && systemsWire /= rootWire
                    && commonWire /= rawWire
                    && commonWire /= rootWire
                    && closedWire /= rawWire
                    && closedWire /= rootWire
                    && decodeNativeSystemsRevisionWire commonWire == Nothing
                    && decodeNativeSystemsRevisionWire closedWire == Nothing
                    && decodeNativeCommonContractRevisionWire systemsWire == Nothing
                    && decodeNativeCommonContractRevisionWire closedWire == Nothing
                    && decodeNativeClosedContractRevisionWire systemsWire == Nothing
                    && decodeNativeClosedContractRevisionWire commonWire == Nothing
                    && decodeNativeRawSystemsDigestWire closedWire == Nothing
                    && decodeNativeLoweringRootWire systemsWire == Nothing
    _ -> False

-- | Read the three revision roles only from the checked producer and exact
-- accepted VER-010 / INT-005 consumer replay. Tagged data is never authority.
nativeStageIdentityRoleReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeStageIdentityRoleReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeManifestStageCoordinates witness
                (nativeCorrespondenceManifest witness)
                (nativeCorrespondenceStageClosure witness) of
                Left _ -> False
                Right view ->
                  let subject = nativeReplaySubjectRevision view
                      instanceRev = nativeReplayInstanceRevision view
                      realization = nativeReplayRealizationRevision view
                      bWire = encodeNativeSubjectRevisionWire subject
                      iWire = encodeNativeInstanceRevisionWire instanceRev
                      aWire = encodeNativeRealizationRevisionWire realization
                      existingWires =
                        [ encodeNativeRawSystemsDigestWire (nativeReplayRawDigest view)
                        , encodeNativeLoweringRootWire (nativeReplayLoweringRoot view)
                        , encodeNativeSystemsRevisionWire (nativeReplaySystemsRevision view)
                        , encodeNativeCommonContractRevisionWire (nativeReplayCommonRevision view)
                        , encodeNativeClosedContractRevisionWire (nativeReplayClosedRevision view)
                        ]
                      wires = bWire : iWire : aWire : existingWires
                      authority = nativeCorrespondenceAuthority witness
                  in subject == nativeFinalSubjectRevision authority
                    && instanceRev == nativeFinalInstanceRevision authority
                    && realization == nativeFinalRealizationRevision authority
                    && decodeNativeSubjectRevisionWire bWire == Just subject
                    && decodeNativeInstanceRevisionWire iWire == Just instanceRev
                    && decodeNativeRealizationRevisionWire aWire == Just realization
                    && Set.size (Set.fromList wires) == length wires
                    && decodeNativeSubjectRevisionWire iWire == Nothing
                    && decodeNativeSubjectRevisionWire aWire == Nothing
                    && decodeNativeInstanceRevisionWire bWire == Nothing
                    && decodeNativeInstanceRevisionWire aWire == Nothing
                    && decodeNativeRealizationRevisionWire bWire == Nothing
                    && decodeNativeRealizationRevisionWire iWire == Nothing
                    && all (== Nothing) (map decodeNativeSubjectRevisionWire existingWires)
                    && all (== Nothing) (map decodeNativeInstanceRevisionWire existingWires)
                    && all (== Nothing) (map decodeNativeRealizationRevisionWire existingWires)
    _ -> False

-- | This deliberately constructs UNACCEPTED role wrappers containing the
-- same payload taken from a real accepted instance revision. Equal Text does
-- not allow a subject, instance or realization to impersonate another domain.
nativeStageIdentityEqualPayloadRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeStageIdentityEqualPayloadRejects source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeManifestStageCoordinates witness
                (nativeCorrespondenceManifest witness)
                (nativeCorrespondenceStageClosure witness) of
                Left _ -> False
                Right view ->
                  let same = unInstanceRevision (nativeReplayInstanceRevision view)
                      bWire = encodeNativeSubjectRevisionWire (SubjectStageRevision same)
                      iWire = encodeNativeInstanceRevisionWire (InstanceRevision same)
                      aWire = encodeNativeRealizationRevisionWire (RealizationRevision same)
                  in Set.size (Set.fromList [bWire, iWire, aWire]) == 3
                    && decodeNativeSubjectRevisionWire iWire == Nothing
                    && decodeNativeSubjectRevisionWire aWire == Nothing
                    && decodeNativeInstanceRevisionWire bWire == Nothing
                    && decodeNativeInstanceRevisionWire aWire == Nothing
                    && decodeNativeRealizationRevisionWire bWire == Nothing
                    && decodeNativeRealizationRevisionWire iWire == Nothing
    _ -> False


-- | Real profile value from exact accepted checked source, VER-010 and
-- INT-005 objects. The role tag is a codec, not a profile acceptor.
nativeVerifierProfileWireReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeVerifierProfileWireReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right accepted ->
                  let c = nativeExactReplayCoordinates accepted
                      profile = NativeVerifierProfileText (nativeReplayVerifierProfile c)
                      wire = encodeNativeVerifierProfileWire profile
                      other =
                        [ encodeNativeRawSystemsDigestWire (nativeReplayRawDigest c)
                        , encodeNativeLoweringRootWire (nativeReplayLoweringRoot c)
                        , encodeNativeSystemsRevisionWire (nativeReplaySystemsRevision c)
                        , encodeNativeCommonContractRevisionWire (nativeReplayCommonRevision c)
                        , encodeNativeClosedContractRevisionWire (nativeReplayClosedRevision c)
                        , encodeNativeSubjectRevisionWire (nativeReplaySubjectRevision c)
                        , encodeNativeInstanceRevisionWire (nativeReplayInstanceRevision c)
                        , encodeNativeRealizationRevisionWire (nativeReplayRealizationRevision c)
                        ]
                  in unNativeVerifierProfileText profile ==
                       nativeFinalVerifierProfile (nativeCorrespondenceAuthority witness)
                    && decodeNativeVerifierProfileWire wire == Just profile
                    && all (/= wire) other
                    && all (== Nothing) (map decodeNativeVerifierProfileWire other)
    _ -> False

-- | Eight UNACCEPTED wrappers deliberately use exactly the accepted
-- profile's Text payload; none may substitute for the profile role.
-- A changed P-prefixed payload may still decode as data, but is not equal
-- to the profile retained by the exact accepted consumer witness.
nativeVerifierProfileSamePayloadRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeVerifierProfileSamePayloadRejects source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right accepted ->
                  let payload = nativeReplayVerifierProfile (nativeExactReplayCoordinates accepted)
                      profile = NativeVerifierProfileText payload
                      actual = encodeNativeVerifierProfileWire profile
                      foreignWires =
                        [ encodeNativeRawSystemsDigestWire (NativeRawSystemsDigest (Digest payload))
                        , encodeNativeLoweringRootWire (NativeLoweringRootDigest (Digest payload))
                        , encodeNativeSystemsRevisionWire (SystemsArtifactRevision payload)
                        , encodeNativeCommonContractRevisionWire (Phase1StageContractRevision payload)
                        , encodeNativeClosedContractRevisionWire (ClosedStageContractRevision payload)
                        , encodeNativeSubjectRevisionWire (SubjectStageRevision payload)
                        , encodeNativeInstanceRevisionWire (InstanceRevision payload)
                        , encodeNativeRealizationRevisionWire (RealizationRevision payload)
                        ]
                      altered = NativeVerifierProfileText (payload <> ".unaccepted")
                  in Set.size (Set.fromList (actual : foreignWires)) == 9
                    && all (== Nothing) (map decodeNativeVerifierProfileWire foreignWires)
                    && decodeNativeVerifierProfileWire actual == Just profile
                    && decodeNativeVerifierProfileWire
                         (encodeNativeVerifierProfileWire altered) /= Just profile
    _ -> False

-- | Exact checked-instance source/manifest producer and full accepted
-- VER-010/INT-005 objects are required before inspecting the occurrence key.
-- The key is derived from the retained architecture descriptor, NOT from
-- the independently accepted StageClosure, which does not contain one.
-- Nine unaccepted equal-payload role substitutions and same-revision/different-
-- key occurrence identities cannot impersonate the accepted K wire.
nativeOccurrenceKeyWireReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeOccurrenceKeyWireReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right accepted ->
                  let occurrence = nativeCorrespondenceArchitectureInstance witness
                      key = identityInstanceKey occurrence
                      revision = identityInstanceRevision occurrence
                      payload = unInstanceKey key
                      wire = encodeNativeOccurrenceKeyWire key
                      otherWires =
                        [ encodeNativeRawSystemsDigestWire (NativeRawSystemsDigest (Digest payload))
                        , encodeNativeLoweringRootWire (NativeLoweringRootDigest (Digest payload))
                        , encodeNativeSystemsRevisionWire (SystemsArtifactRevision payload)
                        , encodeNativeCommonContractRevisionWire (Phase1StageContractRevision payload)
                        , encodeNativeClosedContractRevisionWire (ClosedStageContractRevision payload)
                        , encodeNativeSubjectRevisionWire (SubjectStageRevision payload)
                        , encodeNativeInstanceRevisionWire (InstanceRevision payload)
                        , encodeNativeRealizationRevisionWire (RealizationRevision payload)
                        , encodeNativeVerifierProfileWire (NativeVerifierProfileText payload)
                        ]
                      alteredKey = InstanceKey (payload <> ".unaccepted")
                      otherOccurrence = ArchitectureInstanceIdentity alteredKey revision
                      concreteStage = nativeExactReplayCoordinates accepted
                  in decodeNativeOccurrenceKeyWire wire == Just key
                    && key == identityInstanceKey
                         (deriveArchitectureInstanceIdentity
                           (nativeCorrespondenceArchitectureDescriptor witness))
                    && Set.size (Set.fromList (wire : otherWires)) == 10
                    && all (== Nothing) (map decodeNativeOccurrenceKeyWire otherWires)
                    && decodeNativeOccurrenceKeyWire
                         (encodeNativeOccurrenceKeyWire alteredKey) /= Just key
                    && otherOccurrence /= occurrence
                    && identityInstanceRevision otherOccurrence == revision
                    && nativeReplayInstanceRevision concreteStage ==
                         nativeFinalInstanceRevision
                           (nativeCorrespondenceAuthority witness)
    _ -> False

-- | The checked architecture occurrence identity is the pair of its actual
-- InstanceKey and InstanceRevision. Read it only after the exact checked
-- source-manifest producer and full independently accepted source/release
-- replay. Equal I-stage revision does not identify the originating occurrence.
-- The forged pairs below are data only and cannot acquire producer acceptance.
nativeCheckedOccurrenceIdentityPairReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeCheckedOccurrenceIdentityPairReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right accepted ->
                  let occurrence = nativeCorrespondenceArchitectureInstance witness
                      key = identityInstanceKey occurrence
                      revision = identityInstanceRevision occurrence
                      pairWires@(keyWire, revisionWire) =
                        encodeNativeCheckedOccurrenceIdentityWires occurrence
                      stageRevision = nativeReplayInstanceRevision
                        (nativeExactReplayCoordinates accepted)
                      otherKey = InstanceKey (unInstanceKey key <> ".unaccepted")
                      otherOccurrence = ArchitectureInstanceIdentity otherKey revision
                      wrongRolePairs =
                        [ (encodeNativeInstanceRevisionWire (InstanceRevision (unInstanceKey key)), revisionWire)
                        , (keyWire, encodeNativeOccurrenceKeyWire (InstanceKey (unInstanceRevision revision)))
                        , (encodeNativeVerifierProfileWire (NativeVerifierProfileText (unInstanceKey key)), revisionWire)
                        , (keyWire, encodeNativeRawSystemsDigestWire (NativeRawSystemsDigest (Digest (unInstanceRevision revision))))
                        ]
                      stageEqualityOnly =
                        case checkNativeStageRevisionEquality witness of
                          Left (NativeStageRevisionDifferent expected actual) ->
                            expected == revision && actual == stageRevision
                          Right receipt ->
                            nativeStageRevisionEqualityOccurrence receipt == occurrence
                              && nativeStageRevisionEqualityStageRevision receipt == stageRevision
                  in decodeNativeCheckedOccurrenceIdentityWires pairWires == Just occurrence
                    && keyWire == encodeNativeOccurrenceKeyWire key
                    && revisionWire == encodeNativeInstanceRevisionWire revision
                    && all (== Nothing)
                         (map decodeNativeCheckedOccurrenceIdentityWires wrongRolePairs)
                    && otherOccurrence /= occurrence
                    && identityInstanceRevision otherOccurrence == revision
                    && decodeNativeCheckedOccurrenceIdentityWires
                         (encodeNativeCheckedOccurrenceIdentityWires otherOccurrence)
                         == Just otherOccurrence
                    && decodeNativeCheckedOccurrenceIdentityWires
                         (encodeNativeCheckedOccurrenceIdentityWires otherOccurrence)
                         /= Just occurrence
                    && stageEqualityOnly
    _ -> False

-- | The actual GenericApplicationIdentity includes a checked map of
-- semantic arguments. D/V scalar wires are a reversible but INCOMPLETE
-- projection: equal declaration/interface values cannot replace actuals,
-- source assurance, checked producer binding or independently accepted
-- manifest, VER-010 source and INT-005 release whole objects.
nativeGenericApplicationScalarReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeGenericApplicationScalarReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right _ ->
                  let application = genericDischargeApplicationIdentity
                        (genericApplicationAssuranceLineage
                          (nativeCorrespondenceSourceAssurance witness))
                      declaration = genericApplicationDeclarationKey application
                      interfaceRevision = genericApplicationInterfaceRevision application
                      (declarationWire, interfaceWire) =
                        encodeNativeGenericApplicationScalarWires application
                      forgedActuals = Map.insert
                        (GenericStaticParameterKey "audit.impl.unaccepted.actual")
                        (SemanticAtom "forged") (genericApplicationSemanticArguments application)
                      forgedApplication = application
                        { genericApplicationSemanticArguments = forgedActuals }
                      wrongPairs =
                        [ (encodeNativeOccurrenceKeyWire (InstanceKey (unDeclarationKey declaration)), interfaceWire)
                        , (declarationWire, encodeNativeInstanceRevisionWire
                            (InstanceRevision (unInterfaceRevision interfaceRevision)))
                        , (interfaceWire, declarationWire)
                        ]
                      samePayloadForeign =
                        [ encodeNativeRawSystemsDigestWire
                            (NativeRawSystemsDigest (Digest (unDeclarationKey declaration)))
                        , encodeNativeLoweringRootWire
                            (NativeLoweringRootDigest (Digest (unDeclarationKey declaration)))
                        , encodeNativeOccurrenceKeyWire
                            (InstanceKey (unDeclarationKey declaration))
                        , encodeNativeInstanceRevisionWire
                            (InstanceRevision (unDeclarationKey declaration))
                        ]
                  in decodeNativeGenericApplicationScalarWires
                       (declarationWire, interfaceWire)
                       == Just (declaration, interfaceRevision)
                    && decodeNativeGenericDeclarationWire declarationWire == Just declaration
                    && decodeNativeGenericInterfaceWire interfaceWire == Just interfaceRevision
                    && all (== Nothing)
                         (map decodeNativeGenericApplicationScalarWires wrongPairs)
                    && all (== Nothing)
                         (map decodeNativeGenericDeclarationWire samePayloadForeign)
                    && all (== Nothing)
                         (map decodeNativeGenericInterfaceWire samePayloadForeign)
                    && forgedApplication /= application
                    && genericApplicationSemanticArguments forgedApplication
                         /= genericApplicationSemanticArguments application
                    && encodeNativeGenericApplicationScalarWires forgedApplication
                         == (declarationWire, interfaceWire)
    _ -> False

-- | Q-key domain is read from the *actually checked* GenericApplicationIdentity,
-- with independently accepted manifest, source and release whole-object replay.
-- Key-domain equality is INSUFFICIENT to prove SemanticForm values equal. New
-- adversarial application values below are never claimed to be accepted.
nativeGenericActualsKeyDomainReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeGenericActualsKeyDomainReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right _ ->
                  let application = genericDischargeApplicationIdentity
                        (genericApplicationAssuranceLineage
                          (nativeCorrespondenceSourceAssurance witness))
                      actuals = genericApplicationSemanticArguments application
                      keys = Map.keys actuals
                      actualWires = encodeNativeGenericActualsKeyDomainWires application
                      probeKey = GenericStaticParameterKey "audit.impl.unaccepted.probe"
                      probeWire = encodeNativeGenericStaticParameterKeyWire probeKey
                      alteredActualsA = Map.insert probeKey (SemanticAtom "alpha") actuals
                      alteredActualsB = Map.insert probeKey (SemanticAtom "beta") actuals
                      alteredApplicationA = application
                        { genericApplicationSemanticArguments = alteredActualsA }
                      alteredApplicationB = application
                        { genericApplicationSemanticArguments = alteredActualsB }
                      foreignWires =
                        [ encodeNativeGenericDeclarationWire
                            (DeclarationKey (unGenericStaticParameterKey probeKey))
                        , encodeNativeGenericInterfaceWire
                            (InterfaceRevision (unGenericStaticParameterKey probeKey))
                        , encodeNativeOccurrenceKeyWire
                            (InstanceKey (unGenericStaticParameterKey probeKey))
                        , encodeNativeRawSystemsDigestWire
                            (NativeRawSystemsDigest (Digest (unGenericStaticParameterKey probeKey)))
                        ]
                  in decodeNativeGenericActualsKeyDomainWires actualWires == Just keys
                    && decodeNativeGenericStaticParameterKeyWire probeWire == Just probeKey
                    && decodeNativeGenericActualsKeyDomainWires
                         (encodeNativeGenericActualsKeyDomainWires alteredApplicationA)
                         == Just (Map.keys alteredActualsA)
                    && alteredApplicationA /= alteredApplicationB
                    && alteredActualsA /= alteredActualsB
                    && encodeNativeGenericActualsKeyDomainWires alteredApplicationA
                         == encodeNativeGenericActualsKeyDomainWires alteredApplicationB
                    && decodeNativeGenericActualsKeyDomainWires
                         [probeWire, probeWire] == Nothing
                    && decodeNativeGenericActualsKeyDomainWires
                         [ encodeNativeGenericStaticParameterKeyWire
                             (GenericStaticParameterKey "z")
                         , encodeNativeGenericStaticParameterKeyWire
                             (GenericStaticParameterKey "a") ] == Nothing
                    && all (== Nothing)
                         (map decodeNativeGenericStaticParameterKeyWire foreignWires)
                    && all (== Nothing)
                         (map decodeNativeGenericActualsKeyDomainWires
                           (map (: []) foreignWires))
    _ -> False

-- | The accepted object is replayed before inspecting *actual native*
-- GenericApplicationIdentity SemanticForm entries. M is a partial codec for
-- SemanticAtom only. Any probe map constructed below is intentionally
-- UNACCEPTED; same Q-key domain and two M atoms are not source authority.
nativeGenericSemanticAtomReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeGenericSemanticAtomReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right _ ->
                  let application = genericDischargeApplicationIdentity
                        (genericApplicationAssuranceLineage
                          (nativeCorrespondenceSourceAssurance witness))
                      actuals = genericApplicationSemanticArguments application
                      atomA = SemanticAtom "audit.atom.alpha"
                      atomB = SemanticAtom "audit.atom.beta"
                      probeKey = GenericStaticParameterKey "audit.impl.unaccepted.atom.probe"
                      alteredA = application
                        { genericApplicationSemanticArguments =
                            Map.insert probeKey atomA actuals }
                      alteredB = application
                        { genericApplicationSemanticArguments =
                            Map.insert probeKey atomB actuals }
                      unsupportedForms =
                        [ SemanticOrdered [atomA]
                        , SemanticUnordered (Set.singleton atomA)
                        , SemanticRecord (Map.singleton "v" atomA)
                        ]
                      foreignWires =
                        [ encodeNativeGenericStaticParameterKeyWire
                            (GenericStaticParameterKey "audit.atom.alpha")
                        , encodeNativeGenericDeclarationWire
                            (DeclarationKey "audit.atom.alpha")
                        , encodeNativeGenericInterfaceWire
                            (InterfaceRevision "audit.atom.alpha")
                        , encodeNativeOccurrenceKeyWire
                            (InstanceKey "audit.atom.alpha")
                        , encodeNativeVerifierProfileWire
                            (NativeVerifierProfileText "audit.atom.alpha")
                        ]
                      actualFormChecked form =
                        case form of
                          SemanticAtom _ ->
                            (encodeNativeSemanticAtomWire form >>=
                              decodeNativeSemanticAtomWire) == Just form
                          _ -> encodeNativeSemanticAtomWire form == Nothing
                  in Map.notMember probeKey actuals
                    && all actualFormChecked (Map.elems actuals)
                    && (encodeNativeSemanticAtomWire atomA >>=
                          decodeNativeSemanticAtomWire) == Just atomA
                    && (encodeNativeSemanticAtomWire atomB >>=
                          decodeNativeSemanticAtomWire) == Just atomB
                    && encodeNativeSemanticAtomWire atomA /= encodeNativeSemanticAtomWire atomB
                    && all (== Nothing) (map encodeNativeSemanticAtomWire unsupportedForms)
                    && all (== Nothing) (map decodeNativeSemanticAtomWire foreignWires)
                    && alteredA /= alteredB
                    && genericApplicationSemanticArguments alteredA /=
                       genericApplicationSemanticArguments alteredB
                    && encodeNativeGenericActualsKeyDomainWires alteredA ==
                       encodeNativeGenericActualsKeyDomainWires alteredB
                    && Map.keys (genericApplicationSemanticArguments alteredA) ==
                       Map.keys (genericApplicationSemanticArguments alteredB)
    _ -> False

-- | Actual checked generic actuals are read only after exact accepted
-- producer, independent manifest, source and release/StageClosure replay.
-- Test vectors below are deliberately UNACCEPTED semantic input data.
nativeGenericOrderedAtomVectorReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeGenericOrderedAtomVectorReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right _ ->
                  let application = genericDischargeApplicationIdentity
                        (genericApplicationAssuranceLineage
                          (nativeCorrespondenceSourceAssurance witness))
                      actuals = genericApplicationSemanticArguments application
                      atomA = SemanticAtom "audit.ordered.alpha"
                      atomB = SemanticAtom "audit.ordered.beta"
                      ordered = SemanticOrdered [atomA, atomB]
                      reversed = SemanticOrdered [atomB, atomA]
                      emptyOrdered = SemanticOrdered []
                      singleton = SemanticOrdered [atomA]
                      nested = SemanticOrdered [SemanticOrdered [atomA]]
                      mixed = SemanticOrdered
                        [atomA, SemanticUnordered (Set.singleton atomB)]
                      recordChild = SemanticOrdered
                        [SemanticRecord (Map.singleton "field" atomA)]
                      foreignWire = encodeNativeGenericStaticParameterKeyWire
                        (GenericStaticParameterKey "audit.ordered.alpha")
                      otherWire = encodeNativeGenericDeclarationWire
                        (DeclarationKey "audit.ordered.beta")
                      isAtom (SemanticAtom _) = True
                      isAtom _ = False
                      actualFormChecked form =
                        case form of
                          SemanticOrdered children
                            | all isAtom children ->
                                (encodeNativeSemanticOrderedAtomWires form >>=
                                  decodeNativeSemanticOrderedAtomWires) == Just form
                            | otherwise ->
                                encodeNativeSemanticOrderedAtomWires form == Nothing
                          _ -> encodeNativeSemanticOrderedAtomWires form == Nothing
                  in all actualFormChecked (Map.elems actuals)
                    && (encodeNativeSemanticOrderedAtomWires ordered >>=
                          decodeNativeSemanticOrderedAtomWires) == Just ordered
                    && (encodeNativeSemanticOrderedAtomWires reversed >>=
                          decodeNativeSemanticOrderedAtomWires) == Just reversed
                    && encodeNativeSemanticOrderedAtomWires ordered /=
                       encodeNativeSemanticOrderedAtomWires reversed
                    && encodeNativeSemanticOrderedAtomWires emptyOrdered == Just []
                    && decodeNativeSemanticOrderedAtomWires [] == Just emptyOrdered
                    && (encodeNativeSemanticOrderedAtomWires singleton >>=
                          decodeNativeSemanticOrderedAtomWires) == Just singleton
                    && all (== Nothing)
                      (map encodeNativeSemanticOrderedAtomWires
                        [nested, mixed, recordChild, atomA,
                         SemanticUnordered (Set.singleton atomA)])
                    && decodeNativeSemanticOrderedAtomWires [foreignWire] == Nothing
                    && decodeNativeSemanticOrderedAtomWires
                         [encodeNativeGenericStaticParameterKeyWire
                           (GenericStaticParameterKey "audit.ordered.alpha"),
                          encodeNativeSemanticAtomWireValue atomA] == Nothing
                    && decodeNativeSemanticOrderedAtomWires
                         [encodeNativeSemanticAtomWireValue atomA, otherWire] == Nothing
    _ -> False
  where
    -- The M-wire test inputs use a known native SemanticAtom constructor.
    -- This partial extractor has no fallback for non-atoms and cannot confer
    -- accepted producer authority on test data.
    encodeNativeSemanticAtomWireValue atom =
      case encodeNativeSemanticAtomWire atom of
        Just wire -> wire
        Nothing -> ""

-- | Synthetic Q/M maps are UNACCEPTED test data, not checked applications.
-- Actual accepted producer, independent manifest/source and exact release
-- consumers are rechecked before inspecting any generic semantic actuals.
nativeGenericAtomActualPairsReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeGenericAtomActualPairsReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                (nativeCorrespondenceCertifiedSource witness)
                (nativeCorrespondenceCertifiedRelease witness) of
                Left _ -> False
                Right _ ->
                  let application = genericDischargeApplicationIdentity
                        (genericApplicationAssuranceLineage
                          (nativeCorrespondenceSourceAssurance witness))
                      actuals = genericApplicationSemanticArguments application
                      keyA = GenericStaticParameterKey "audit.qm.alpha"
                      keyB = GenericStaticParameterKey "audit.qm.beta"
                      atomA = SemanticAtom "audit.qm.value.alpha"
                      atomB = SemanticAtom "audit.qm.value.beta"
                      atomMap = Map.fromList [(keyA, atomA), (keyB, atomB)]
                      swappedMap = Map.fromList [(keyA, atomB), (keyB, atomA)]
                      atomApp = application
                        { genericApplicationSemanticArguments = atomMap }
                      swappedApp = application
                        { genericApplicationSemanticArguments = swappedMap }
                      structuredApp = application
                        { genericApplicationSemanticArguments =
                            Map.singleton keyA (SemanticOrdered [atomA]) }
                      isAtom (SemanticAtom _) = True
                      isAtom _ = False
                      actualProjection =
                        case encodeNativeGenericAtomActualPairWires application of
                          Nothing -> any (not . isAtom) (Map.elems actuals)
                          Just pairs ->
                            decodeNativeGenericAtomActualPairWires pairs == Just actuals
                  in actualProjection
                    && encodeNativeGenericAtomActualPairWires structuredApp == Nothing
                    && encodeNativeGenericAtomActualPairWires
                         (application { genericApplicationSemanticArguments = Map.empty })
                         == Just []
                    && decodeNativeGenericAtomActualPairWires [] == Just Map.empty
                    && case (encodeNativeGenericAtomActualPairWires atomApp,
                             encodeNativeGenericAtomActualPairWires swappedApp) of
                        (Just pairs@[(qA, mA), (qB, mB)], Just swappedPairs) ->
                          decodeNativeGenericAtomActualPairWires pairs == Just atomMap
                          && decodeNativeGenericAtomActualPairWires swappedPairs
                               == Just swappedMap
                          && pairs /= swappedPairs
                          && decodeNativeGenericAtomActualPairWires
                               (reverse pairs) == Nothing
                          && decodeNativeGenericAtomActualPairWires
                               [(qA, mA), (qA, mA)] == Nothing
                          && decodeNativeGenericAtomActualPairWires
                               [(mA, qA), (qB, mB)] == Nothing
                          && decodeNativeGenericAtomActualPairWires
                               [(qA, qA), (qB, mB)] == Nothing
                          && decodeNativeGenericAtomActualPairWires
                               [(encodeNativeGenericDeclarationWire
                                   (DeclarationKey "audit.qm.alpha"), mA),
                                (qB, mB)] == Nothing
                        _ -> False
    _ -> False

-- | Adversarial same-manifest-ID projections. Neither modified manifest is an
-- accepted INT-002 artifact. Raw digest drift and lowering-root drift must
-- each fail *in their own domain*, before any attempt to identify native
-- manifest objects using just their manifestId or a stage revision.
nativeManifestStageReplayRejectsChangedDigests
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeManifestStageReplayRejectsChangedDigests source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let manifest = nativeCorrespondenceManifest witness
                  stage = nativeCorrespondenceStageClosure witness
                  rawChallenge = manifest
                    { manifestImplementationDigest = digestText "impl-audit-raw-digest-challenge" }
                  rootChallenge = manifest
                    { manifestLoweringLedgerRoot = digestText "impl-audit-lowering-root-challenge" }
              in manifestId rawChallenge == manifestId manifest
                && manifestId rootChallenge == manifestId manifest
                && manifestImplementationDigest rawChallenge
                    /= manifestImplementationDigest manifest
                && manifestLoweringLedgerRoot rootChallenge
                    /= manifestLoweringLedgerRoot manifest
                && case replayNativeManifestStageCoordinates witness rawChallenge stage of
                    Left (NativeReplayRawSystemsDifferent _ _) -> True
                    _ -> False
                && case replayNativeManifestStageCoordinates witness rootChallenge stage of
                    Left (NativeReplayLoweringRootDifferent _ _) -> True
                    _ -> False
    _ -> False

-- Full-object diagnostic replay over the exact independently accepted
-- producer/source/release retained by the native final witness. Unlike replay
-- of manifest and stage alone, this refuses a different accepted release with
-- identical manifest/stage/LLVM projections but different residual trust.
exactAcceptedConsumerReplayAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
exactAcceptedConsumerReplayAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              case replayNativeExactAcceptedConsumers witness
                (nativeCorrespondenceSourceManifestBinding witness)
                sourceArtifact release of
                Left _ -> False
                Right receipt ->
                  nativeExactReplayCheckedProducer receipt
                    == nativeCorrespondenceSourceManifestBinding witness
                    && nativeExactReplayCertifiedSource receipt == sourceArtifact
                    && nativeExactReplayCertifiedRelease receipt == release
                    && nativeReplayRawDigest (nativeExactReplayCoordinates receipt)
                      == NativeRawSystemsDigest (stageSystemsDigest (fixtureStage produced))
                    && nativeReplayLoweringRoot (nativeExactReplayCoordinates receipt)
                      == NativeLoweringRootDigest (stageLoweringRoot (fixtureStage produced))
    _ -> False

-- The declaration-only token has exactly the same accepted source assurance
-- and complete manifest projections; its missing checked descriptor prevents
-- substitution of the opaque producer, not merely of a digest or manifestId.
exactAcceptedConsumerReplayRejectsWeakProducer
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
exactAcceptedConsumerReplayRejectsWeakProducer source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (checked, produced)) ->
      case closeSourceManifestBinding source bundle policy
          (fixtureContext produced) (fixtureLedger produced)
          emptyProducerSelection of
        Left _ -> False
        Right weak ->
          case nativeAdapterPair source produced of
            Nothing -> False
            Just (sourceArtifact, release) ->
              case closeNativeFinalInstanceCorrespondence
                  source (sourceInstanceDescriptor source) bundle policy
                  (fixtureContext produced) (fixtureLedger produced)
                  emptyProducerSelection sourceArtifact release of
                Left _ -> False
                Right witness ->
                  weak /= checked
                    && sourceManifestBindingManifest weak
                      == sourceManifestBindingManifest checked
                    && sourceManifestBindingSourceAssurance weak
                      == sourceManifestBindingSourceAssurance checked
                    && case replayNativeExactAcceptedConsumers witness
                        weak sourceArtifact release of
                        Left NativeExactReplayProducerDifferent -> True
                        _ -> False
    _ -> False

-- Different independently accepted VER-010 source envelope with the same
-- reusable source assurance but a different concrete StageClosure must fail.
exactAcceptedConsumerReplayRejectsOtherSource
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
exactAcceptedConsumerReplayRejectsOtherSource source fixture other =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case (nativeAdapterPair source produced,
            certifyApplicationArtifact source (fixtureStage other)) of
        (Just (sourceArtifact, release), Right alternate) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              alternate /= sourceArtifact
                && certifiedApplicationSourceAssurance alternate
                  == certifiedApplicationSourceAssurance sourceArtifact
                && case replayNativeExactAcceptedConsumers witness
                    (nativeCorrespondenceSourceManifestBinding witness)
                    alternate release of
                    Left NativeExactReplaySourceDifferent -> True
                    _ -> False
        _ -> False
    _ -> False

-- Both releases are independently accepted and share the complete manifest,
-- concrete StageClosure and emitted LLVM. A changed residual-trust basis
-- changes which exact CertifiedRelease was selected; replay must reject it.
exactAcceptedConsumerReplayRejectsOtherReleaseTrust
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
exactAcceptedConsumerReplayRejectsOtherReleaseTrust source fixture =
  case (fixtureTrust fixture, producerInputs source, produceFixture source fixture) of
    (first : rest, Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, original) ->
          let changed = first
                { releaseTrustBasis =
                    releaseTrustBasis first <> " [different accepted trust basis]" }
          in case (runReleaseWith produced
                  (fixtureContext produced) (fixtureManifest produced)
                  (fixtureLLVM produced) (changed : rest),
                   closeNativeFinalInstanceCorrespondence
                    source (sourceInstanceDescriptor source) bundle policy
                    (fixtureContext produced) (fixtureLedger produced)
                    emptyProducerSelection sourceArtifact original) of
            (Right alternate, Right witness) ->
              alternate /= original
                && certifiedReleaseManifest alternate
                  == certifiedReleaseManifest original
                && certifiedReleaseStageClosure alternate
                  == certifiedReleaseStageClosure original
                && certifiedReleaseLLVMArtifact alternate
                  == certifiedReleaseLLVMArtifact original
                && certifiedReleaseTrustBoundaries alternate
                  /= certifiedReleaseTrustBoundaries original
                && case replayNativeExactAcceptedConsumers witness
                    (nativeCorrespondenceSourceManifestBinding witness)
                    sourceArtifact alternate of
                    Left NativeExactReplayReleaseDifferent -> True
                    _ -> False
            _ -> False
    _ -> False

-- This new consumer is deliberately *stronger* than the old caller-supplied
-- association: it runs the exact generic-actuals / architecture instance
-- producer again, and then compares both separately accepted consumer objects.
nativeFinalInstanceAccepts
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeFinalInstanceAccepts source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witnessed ->
              let authority = nativeCorrespondenceAuthority witnessed
                  stage = fixtureStage produced
                  subject = concreteSubjectStage (stageClosureConcrete stage)
                  common = subjectStageBase subject
              in nativeCorrespondenceArchitectureDescriptor witnessed
                    == sourceInstanceDescriptor source
                && nativeCorrespondenceArchitectureInstance witnessed
                    == deriveArchitectureInstanceIdentity (sourceInstanceDescriptor source)
                && nativeCorrespondenceSourceAssurance witnessed == source
                && nativeCorrespondenceManifest witnessed == fixtureManifest produced
                && nativeFinalSourceIdentity authority == nativeAdapterSourceId source
                && nativeFinalManifestId authority == manifestId (fixtureManifest produced)
                && nativeFinalRawSystemsDigest authority == stageSystemsDigest stage
                && nativeFinalLoweringRoot authority == stageLoweringRoot stage
                && nativeFinalSubjectRevision authority == subjectStageRevision subject
                && nativeFinalInstanceRevision authority == phase1StageInstanceRevision common
                && nativeFinalRealizationRevision authority == phase1StageRealizationRevision common
                && nativeFinalSystemsRevision authority == phase1StageSystemsArtifactRevision common
                && nativeFinalCommonContractRevision authority == phase1StageContractRevision common
                && nativeFinalClosedContractRevision authority == stageClosureContractRevision stage
                && nativeFinalVerifierProfile authority == phase1StageVerifierProfileRevision common
    _ -> False


-- | Check the *cross-boundary* retention that the source-manifest token and
-- the final opaque witness share the same entire independently checked
-- descriptor. Neither equality states that the occurrence produced StageClosure.
finalWitnessRetainsProducerDescriptor
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsProducerDescriptor source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (sourceBinding, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let exact = sourceInstanceDescriptor source
                  exported = nativeCorrespondenceArchitectureDescriptor witness
              in sourceManifestBindingArchitectureDescriptor sourceBinding == Just exact
                && exported == exact
                && nativeCorrespondenceArchitectureInstance witness
                   == deriveArchitectureInstanceIdentity exported
    _ -> False

-- | A second, different descriptor is not substituted after source acceptance.
-- It fails the producer on semantic-actual mismatch; the existing witness
-- still exports the unchanged original descriptor. No collision or stage
-- origin inference is made from the derived architecture identity.
finalWitnessDescriptorSubstitutionRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessDescriptorSubstitutionRejects source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          let exact = sourceInstanceDescriptor source
              wrong = exact
                { architectureStaticBindings =
                    Map.singleton "T" (SemanticAtom "substituted-at-final-export") }
              close descriptor = closeNativeFinalInstanceCorrespondence
                source descriptor bundle policy (fixtureContext produced)
                (fixtureLedger produced) emptyProducerSelection
                sourceArtifact release
          in case close exact of
            Left _ -> False
            Right witness ->
              nativeCorrespondenceArchitectureDescriptor witness == exact
                && wrong /= exact
                && case close wrong of
                    Left (NativeFinalInstanceSourceRejected
                      SourceManifestStaticArgumentsMismatch) -> True
                    _ -> False
    _ -> False

-- | Final consumers must retain the *whole* independently checked source
-- assurance from the opaque manifest producer, not just an equal application
-- identity or a stand-in source proof with unrelated checked-body evidence.
finalWitnessRetainsProducedSource
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsProducedSource source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (producedToken, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              nativeCorrespondenceSourceAssurance witness == source
                && nativeCorrespondenceSourceAssurance witness
                   == sourceManifestBindingSourceAssurance producedToken
    _ -> False

-- | The accepted final witness must retain the complete checked INT-002
-- manifest, not only its digest identity. The accepted CertifiedRelease
-- carries the identical whole manifest, and raw Systems digest and lowering
-- root retain their distinct meanings.
finalWitnessRetainsProducedManifest
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsProducedManifest source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (sourceToken, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let manifest = nativeCorrespondenceManifest witness
                  authority = nativeCorrespondenceAuthority witness
              in manifest == sourceManifestBindingManifest sourceToken
                && manifest == certifiedReleaseManifest release
                && manifest == fixtureManifest produced
                && manifestId manifest == nativeFinalManifestId authority
                && manifestImplementationDigest manifest
                    == nativeFinalRawSystemsDigest authority
                && manifestLoweringLedgerRoot manifest
                    == nativeFinalLoweringRoot authority
    _ -> False

-- | Retain the actual *complete* independently checked StageClosure object,
-- not just its Systems or closed-contract revision. The accepted source and
-- release artifacts are independently constructed and compared by the binder.
finalWitnessRetainsAcceptedStage
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsAcceptedStage source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let stage = nativeCorrespondenceStageClosure witness
                  authority = nativeCorrespondenceAuthority witness
              in stage == certifiedApplicationStageClosure sourceArtifact
                && stage == certifiedReleaseStageClosure release
                && stage == fixtureStage produced
                && stageClosureSystemsArtifactRevision stage
                    == nativeFinalSystemsRevision authority
                && stageClosureContractRevision stage
                    == nativeFinalClosedContractRevision authority
    _ -> False


-- | Complete independently accepted VER-010 source envelope is retained at
-- the *same* witness boundary as the complete independently accepted release.
-- The two StageClosure consumers must be exactly equal, while a source
-- assurance projection alone does not constitute an accepted source artifact.
finalWitnessRetainsAcceptedSource
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsAcceptedSource source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let accepted = nativeCorrespondenceCertifiedSource witness
              in accepted == sourceArtifact
                && certifiedApplicationSourceAssurance accepted
                    == nativeCorrespondenceSourceAssurance witness
                && certifiedApplicationStageClosure accepted
                    == nativeCorrespondenceStageClosure witness
                && certifiedApplicationStageClosure accepted
                    == certifiedReleaseStageClosure
                         (nativeCorrespondenceCertifiedRelease witness)

    _ -> False

-- | Two independently certified VER-010 artifacts can carry the same
-- accepted reusable source assurance and different complete StageClosures.
-- A changed stage must be rejected at the actual existing release consumer
-- gate even though the accepted source proof is unchanged. Unlike an identity
-- projection, the final witness retains exactly which source envelope passed.
sameSourceDifferentStageCannotReplaceSourceEnvelope
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
sameSourceDifferentStageCannotReplaceSourceEnvelope source fixture other =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case ( nativeAdapterPair source produced
           , certifyApplicationArtifact source (fixtureStage other) ) of
        (Just (original, release), Right alternative) ->
          let close artifact = closeNativeFinalInstanceCorrespondence
                source (sourceInstanceDescriptor source) bundle policy
                (fixtureContext produced) (fixtureLedger produced)
                emptyProducerSelection artifact release
          in case close original of
            Left _ -> False
            Right witness ->
              alternative /= original
                && certifiedApplicationSourceAssurance alternative
                    == certifiedApplicationSourceAssurance original
                && certifiedApplicationStageClosure alternative
                    /= certifiedApplicationStageClosure original
                && nativeCorrespondenceCertifiedSource witness == original
                && case close alternative of
                    Left (NativeFinalInstanceReleaseRejected
                      (SourceManifestNativeBindingRejected NativeFinalStageMismatch)) -> True
                    _ -> False
        _ -> False
    _ -> False

-- | The final exported opaque witness retains the *entire* accepted INT-005
-- release, not just its manifest, stage coordinates, or closed-stage digest.
-- The release may contain additional LLVM and residual-trust evidence.
finalWitnessRetainsAcceptedRelease
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessRetainsAcceptedRelease source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let exported = nativeCorrespondenceCertifiedRelease witness
              in exported == release
                && certifiedReleaseManifest exported
                    == nativeCorrespondenceManifest witness
                && certifiedReleaseStageClosure exported
                    == nativeCorrespondenceStageClosure witness
                && certifiedReleaseLLVMArtifact exported == fixtureLLVM produced
                && certifiedReleaseTrustBoundaries exported
                    == certifiedReleaseTrustBoundaries release
    _ -> False

-- | Two independently *accepted* INT-005 envelopes can have the exact same
-- manifest, stage, emitted LLVM and native authority coordinates, yet declare
-- different nonblank residual-trust bases. Both are valid under the existing
-- release verifier. The final witness must preserve WHICH accepted release was
-- passed to it. This is negative pressure against projection-only identity,
-- NOT an assertion that the original binder prohibits an alternate accepted
-- release or that the alternate declaration is true.
equalReleaseCoordinatesCanHideDifferentTrust
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
equalReleaseCoordinatesCanHideDifferentTrust source fixture =
  case (fixtureTrust fixture, producerInputs source, produceFixture source fixture) of
    (first : rest, Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, original) ->
          let replacement = first
                { releaseTrustBasis =
                    releaseTrustBasis first <> " [independent alternative basis]" }
              close release = closeNativeFinalInstanceCorrespondence
                source (sourceInstanceDescriptor source) bundle policy
                (fixtureContext produced) (fixtureLedger produced)
                emptyProducerSelection sourceArtifact release
          in case ( runReleaseWith produced
                      (fixtureContext produced) (fixtureManifest produced)
                      (fixtureLLVM produced) (replacement : rest)
                  , close original ) of
            (Right alternative, Right originalWitness) ->
              case close alternative of
                Left _ -> False
                Right alternativeWitness ->
                  alternative /= original
                    && certifiedReleaseManifest alternative
                        == certifiedReleaseManifest original
                    && certifiedReleaseStageClosure alternative
                        == certifiedReleaseStageClosure original
                    && certifiedReleaseLLVMArtifact alternative
                        == certifiedReleaseLLVMArtifact original
                    && certifiedReleaseTrustBoundaries alternative
                        /= certifiedReleaseTrustBoundaries original
                    && nativeCorrespondenceAuthority originalWitness
                        == nativeCorrespondenceAuthority alternativeWitness
                    && nativeCorrespondenceCertifiedRelease originalWitness
                        == original
                    && nativeCorrespondenceCertifiedRelease alternativeWitness
                        == alternative
                    && nativeCorrespondenceCertifiedRelease originalWitness
                        /= nativeCorrespondenceCertifiedRelease alternativeWitness
            _ -> False
    _ -> False

-- | Same *advertised closed revision* is insufficient to substitute an
-- altered concrete StageClosure. Independently supplied stale Systems identity
-- is rejected by both the real stage verifier and release-certification gate.
-- The original accepted witness continues to expose the unmodified stage.
finalWitnessStageRevisionOnlyRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessStageRevisionOnlyRejects source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let original = nativeCorrespondenceStageClosure witness
                  stale = SystemsArtifactRevision "nr-d06.final-witness-stale-systems"
                  substituted = original
                    { stageClosureSystemsArtifactRevision = stale }
              in substituted /= original
                && stageClosureContractRevision substituted
                    == stageClosureContractRevision original
                && original == certifiedReleaseStageClosure release
                && case (verifyStageClosureBundle substituted,
                    certifyReleaseArtifact
                      (fixtureProfile produced)
                      (fixtureContext produced)
                      (fixtureLedger produced)
                      (fixtureManifest produced)
                      substituted
                      (fixtureLLVM produced)
                      (fixtureTrust produced)) of
                  ( Left (StageClosureStoredSystemsRevisionMismatch _ observed1)
                    , Left (CertifiedReleaseStageClosureRejected
                        (StageClosureStoredSystemsRevisionMismatch _ observed2))) ->
                      observed1 == stale && observed2 == stale
                  _ -> False
    _ -> False

-- | A forged same-ID but different full manifest is not an accepted release:
-- independently verifying its bytes/fields fails before the opaque release
-- exists. A projected manifest ID cannot stand in for that accepted object.
-- This is negative pressure, not a proof of digest collision resistance.
finalWitnessManifestIdCollisionRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessManifestIdCollisionRejects source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (sourceToken, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          let manifest = sourceManifestBindingManifest sourceToken
              substituted = manifest
                { manifestCompilationProfile =
                    manifestCompilationProfile manifest <> ".substituted" }
          in manifestId manifest == manifestId substituted
            && manifest /= substituted
            && case runReleaseWith produced
                  (fixtureContext produced) substituted
                  (fixtureLLVM produced) (fixtureTrust produced) of
                Left (CertifiedReleaseManifestRejected _) ->
                  case closeNativeFinalInstanceCorrespondence
                      source (sourceInstanceDescriptor source) bundle policy
                      (fixtureContext produced) (fixtureLedger produced)
                      emptyProducerSelection sourceArtifact release of
                    Right witness -> nativeCorrespondenceManifest witness == manifest
                    Left _ -> False
                _ -> False
    _ -> False

-- | Identity-colliding but independently checked source evidence must not
-- replace the original accepted final witness's exported assurance. The
-- substituted source is rejected by the exact certified-source gate.
finalWitnessSourceProofSubstitutionRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
finalWitnessSourceProofSubstitutionRejects source fixture =
  let alternativeEvidence = ArtifactIdentity
        (ArtifactRef "nr-d06.final-witness-substituted-source-proof")
        (digestText "nr-d06.final-witness-distinct-checked-body-evidence")
  in case ( nativeAdapterSourceAssuranceWithEvidence alternativeEvidence
          , producerInputs source
          , produceFixture source fixture ) of
    (Right alternative, Right (bundle, policy), Right (producedToken, produced))
      | alternative /= source
        && nativeAdapterSourceId alternative == nativeAdapterSourceId source ->
          case nativeAdapterPair source produced of
            Nothing -> False
            Just (sourceArtifact, release) ->
              let close withSource = closeNativeFinalInstanceCorrespondence
                    withSource (sourceInstanceDescriptor source) bundle policy
                    (fixtureContext produced) (fixtureLedger produced)
                    emptyProducerSelection sourceArtifact release
              in case close source of
                Left _ -> False
                Right witness ->
                  nativeCorrespondenceSourceAssurance witness == source
                    && nativeCorrespondenceSourceAssurance witness
                       == sourceManifestBindingSourceAssurance producedToken
                    && case close alternative of
                        Left NativeFinalInstanceSourceAssuranceMismatch -> True
                        _ -> False
    _ -> False

-- The exported low-level manifest/release binder cannot be used to substitute
-- a different checked source proof while retaining the same application ID.
producedBindingDifferentAcceptedSourceRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
producedBindingDifferentAcceptedSourceRejects source fixture =
  let alternativeEvidence = ArtifactIdentity
        (ArtifactRef "nr-d06.binding-second-source-proof")
        (digestText "nr-d06.binding-distinct-checked-body-evidence")
  in case ( nativeAdapterSourceAssuranceWithEvidence alternativeEvidence
          , produceFixture source fixture ) of
    (Right alternative, Right (binding, produced))
      | alternative /= source
          && nativeAdapterSourceId alternative == nativeAdapterSourceId source ->
          case ( certifyApplicationArtifact alternative (fixtureStage produced)
               , runRelease produced ) of
            (Right independentArtifact, Right release) ->
              case bindProducedFinalAuthority binding independentArtifact release of
                Left SourceManifestSourceAssuranceMismatch -> True
                _ -> False
            _ -> False
    _ -> False

-- A second *independently constructed* source assurance has the same exact
-- application identity but different checked body evidence. The final
-- source/manifest producer must use the same accepted assurance object as the
-- independently certified application artifact, not merely the same ID.
nativeFinalInstanceDifferentAcceptedSourceRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeFinalInstanceDifferentAcceptedSourceRejects source fixture =
  let alternativeEvidence = ArtifactIdentity
        (ArtifactRef "nr-d06.independent-second-source-proof")
        (digestText "nr-d06.distinct-content-checked-source-evidence")
  in case ( nativeAdapterSourceAssuranceWithEvidence alternativeEvidence
          , producerInputs source
          , produceFixture source fixture ) of
    (Right alternative, Right (bundle, policy), Right (_, produced))
      | alternative /= source
          && nativeAdapterSourceId alternative == nativeAdapterSourceId source ->
          case ( certifyApplicationArtifact alternative (fixtureStage produced)
               , runRelease produced ) of
            (Right independentArtifact, Right release) ->
              case closeNativeFinalInstanceCorrespondence source
                  (sourceInstanceDescriptor source) bundle policy
                  (fixtureContext produced) (fixtureLedger produced)
                  emptyProducerSelection independentArtifact release of
                Left NativeFinalInstanceSourceAssuranceMismatch -> True
                _ -> False
            _ -> False
    _ -> False

nativeFinalInstanceWrongActualRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeFinalInstanceWrongActualRejects source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          let bad = (sourceInstanceDescriptor source)
                { architectureStaticBindings =
                    Map.singleton "T" (SemanticAtom "substituted") }
          in case closeNativeFinalInstanceCorrespondence source bad bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
               Left (NativeFinalInstanceSourceRejected
                 SourceManifestStaticArgumentsMismatch) -> True
               _ -> False
    _ -> False

nativeFinalInstanceOtherReleaseRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
nativeFinalInstanceOtherReleaseRejects source fixture other =
  case (producerInputs source, produceFixture source fixture, runRelease other) of
    (Right (bundle, policy), Right (_, produced), Right otherRelease) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, _) ->
          case closeNativeFinalInstanceCorrespondence source
              (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact otherRelease of
            Left (NativeFinalInstanceReleaseRejected
              SourceManifestReleaseManifestMismatch) -> True
            _ -> False
    _ -> False

nativeFinalInstanceWrongStageRejects
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
nativeFinalInstanceWrongStageRejects source fixture other =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case (certifyApplicationArtifact source (fixtureStage other), runRelease produced) of
        (Right wrongSourceArtifact, Right release) ->
          case closeNativeFinalInstanceCorrespondence source
              (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection wrongSourceArtifact release of
            Left (NativeFinalInstanceReleaseRejected
              (SourceManifestNativeBindingRejected NativeFinalStageMismatch)) -> True
            _ -> False
        _ -> False
    _ -> False

-- The NR-D06 source occurrence is independently accepted, but it is not the
-- occurrence that generated either Upload or Steve. The earlier native witness
-- must remain usable for its *bounded* manifest/stage equalities; the stronger
-- revision gate must expose the missing origin connection, not bless it.
nativeStageRevisionGateRejectsUnrelated
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
nativeStageRevisionGateRejectsUnrelated source fixture =
  case (producerInputs source, produceFixture source fixture) of
    (Right (bundle, policy), Right (_, produced)) ->
      case nativeAdapterPair source produced of
        Nothing -> False
        Just (sourceArtifact, release) ->
          case closeNativeFinalInstanceCorrespondence
              source (sourceInstanceDescriptor source) bundle policy
              (fixtureContext produced) (fixtureLedger produced)
              emptyProducerSelection sourceArtifact release of
            Left _ -> False
            Right witness ->
              let occurrence = nativeCorrespondenceArchitectureInstance witness
                  expected = identityInstanceRevision occurrence
                  actual = nativeFinalInstanceRevision
                    (nativeCorrespondenceAuthority witness)
              in expected /= actual
                && case checkNativeStageRevisionEquality witness of
                    Left (NativeStageRevisionDifferent expected' actual') ->
                      expected' == expected && actual' == actual
                    _ -> False
    _ -> False

-- An explicitly constructed *counterexample*, not a certified occurrence:
-- revision equality cannot recover the key that StageClosure never stored.
sameInstanceRevisionDifferentOccurrenceKey
  :: GenericApplicationAssurance -> Bool
sameInstanceRevisionDifferentOccurrenceKey source =
  let original = deriveArchitectureInstanceIdentity (sourceInstanceDescriptor source)
      other = original
        { identityInstanceKey = InstanceKey "audit.different.occurrence" }
  in original /= other
    && identityInstanceRevision original == identityInstanceRevision other

instanceRejectsWrongStaticArgument
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
instanceRejectsWrongStaticArgument source fixture =
  case producerInputs source of
    Left _ -> False
    Right (bundle, policy) ->
      let descriptor = (sourceInstanceDescriptor source)
            { architectureStaticBindings = Map.singleton "T" (SemanticAtom "Other") }
          context = (fixtureContext fixture)
            { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle }
      in case closeSourceManifestBindingForInstance source descriptor bundle policy
           context (fixtureLedger fixture) emptyProducerSelection of
        Left SourceManifestStaticArgumentsMismatch -> True
        _ -> False

instanceRejectsMissingStaticArgument
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
instanceRejectsMissingStaticArgument source fixture =
  case producerInputs source of
    Left _ -> False
    Right (bundle, policy) ->
      let descriptor = (sourceInstanceDescriptor source)
            { architectureStaticBindings = Map.empty }
          context = (fixtureContext fixture)
            { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle }
      in case closeSourceManifestBindingForInstance source descriptor bundle policy
           context (fixtureLedger fixture) emptyProducerSelection of
        Left SourceManifestStaticArgumentsMismatch -> True
        _ -> False

instanceRejectsUnregisteredIdentity
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
instanceRejectsUnregisteredIdentity source fixture =
  case producerInputs source of
    Left _ -> False
    Right (bundle, policy) ->
      let descriptor = (sourceInstanceDescriptor source)
            { architectureInstanceKey = InstanceKey "audit.unregistered.instance" }
          context = (fixtureContext fixture)
            { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle }
      in case closeSourceManifestBindingForInstance source descriptor bundle policy
           context (fixtureLedger fixture) emptyProducerSelection of
        Left SourceManifestInstanceNotInVerificationBundle -> True
        _ -> False

instanceRejectsWrongDeclaration
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
instanceRejectsWrongDeclaration source fixture =
  case producerInputs source of
    Left _ -> False
    Right (bundle, policy) ->
      let descriptor = (sourceInstanceDescriptor source)
            { architectureDeclarationIdentity = (architectureDeclarationIdentity
                (sourceInstanceDescriptor source))
                { identityDefinitionRevision = DefinitionRevision "audit.wrong.definition" } }
          context = (fixtureContext fixture)
            { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle }
      in case closeSourceManifestBindingForInstance source descriptor bundle policy
           context (fixtureLedger fixture) emptyProducerSelection of
        Left (SourceManifestInstanceDeclarationMismatch _ _) -> True
        _ -> False

producerRejectsUnlistedDeclaration
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
producerRejectsUnlistedDeclaration source fixture =
  case producerInputs source of
    Left _ -> False
    Right (bundle, policy) ->
      let wrong = bundle { verificationBundleDeclarations = Set.empty }
          context = (fixtureContext fixture)
            { verificationArchitectureDigest =
                verificationBundleArchitectureDigest wrong }
      in case closeSourceManifestBinding source wrong policy context
           (fixtureLedger fixture) emptyProducerSelection of
          Left (SourceManifestDeclarationNotInVerificationBundle _) -> True
          _ -> False

producerRejectsWrongArchitecture
  :: GenericApplicationAssurance -> ReleaseFixture -> Bool
producerRejectsWrongArchitecture source fixture =
  case producerInputs source of
    Left _ -> False
    Right (bundle, policy) ->
      case closeSourceManifestBinding source bundle policy
           (fixtureContext fixture) (fixtureLedger fixture)
           emptyProducerSelection of
        Left (SourceManifestClosureRejected _) -> True
        _ -> False

producedBindingRejectsOtherRelease
  :: GenericApplicationAssurance -> ReleaseFixture -> ReleaseFixture -> Bool
producedBindingRejectsOtherRelease source fixture other =
  case (produceFixture source fixture, produceFixture source other) of
    (Right (binding, leftFixture), Right (_, rightFixture)) ->
      case (nativeAdapterPair source leftFixture, runRelease rightFixture) of
        (Just (sourceArtifact, _), Right rightRelease) ->
          manifestId (fixtureManifest leftFixture)
            /= manifestId (fixtureManifest rightFixture)
          && case bindProducedFinalAuthority binding sourceArtifact rightRelease of
               Left SourceManifestReleaseManifestMismatch -> True
               _ -> False
        _ -> False
    _ -> False

data ReleaseFixture = ReleaseFixture
  { fixtureProfile :: CertifiedReleaseProfile
  , fixtureContext :: VerificationContext
  , fixtureLedger :: AssuranceLedger
  , fixtureManifest :: AssuranceManifest
  , fixtureStage :: StageClosureBundle
  , fixtureLLVM :: LLVMArtifact
  , fixtureTrust :: [ReleaseTrustBoundary]
  }

releaseFixture :: Text -> StageClosureBundle -> ReleaseFixture
releaseFixture witness stage = ReleaseFixture
  { fixtureProfile = releaseProfile
  , fixtureContext = context
  , fixtureLedger = ledger
  , fixtureManifest = manifest
  , fixtureStage = stage
  , fixtureLLVM = llvm
  , fixtureTrust = conventionalTrust
  }
  where
    ledger = emptyLedger
    systems = stageSystemsArtifact stage
    systemsDigest = systemsArtifactDigest systems
    root = loweringLedgerRoot (systemsArtifactLoweringLedger systems)
    targetName = "phase1-conventional-x86_64-linux"
    compilationProfile = "phase1/int005/certified-release-envelope-v1"
    architectureDigest = digestText ("int005.architecture." <> witness)
    coreDigest = digestText ("int005.core." <> witness)
    context = emptyVerificationContext
      { verificationArchitectureDigest = architectureDigest
      , verificationPhilCoreDigest = coreDigest
      , verificationImplementationDigest = systemsDigest
      , verificationTarget = targetName
      , verificationCompilationProfile = compilationProfile
      , verificationLoweringLedgerRoot = root
      }
    provisional = emptyManifest
      { manifestArchitectureDigest = architectureDigest
      , manifestPhilCoreDigest = coreDigest
      , manifestImplementationDigest = systemsDigest
      , manifestTarget = targetName
      , manifestCompilationProfile = compilationProfile
      , manifestLoweringLedgerRoot = root
      }
    manifest = provisional
      { manifestId = deriveManifestId ledger provisional }
    llvm = lowerSystemsConservative phase0LLVMTarget systems
    releaseProfile = CertifiedReleaseProfile
      { releaseProfileRevision =
          ReleaseProfileRevision "phase1.int005.conventional-x86_64-linux.v1"
      , releaseProfileManifestTarget = targetName
      , releaseProfileManifestCompilationProfile = compilationProfile
      , releaseProfileLLVMTarget = phase0LLVMTarget
      , releaseProfileRequiredTrustKinds = Set.fromList
          [ CompilerCheckerTrust
          , LLVMToolchainTrust
          , RuntimeTrust
          , ProviderTrust
          , ExternalCheckerTrust
          , TargetAssumptionTrust
          ]
      }

runRelease :: ReleaseFixture -> Either CertifiedReleaseError CertifiedReleaseArtifact
runRelease fixture = runReleaseWith fixture
  (fixtureContext fixture)
  (fixtureManifest fixture)
  (fixtureLLVM fixture)
  (fixtureTrust fixture)

runReleaseWith
  :: ReleaseFixture
  -> VerificationContext
  -> AssuranceManifest
  -> LLVMArtifact
  -> [ReleaseTrustBoundary]
  -> Either CertifiedReleaseError CertifiedReleaseArtifact
runReleaseWith fixture context manifest artifact trust = certifyReleaseArtifact
  (fixtureProfile fixture)
  context
  (fixtureLedger fixture)
  manifest
  (fixtureStage fixture)
  artifact
  trust

stageSystemsArtifact :: StageClosureBundle -> SystemsArtifact
stageSystemsArtifact stage =
  phase1StageSystemsArtifact
    . subjectStageBase
    . concreteSubjectStage
    . stageClosureConcrete
    $ stage

stageSystemsDigest :: StageClosureBundle -> Digest
stageSystemsDigest = systemsArtifactDigest . stageSystemsArtifact

stageLoweringRoot :: StageClosureBundle -> Digest
stageLoweringRoot =
  loweringLedgerRoot . systemsArtifactLoweringLedger . stageSystemsArtifact

conventionalTrust :: [ReleaseTrustBoundary]
conventionalTrust =
  [ trust "compiler-checker" CompilerCheckerTrust
      "Phil Haskell compiler/checker" "phase1-current"
      "first implementation remains trusted until Phase 2"
  , trust "llvm-toolchain" LLVMToolchainTrust
      "LLVM assembler/linker and clang" "LLVM 18.x"
      "conventional native emission and link toolchain"
  , trust "runtime" RuntimeTrust
      "Phil conventional host runtime" "phase1-runtime-v1"
      "runtime behavior below checked Phil/Systems contracts"
  , trust "providers" ProviderTrust
      "qualified conventional providers" "phase1-provider-set-v1"
      "provider implementations remain trusted at their declared qualification boundaries"
  , trust "external-checkers" ExternalCheckerTrust
      "external proof/certificate checkers" "phase1-certified-checker-set-v1"
      "accepted external evidence depends on the named competent checkers"
  , trust "target-assumptions" TargetAssumptionTrust
      "x86_64 Linux target assumptions" "phase1-x86_64-linux-v1"
      "selected conventional ABI/tool/runtime assumptions"
  ]
  where
    trust ident kind name revision basis = ReleaseTrustBoundary
      { releaseTrustBoundaryId = ReleaseTrustBoundaryId ident
      , releaseTrustKind = kind
      , releaseTrustName = name
      , releaseTrustRevision = revision
      , releaseTrustBasis = basis
      }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft convert = either (Left . convert) Right
