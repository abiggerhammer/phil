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
  , SemanticForm (..)
  , deriveArchitectureInstanceIdentity
  , DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  )
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
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
  , Digest
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
