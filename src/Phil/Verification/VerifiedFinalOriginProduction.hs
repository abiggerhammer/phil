-- | P7: the final accepted-origin route.  Structural VER-010/INT-005 and
-- legacy NativeFinalAuthority values cannot mint this opaque result.
-- No Rocq proof inhabitant or LLVM toolchain correctness is claimed.
module Phil.Verification.VerifiedFinalOriginProduction
  ( VerifiedFinalOriginProduction
  , AcceptedVerifiedFinalOrigin
  , VerifiedFinalOriginError (..)
  , produceVerifiedFinalOrigin
  , acceptVerifiedFinalOrigin
  , verifiedFinalOriginStageProduction
  , verifiedFinalOriginSourceBinding
  , verifiedFinalOriginSourceArtifact
  , verifiedFinalOriginRelease
  , acceptedVerifiedFinalOriginAuthority
  , acceptedVerifiedFinalOriginProduction
  ) where

import Phil.Assurance.Types (AssuranceLedger, VerificationContext)
import qualified Phil.Compiler.SourceSystems as Source
import Phil.LLVM.IR (LLVMArtifact)
import qualified Phil.Verification.ArtifactClosure as Artifact
import qualified Phil.Verification.CertifiedRelease as Release
import qualified Phil.Verification.FinalAuthorityAdapter as Native
import qualified Phil.Verification.SourceManifestBinding as Binding
import qualified Phil.Verification.VerifiedStageClosureProduction as Stage

-- | A sealed source -> whole-stage -> complete manifest -> independently
-- accepted whole release production event. The release is constructed HERE,
-- not supplied as a post-hoc claim to have originated from the source.
data VerifiedFinalOriginProduction = VerifiedFinalOriginProduction
  Stage.VerifiedStageClosureProduction
  Binding.CertifiedSourceManifestBinding
  Artifact.CertifiedApplicationArtifact
  Release.CertifiedReleaseArtifact
  Native.NativeFinalAuthority
  deriving (Eq, Show)

-- | The stronger final-origin consumer result is only minted on exact
-- whole-object replay against a previously sealed production event.
-- Existing structural projection APIs return neither this type nor a
-- capability to create it.
newtype AcceptedVerifiedFinalOrigin =
  AcceptedVerifiedFinalOrigin VerifiedFinalOriginProduction
  deriving (Eq, Show)

data VerifiedFinalOriginError
  = VerifiedFinalOriginMissingCheckedInstance
  | VerifiedFinalOriginSourceOccurrenceMismatch
  | VerifiedFinalOriginArtifactRejected Artifact.ArtifactCertificationError
  | VerifiedFinalOriginReleaseRejected Release.CertifiedReleaseError
  | VerifiedFinalOriginStructuralRejected Binding.SourceManifestBindingError
  | VerifiedFinalOriginSourceBindingSubstituted
  | VerifiedFinalOriginCertifiedSourceSubstituted
  | VerifiedFinalOriginCertifiedReleaseSubstituted
  | VerifiedFinalOriginStructuralReplayRejected Binding.SourceManifestBindingError
  deriving (Eq, Show)

-- | The P2 event is constructed by rechecking ordinary source and Core before
-- Systems lowering; P6 rebuilds BOTH closure arms from that event. Here the
-- exact complete checked architecture descriptor, including K/I and actuals,
-- MUST equal the one independently accepted by the source-manifest producer.
-- The sealed producer alone selects the StageClosure, and the independently
-- accepted release is minted with that same stage and manifest. LLVM/TCB
-- validation is exactly the existing INT-005 policy, not a new trusted axiom.
produceVerifiedFinalOrigin
  :: Stage.VerifiedStageClosureProduction
  -> Binding.CertifiedSourceManifestBinding
  -> VerificationContext
  -> AssuranceLedger
  -> Release.CertifiedReleaseProfile
  -> LLVMArtifact
  -> [Release.ReleaseTrustBoundary]
  -> Either VerifiedFinalOriginError VerifiedFinalOriginProduction
produceVerifiedFinalOrigin stageProduction binding context ledger profile llvm trust = do
  let sourceProduction = Stage.verifiedStageClosureSourceProduction stageProduction
      actualDescriptor = Source.verifiedSourceSystemsArchitectureDescriptor sourceProduction
      expectedDescriptor = Binding.sourceManifestBindingArchitectureDescriptor binding
  case expectedDescriptor of
    Nothing -> Left VerifiedFinalOriginMissingCheckedInstance
    Just descriptor ->
      if descriptor == actualDescriptor
        then Right ()
        else Left VerifiedFinalOriginSourceOccurrenceMismatch
  let source = Binding.sourceManifestBindingSourceAssurance binding
      manifest = Binding.sourceManifestBindingManifest binding
      selected = Stage.verifiedStageClosureSelected stageProduction
  sourceArtifact <- mapLeft VerifiedFinalOriginArtifactRejected
    (Artifact.certifyApplicationArtifact source selected)
  release <- mapLeft VerifiedFinalOriginReleaseRejected
    (Release.certifyReleaseArtifact
      profile context ledger manifest selected llvm trust)
  authority <- mapLeft VerifiedFinalOriginStructuralRejected
    (Binding.bindProducedFinalAuthority binding sourceArtifact release)
  pure (VerifiedFinalOriginProduction
    stageProduction binding sourceArtifact release authority)

-- | Mandatory accepting consumer for the *stronger* final-origin type. No
-- caller can substitute an independently accepted source, manifest, stage,
-- release, LLVM payload or trust map merely because its revisions agree.
-- The complete release envelope is compared before structural rechecking.
acceptVerifiedFinalOrigin
  :: VerifiedFinalOriginProduction
  -> Binding.CertifiedSourceManifestBinding
  -> Artifact.CertifiedApplicationArtifact
  -> Release.CertifiedReleaseArtifact
  -> Either VerifiedFinalOriginError AcceptedVerifiedFinalOrigin
acceptVerifiedFinalOrigin production@(VerifiedFinalOriginProduction _ binding source release _) candidateBinding candidateSource candidateRelease = do
  if binding == candidateBinding
    then Right ()
    else Left VerifiedFinalOriginSourceBindingSubstituted
  if source == candidateSource
    then Right ()
    else Left VerifiedFinalOriginCertifiedSourceSubstituted
  if release == candidateRelease
    then Right ()
    else Left VerifiedFinalOriginCertifiedReleaseSubstituted
  _ <- mapLeft VerifiedFinalOriginStructuralReplayRejected
    (Binding.bindProducedFinalAuthority candidateBinding candidateSource candidateRelease)
  pure (AcceptedVerifiedFinalOrigin production)

verifiedFinalOriginStageProduction
  :: VerifiedFinalOriginProduction -> Stage.VerifiedStageClosureProduction
verifiedFinalOriginStageProduction (VerifiedFinalOriginProduction stage _ _ _ _) = stage

verifiedFinalOriginSourceBinding
  :: VerifiedFinalOriginProduction -> Binding.CertifiedSourceManifestBinding
verifiedFinalOriginSourceBinding (VerifiedFinalOriginProduction _ binding _ _ _) = binding

verifiedFinalOriginSourceArtifact
  :: VerifiedFinalOriginProduction -> Artifact.CertifiedApplicationArtifact
verifiedFinalOriginSourceArtifact (VerifiedFinalOriginProduction _ _ source _ _) = source

verifiedFinalOriginRelease
  :: VerifiedFinalOriginProduction -> Release.CertifiedReleaseArtifact
verifiedFinalOriginRelease (VerifiedFinalOriginProduction _ _ _ release _) = release

acceptedVerifiedFinalOriginAuthority
  :: AcceptedVerifiedFinalOrigin -> Native.NativeFinalAuthority
acceptedVerifiedFinalOriginAuthority
  (AcceptedVerifiedFinalOrigin (VerifiedFinalOriginProduction _ _ _ _ authority)) = authority

acceptedVerifiedFinalOriginProduction
  :: AcceptedVerifiedFinalOrigin -> VerifiedFinalOriginProduction
acceptedVerifiedFinalOriginProduction (AcceptedVerifiedFinalOrigin production) = production

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
