{-# LANGUAGE OverloadedStrings #-}

-- | A narrow, native, producer-to-consumer final-authority witness.  No Rocq
-- nat encoding or claim of FinalArtifactCertified is exported here.
module Phil.Verification.NativeFinalInstanceCorrespondence
  ( NativeFinalInstanceCorrespondence
  , nativeCorrespondenceArchitectureInstance
  , nativeCorrespondenceArchitectureDescriptor
  , nativeCorrespondenceSourceAssurance
  , nativeCorrespondenceSourceManifestBinding
  , nativeCorrespondenceManifest
  , nativeCorrespondenceStageClosure
  , nativeCorrespondenceCertifiedSource
  , nativeCorrespondenceCertifiedRelease
  , nativeCorrespondenceAuthority
  , NativeRawSystemsDigest (..)
  , NativeLoweringRootDigest (..)
  , encodeNativeRawSystemsDigestWire
  , decodeNativeRawSystemsDigestWire
  , encodeNativeLoweringRootWire
  , decodeNativeLoweringRootWire
  , encodeNativeSystemsRevisionWire
  , decodeNativeSystemsRevisionWire
  , encodeNativeCommonContractRevisionWire
  , decodeNativeCommonContractRevisionWire
  , encodeNativeClosedContractRevisionWire
  , decodeNativeClosedContractRevisionWire
  , encodeNativeSubjectRevisionWire
  , decodeNativeSubjectRevisionWire
  , encodeNativeInstanceRevisionWire
  , decodeNativeInstanceRevisionWire
  , encodeNativeRealizationRevisionWire
  , decodeNativeRealizationRevisionWire
  , encodeNativeOccurrenceKeyWire
  , decodeNativeOccurrenceKeyWire
  , encodeNativeCheckedOccurrenceIdentityWires
  , decodeNativeCheckedOccurrenceIdentityWires
  , encodeNativeGenericDeclarationWire
  , decodeNativeGenericDeclarationWire
  , encodeNativeGenericInterfaceWire
  , decodeNativeGenericInterfaceWire
  , encodeNativeGenericApplicationScalarWires
  , decodeNativeGenericApplicationScalarWires
  , encodeNativeGenericStaticParameterKeyWire
  , decodeNativeGenericStaticParameterKeyWire
  , encodeNativeGenericActualsKeyDomainWires
  , decodeNativeGenericActualsKeyDomainWires
  , encodeNativeSemanticAtomWire
  , decodeNativeSemanticAtomWire
  , encodeNativeSemanticOrderedAtomWires
  , decodeNativeSemanticOrderedAtomWires
  , encodeNativeSemanticUnorderedAtomWires
  , decodeNativeSemanticUnorderedAtomWires
  , NativeSemanticRecordFieldText (..)
  , encodeNativeSemanticRecordFieldWire
  , decodeNativeSemanticRecordFieldWire
  , encodeNativeSemanticRecordAtomFieldWires
  , decodeNativeSemanticRecordAtomFieldWires
  , encodeNativeGenericAtomActualPairWires
  , decodeNativeGenericAtomActualPairWires
  , encodeNativeGenericAtomApplicationWires
  , decodeNativeGenericAtomApplicationWires
  , NativeAtomManifestWireCandidate (..)
  , NativeAtomManifestReplay
  , nativeAtomManifestReplayApplication
  , nativeAtomManifestReplayRawDigest
  , nativeAtomManifestReplayLoweringRoot
  , nativeAtomManifestReplayStageCoordinates
  , nativeAtomManifestReplayCheckedOccurrence
  , NativeAtomManifestReplayError (..)
  , replayNativeAtomManifestCandidate
  , NativeAtomManifestSystemsWireCandidate (..)
  , NativeAtomManifestSystemsReplay
  , nativeAtomManifestSystemsReplayBase
  , nativeAtomManifestSystemsReplayRevision
  , NativeAtomManifestSystemsReplayError (..)
  , replayNativeAtomManifestSystemsCandidate
  , NativeAtomManifestCommonWireCandidate (..)
  , NativeAtomManifestCommonReplay
  , nativeAtomManifestCommonReplayBase
  , nativeAtomManifestCommonReplayRevision
  , NativeAtomManifestCommonReplayError (..)
  , replayNativeAtomManifestCommonCandidate
  , NativeAtomManifestClosedWireCandidate (..)
  , NativeAtomManifestClosedReplay
  , nativeAtomManifestClosedReplayBase
  , nativeAtomManifestClosedReplayRevision
  , NativeAtomManifestClosedReplayError (..)
  , replayNativeAtomManifestClosedCandidate
  , NativeAtomManifestSubjectWireCandidate (..)
  , NativeAtomManifestSubjectReplay
  , nativeAtomManifestSubjectReplayBase
  , nativeAtomManifestSubjectReplayRevision
  , NativeAtomManifestSubjectReplayError (..)
  , replayNativeAtomManifestSubjectCandidate
  , NativeVerifierProfileText (..)
  , encodeNativeVerifierProfileWire
  , decodeNativeVerifierProfileWire
  , NativeManifestStageReplay
  , nativeReplayRawDigest
  , nativeReplayLoweringRoot
  , nativeReplaySubjectRevision
  , nativeReplayInstanceRevision
  , nativeReplayRealizationRevision
  , nativeReplaySystemsRevision
  , nativeReplayCommonRevision
  , nativeReplayClosedRevision
  , nativeReplayVerifierProfile
  , NativeManifestStageReplayError (..)
  , replayNativeManifestStageCoordinates
  , NativeExactAcceptedConsumerReplay
  , nativeExactReplayCheckedProducer
  , nativeExactReplayCertifiedSource
  , nativeExactReplayCertifiedRelease
  , nativeExactReplayCoordinates
  , NativeExactAcceptedConsumerReplayError (..)
  , replayNativeExactAcceptedConsumers
  , NativeStageRevisionEquality
  , nativeStageRevisionEqualityOccurrence
  , nativeStageRevisionEqualityStageRevision
  , NativeStageRevisionEqualityError (..)
  , checkNativeStageRevisionEquality
  , NativeFinalInstanceCorrespondenceError (..)
  , closeNativeFinalInstanceCorrespondence
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Generic
  ( GenericApplicationIdentity (..), GenericStaticParameterKey (..)
  , GenericDischargeLineage (..)
  )
import Phil.Assurance.Types
  ( AssuranceLedger, AssuranceManifest (..), Digest (..), VerificationContext )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor
  , DeclarationKey (..)
  , InterfaceRevision (..)
  , ArchitectureInstanceIdentity (..)
  , InstanceRevision (..)
  , InstanceKey (..)
  , RealizationRevision (..)
  , SemanticForm (..)
  , deriveArchitectureInstanceIdentity
  )
import Phil.Verification (ApplicationAssurancePolicy)
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  , certifiedApplicationSourceAssurance
  , certifiedApplicationStageClosure
  )
import Phil.Verification.Bundle (VerificationBundle)
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , certifiedReleaseManifest
  , certifiedReleaseStageClosure
  )
import Phil.Systems.IR
  ( loweringLedgerRoot, systemsArtifactDigest, systemsArtifactLoweringLedger )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..), SystemsArtifactRevision (..), Phase1StageContractRevision (..) )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..), ClosedStageContractRevision (..), concreteSubjectStage )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..), SubjectStageRevision (..) )
import Phil.Verification.FinalAuthorityAdapter
  ( NativeFinalAuthority
  , nativeFinalInstanceRevision
  , nativeFinalRawSystemsDigest
  , nativeFinalLoweringRoot
  , nativeFinalManifestId
  , nativeFinalSubjectRevision
  , nativeFinalRealizationRevision
  , nativeFinalSystemsRevision
  , nativeFinalCommonContractRevision
  , nativeFinalClosedContractRevision
  , nativeFinalVerifierProfile
  )
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance, genericApplicationAssuranceLineage )
import Phil.Verification.ManifestClosure (ManifestClosureSelection)
import Phil.Verification.SourceManifestBinding
  ( CertifiedSourceManifestBinding
  , SourceManifestBindingError
  , bindProducedFinalAuthority
  , closeSourceManifestBindingForInstance
  , sourceManifestBindingSourceAssurance
  , sourceManifestBindingManifest
  )

-- | Preserve the *whole* canonical architecture descriptor validated by
-- the checked actuals/instance/bundle producer, not just its identity. The
-- identity projection is derived from this retained descriptor. The concrete
-- StageClosure InstanceRevision remains a separate domain and does NOT
-- authenticate occurrence-to-stage production or its source origin.
-- Constructor private: callers cannot replace verified descriptor inputs.
data NativeFinalInstanceCorrespondence = NativeFinalInstanceCorrespondence
  GenericApplicationAssurance
  AssuranceManifest
  ArchitectureInstanceDescriptor
  CertifiedSourceManifestBinding
  CertifiedApplicationArtifact
  StageClosureBundle
  CertifiedReleaseArtifact
  NativeFinalAuthority
  deriving (Eq, Show)

-- | The exact complete source assurance retained by the checked source-manifest
-- producer and independently matched to the certified source artifact.
-- Returning its generic application identity alone would discard accepted
-- reusable-body evidence; this accessor does not derive any Rocq authority.
nativeCorrespondenceSourceAssurance
  :: NativeFinalInstanceCorrespondence -> GenericApplicationAssurance
nativeCorrespondenceSourceAssurance
  (NativeFinalInstanceCorrespondence source _ _ _ _ _ _ _) = source

-- | Preserve the entire independently checked INT-002 manifest through the
-- exported final boundary. The checked producer token supplies it, and the
-- lower-level binder requires equality with the independently certified
-- release manifest. A manifestId alone is not the accepted manifest object.
-- Read-only: no downstream producer or stage-origin authority is introduced.
-- | Preserve the exact opaque checked-instance source-manifest producer token.
-- Its constructor is private upstream: declaration-only closure can share the
-- same source and manifest projections but cannot carry the checked descriptor
-- required by the final binder. Retention is not StageClosure origin evidence.
nativeCorrespondenceSourceManifestBinding
  :: NativeFinalInstanceCorrespondence -> CertifiedSourceManifestBinding
nativeCorrespondenceSourceManifestBinding
  (NativeFinalInstanceCorrespondence _ _ _ binding _ _ _ _) = binding

nativeCorrespondenceManifest
  :: NativeFinalInstanceCorrespondence -> AssuranceManifest
nativeCorrespondenceManifest
  (NativeFinalInstanceCorrespondence _ manifest _ _ _ _ _ _) = manifest

-- | Complete checked producer descriptor at the final witness boundary.
-- No new downstream StageClosure/provenance authority is inferred.
nativeCorrespondenceArchitectureDescriptor
  :: NativeFinalInstanceCorrespondence -> ArchitectureInstanceDescriptor
nativeCorrespondenceArchitectureDescriptor
  (NativeFinalInstanceCorrespondence _ _ descriptor _ _ _ _ _) = descriptor

nativeCorrespondenceArchitectureInstance
  :: NativeFinalInstanceCorrespondence -> ArchitectureInstanceIdentity
nativeCorrespondenceArchitectureInstance =
  deriveArchitectureInstanceIdentity . nativeCorrespondenceArchitectureDescriptor

-- | Exact independently accepted StageClosure retained after the existing
-- CertifiedApplicationArtifact / CertifiedReleaseArtifact full-object equality
-- gate. Neither its closed revision nor its normalized Systems revision is a
-- substitute for this concrete object. This read-only projection is not a
-- stage-origin certificate or a Rocq representation.
-- | The independently accepted VER-010 source artifact, not merely the
-- matched source assurance and stage projections. The existing full-object
-- consumer equality gate has already compared its StageClosure against the
-- independently certified release. Retention does not authenticate an
-- architecture occurrence as the producer of that StageClosure.
nativeCorrespondenceCertifiedSource
  :: NativeFinalInstanceCorrespondence -> CertifiedApplicationArtifact
nativeCorrespondenceCertifiedSource
  (NativeFinalInstanceCorrespondence _ _ _ _ sourceArtifact _ _ _) = sourceArtifact

nativeCorrespondenceStageClosure
  :: NativeFinalInstanceCorrespondence -> StageClosureBundle
nativeCorrespondenceStageClosure
  (NativeFinalInstanceCorrespondence _ _ _ _ _ stage _ _) = stage

-- | Preserve the complete *supplied and independently certified* INT-005
-- release envelope, including LLVM and declared residual trust, at the final
-- consumer boundary. Its exact identity is not determined by manifest and
-- StageClosure projections alone. This accessor creates no release authority.
nativeCorrespondenceCertifiedRelease
  :: NativeFinalInstanceCorrespondence -> CertifiedReleaseArtifact
nativeCorrespondenceCertifiedRelease
  (NativeFinalInstanceCorrespondence _ _ _ _ _ _ release _) = release

nativeCorrespondenceAuthority
  :: NativeFinalInstanceCorrespondence -> NativeFinalAuthority
nativeCorrespondenceAuthority
  (NativeFinalInstanceCorrespondence _ _ _ _ _ _ _ authority) = authority

-- | Native assurance stores these both as 'Digest'; the wrappers distinguish
-- the raw Systems *byte digest* from the independently named lowering-ledger
-- root. Neither is the normalized SystemsArtifactRevision.
newtype NativeRawSystemsDigest = NativeRawSystemsDigest
  { unNativeRawSystemsDigest :: Digest }
  deriving (Eq, Show)

newtype NativeLoweringRootDigest = NativeLoweringRootDigest
  { unNativeLoweringRootDigest :: Digest }
  deriving (Eq, Show)

-- | Role-tagged, lossless *data* representation of the two independently
-- named native Digest uses. The leading ASCII role octet makes their wire
-- images disjoint even if the digest payloads happen to be identical.
-- Do not normalize or hash again: the entire native Text payload is retained.
-- Neither decoder independently accepts a manifest, supplies a Rocq encoding,
-- or establishes architecture-occurrence-to-StageClosure provenance.
encodeNativeRawSystemsDigestWire :: NativeRawSystemsDigest -> Text
encodeNativeRawSystemsDigestWire (NativeRawSystemsDigest (Digest value)) =
  Text.cons 'R' value

decodeNativeRawSystemsDigestWire :: Text -> Maybe NativeRawSystemsDigest
decodeNativeRawSystemsDigestWire wire =
  case Text.uncons wire of
    Just ('R', payload) -> Just (NativeRawSystemsDigest (Digest payload))
    _ -> Nothing

encodeNativeLoweringRootWire :: NativeLoweringRootDigest -> Text
encodeNativeLoweringRootWire (NativeLoweringRootDigest (Digest value)) =
  Text.cons 'L' value

decodeNativeLoweringRootWire :: Text -> Maybe NativeLoweringRootDigest
decodeNativeLoweringRootWire wire =
  case Text.uncons wire of
    Just ('L', payload) -> Just (NativeLoweringRootDigest (Digest payload))
    _ -> Nothing


-- | The normalized Systems revision, common Phase-1 contract revision, and
-- final closed contract revision are THREE independent native Text newtypes.
-- S/C/F role tags deliberately differ from raw manifest R and lowering L.
-- These partial data decoders provide lossless, role-separated transport;
-- accepting a supplied wire does not certify that a revision was derived
-- or that an architecture occurrence produced the accepted StageClosure.
encodeNativeSystemsRevisionWire :: SystemsArtifactRevision -> Text
encodeNativeSystemsRevisionWire (SystemsArtifactRevision value) = Text.cons 'S' value

decodeNativeSystemsRevisionWire :: Text -> Maybe SystemsArtifactRevision
decodeNativeSystemsRevisionWire wire =
  case Text.uncons wire of
    Just ('S', payload) -> Just (SystemsArtifactRevision payload)
    _ -> Nothing

encodeNativeCommonContractRevisionWire :: Phase1StageContractRevision -> Text
encodeNativeCommonContractRevisionWire (Phase1StageContractRevision value) =
  Text.cons 'C' value

decodeNativeCommonContractRevisionWire :: Text -> Maybe Phase1StageContractRevision
decodeNativeCommonContractRevisionWire wire =
  case Text.uncons wire of
    Just ('C', payload) -> Just (Phase1StageContractRevision payload)
    _ -> Nothing

encodeNativeClosedContractRevisionWire :: ClosedStageContractRevision -> Text
encodeNativeClosedContractRevisionWire (ClosedStageContractRevision value) =
  Text.cons 'F' value

decodeNativeClosedContractRevisionWire :: Text -> Maybe ClosedStageContractRevision
decodeNativeClosedContractRevisionWire wire =
  case Text.uncons wire of
    Just ('F', payload) -> Just (ClosedStageContractRevision payload)
    _ -> Nothing

-- | A separate data-only wire fragment for the concrete subject, instance and
-- realization revisions. These are three native Text newtypes, distinct from
-- R/L manifest digests and S/C/F stage contract revisions. The B/I/A tags
-- retain every character without deriving revision validity or provenance.
-- InstanceRevision is NOT the architecture occurrence's InstanceKey.
encodeNativeSubjectRevisionWire :: SubjectStageRevision -> Text
encodeNativeSubjectRevisionWire (SubjectStageRevision value) = Text.cons 'B' value

decodeNativeSubjectRevisionWire :: Text -> Maybe SubjectStageRevision
decodeNativeSubjectRevisionWire wire =
  case Text.uncons wire of
    Just ('B', payload) -> Just (SubjectStageRevision payload)
    _ -> Nothing

encodeNativeInstanceRevisionWire :: InstanceRevision -> Text
encodeNativeInstanceRevisionWire (InstanceRevision value) = Text.cons 'I' value

decodeNativeInstanceRevisionWire :: Text -> Maybe InstanceRevision
decodeNativeInstanceRevisionWire wire =
  case Text.uncons wire of
    Just ('I', payload) -> Just (InstanceRevision payload)
    _ -> Nothing

encodeNativeRealizationRevisionWire :: RealizationRevision -> Text
encodeNativeRealizationRevisionWire (RealizationRevision value) =
  Text.cons 'A' value

decodeNativeRealizationRevisionWire :: Text -> Maybe RealizationRevision
decodeNativeRealizationRevisionWire wire =
  case Text.uncons wire of
    Just ('A', payload) -> Just (RealizationRevision payload)
    _ -> Nothing

-- | The checked architecture occurrence's InstanceKey is an independent
-- native Text newtype; K is reserved for the occurrence key, not the concrete
-- StageClosure's I-tagged InstanceRevision. The StageClosure has no InstanceKey.
-- This is a reversible data representation of the *checked descriptor's*
-- identity projection, not a certificate that it produced any stage.
encodeNativeOccurrenceKeyWire :: InstanceKey -> Text
encodeNativeOccurrenceKeyWire (InstanceKey value) = Text.cons 'K' value

decodeNativeOccurrenceKeyWire :: Text -> Maybe InstanceKey
decodeNativeOccurrenceKeyWire wire =
  case Text.uncons wire of
    Just ('K', payload) -> Just (InstanceKey payload)
    _ -> Nothing

-- | The checked architecture occurrence is an exact pair (InstanceKey,
-- InstanceRevision), not an InstanceRevision alone. Keep both role-tagged
-- Text components separate. Neither pair equality nor matching the I-tagged
-- stage revision proves that this occurrence produced the accepted stage.
-- This is a reversible data codec; native acceptance still requires the
-- existing checked producer and exact accepted consumer objects.
encodeNativeCheckedOccurrenceIdentityWires
  :: ArchitectureInstanceIdentity -> (Text, Text)
encodeNativeCheckedOccurrenceIdentityWires occurrence =
  ( encodeNativeOccurrenceKeyWire (identityInstanceKey occurrence)
  , encodeNativeInstanceRevisionWire (identityInstanceRevision occurrence)
  )

decodeNativeCheckedOccurrenceIdentityWires
  :: (Text, Text) -> Maybe ArchitectureInstanceIdentity
decodeNativeCheckedOccurrenceIdentityWires (keyWire, revisionWire) =
  ArchitectureInstanceIdentity
    <$> decodeNativeOccurrenceKeyWire keyWire
    <*> decodeNativeInstanceRevisionWire revisionWire


-- | D is the verified GenericApplicationIdentity declaration-key ROLE;
-- V is the independent generic interface-revision ROLE. Both native
-- components are Text newtypes, but neither is a stage or instance revision.
-- This is ONLY a scalar projection of the checked identity: its essential
-- Map GenericStaticParameterKey SemanticForm is deliberately NOT serialized.
-- Equal D/V wires do not identify a GenericApplicationIdentity, let alone
-- establish independently accepted manifest or StageClosure provenance.
encodeNativeGenericDeclarationWire :: DeclarationKey -> Text
encodeNativeGenericDeclarationWire (DeclarationKey value) = Text.cons 'D' value

decodeNativeGenericDeclarationWire :: Text -> Maybe DeclarationKey
decodeNativeGenericDeclarationWire wire =
  case Text.uncons wire of
    Just ('D', payload) -> Just (DeclarationKey payload)
    _ -> Nothing

encodeNativeGenericInterfaceWire :: InterfaceRevision -> Text
encodeNativeGenericInterfaceWire (InterfaceRevision value) = Text.cons 'V' value

decodeNativeGenericInterfaceWire :: Text -> Maybe InterfaceRevision
decodeNativeGenericInterfaceWire wire =
  case Text.uncons wire of
    Just ('V', payload) -> Just (InterfaceRevision payload)
    _ -> Nothing

encodeNativeGenericApplicationScalarWires
  :: GenericApplicationIdentity -> (Text, Text)
encodeNativeGenericApplicationScalarWires application =
  ( encodeNativeGenericDeclarationWire (genericApplicationDeclarationKey application)
  , encodeNativeGenericInterfaceWire (genericApplicationInterfaceRevision application)
  )

-- | Returns a pair of role-checked scalar values, NEVER an accepted generic
-- application identity. Exact semantic actuals and checked producer evidence
-- must still come from the retained native source assurance and binding.
decodeNativeGenericApplicationScalarWires
  :: (Text, Text) -> Maybe (DeclarationKey, InterfaceRevision)
decodeNativeGenericApplicationScalarWires (declarationWire, interfaceWire) =
  (,) <$> decodeNativeGenericDeclarationWire declarationWire
      <*> decodeNativeGenericInterfaceWire interfaceWire

-- | Q identifies a static semantic-actuals MAP KEY, not a SemanticForm value.
-- The checked GenericApplicationIdentity contains a Map from these native
-- Text newtypes to structured SemanticForm values. Encoding its key domain
-- cannot authenticate the map's values, equality, or producer provenance.
encodeNativeGenericStaticParameterKeyWire :: GenericStaticParameterKey -> Text
encodeNativeGenericStaticParameterKeyWire (GenericStaticParameterKey key) =
  Text.cons 'Q' key

decodeNativeGenericStaticParameterKeyWire :: Text -> Maybe GenericStaticParameterKey
decodeNativeGenericStaticParameterKeyWire wire =
  case Text.uncons wire of
    Just ('Q', payload) -> Just (GenericStaticParameterKey payload)
    _ -> Nothing

-- | Canonical native key-domain diagnostic: Map.keys is ascending and unique.
-- This does not serialize SemanticForm or reconstruct an accepted application.
encodeNativeGenericActualsKeyDomainWires :: GenericApplicationIdentity -> [Text]
encodeNativeGenericActualsKeyDomainWires =
  map encodeNativeGenericStaticParameterKeyWire
    . Map.keys . genericApplicationSemanticArguments

-- | Only a canonical ascending, duplicate-free key list can be reconstructed.
-- No semantic values, source assurance, or generic acceptance are produced.
decodeNativeGenericActualsKeyDomainWires :: [Text] -> Maybe [GenericStaticParameterKey]
decodeNativeGenericActualsKeyDomainWires wires = do
  keys <- traverse decodeNativeGenericStaticParameterKeyWire wires
  if keys == Map.keys (Map.fromList (map (\key -> (key, ())) keys))
    then Just keys
    else Nothing

-- | M is a deliberately *partial* value representation: the native
-- SemanticForm sum has Atom, Ordered, Unordered and Record constructors.
-- Only an actual SemanticAtom carries a raw Text payload suitable for this
-- reversible scalar wire. A structured value is NEVER silently serialized
-- with show, coerced to an atom or treated as accepted generic actuals.
-- Neither direction authenticates a SemanticForm, producer, map or release.
encodeNativeSemanticAtomWire :: SemanticForm -> Maybe Text
encodeNativeSemanticAtomWire (SemanticAtom payload) = Just (Text.cons 'M' payload)
encodeNativeSemanticAtomWire _ = Nothing

decodeNativeSemanticAtomWire :: Text -> Maybe SemanticForm
decodeNativeSemanticAtomWire wire =
  case Text.uncons wire of
    Just ('M', payload) -> Just (SemanticAtom payload)
    _ -> Nothing

-- | Partial typed VECTOR, not a serialized Text/nat framing: preserve the
-- exact list order for a native SemanticOrdered whose immediate children are
-- all SemanticAtom. Empty vectors are valid ordered values. Nested, unordered
-- or record children fail closed; scalar/non-ordered inputs also fail.
-- The list carries disjoint per-atom M wires, not acceptance or provenance.
encodeNativeSemanticOrderedAtomWires :: SemanticForm -> Maybe [Text]
encodeNativeSemanticOrderedAtomWires (SemanticOrdered children) =
  traverse encodeNativeSemanticAtomWire children
encodeNativeSemanticOrderedAtomWires _ = Nothing

-- | Reconstructs an *unaccepted* SemanticOrdered native value, never a
-- GenericApplicationIdentity, source, stage, or CertifiedRelease artifact.
decodeNativeSemanticOrderedAtomWires :: [Text] -> Maybe SemanticForm
decodeNativeSemanticOrderedAtomWires wires =
  SemanticOrdered <$> traverse decodeNativeSemanticAtomWire wires

-- | Partial native SemanticUnordered set of ONLY SemanticAtom members. The
-- source Set.toAscList order is canonical for the native SemanticForm Ord
-- instance, not an asserted Rocq ordering or Text/string codec. Neither a
-- nested constructor nor an ordered/record/scalar value is accepted.
encodeNativeSemanticUnorderedAtomWires :: SemanticForm -> Maybe [Text]
encodeNativeSemanticUnorderedAtomWires (SemanticUnordered members) =
  traverse encodeNativeSemanticAtomWire (Set.toAscList members)
encodeNativeSemanticUnorderedAtomWires _ = Nothing

-- | Fail closed on duplicate, out-of-order or wrong-role atoms. The decoded
-- Set is an UNACCEPTED native data value, never release or stage authority.
-- Ordering and uniqueness are checked against the real native Set Ord.
decodeNativeSemanticUnorderedAtomWires :: [Text] -> Maybe SemanticForm
decodeNativeSemanticUnorderedAtomWires wires = do
  atoms <- traverse decodeNativeSemanticAtomWire wires
  let members = Set.fromList atoms
  if atoms == Set.toAscList members
    then Just (SemanticUnordered members)
    else Nothing

-- | H is a new, read-only transport role for the *plain Text* field
-- name of native SemanticRecord (Map Text SemanticForm). It is separate
-- from R (raw Systems digest), L (lowering root), S/C/F stage revisions,
-- B/I/A/P/K occurrence/stage identities, and D/V/Q/M generic/value roles.
-- This wrapper is not a checked record field or acceptance credential.
newtype NativeSemanticRecordFieldText = NativeSemanticRecordFieldText
  { unNativeSemanticRecordFieldText :: Text }
  deriving (Eq, Ord, Show)

encodeNativeSemanticRecordFieldWire :: NativeSemanticRecordFieldText -> Text
encodeNativeSemanticRecordFieldWire (NativeSemanticRecordFieldText field) =
  Text.cons 'H' field

decodeNativeSemanticRecordFieldWire :: Text -> Maybe NativeSemanticRecordFieldText
decodeNativeSemanticRecordFieldWire wire =
  case Text.uncons wire of
    Just ('H', payload) -> Just (NativeSemanticRecordFieldText payload)
    _ -> Nothing

-- | Native SemanticRecord projection restricted to atom-only field values.
-- Real Map.toAscList order is preserved. Never coerce a structured field
-- value or treat a wire as accepted manifest/stage/release authority.
encodeNativeSemanticRecordAtomFieldWires :: SemanticForm -> Maybe [(Text, Text)]
encodeNativeSemanticRecordAtomFieldWires (SemanticRecord fields) =
  traverse encodeField (Map.toAscList fields)
  where
    encodeField (key, value) = do
      atomWire <- encodeNativeSemanticAtomWire value
      pure (encodeNativeSemanticRecordFieldWire
              (NativeSemanticRecordFieldText key), atomWire)
encodeNativeSemanticRecordAtomFieldWires _ = Nothing

-- | Return only an UNACCEPTED native SemanticRecord. The exact native Map
-- Ord decides canonical key order; duplicate and out-of-order fields reject.
-- No Text/Rocq string transport or native-to-Rocq Map comparison is claimed.
decodeNativeSemanticRecordAtomFieldWires :: [(Text, Text)] -> Maybe SemanticForm
decodeNativeSemanticRecordAtomFieldWires wires = do
  fields <- traverse decodeField wires
  let keys = map fst fields
      canonicalKeys = Map.keys (Map.fromList (map (\key -> (key, ())) keys))
  if keys == canonicalKeys
    then Just (SemanticRecord (Map.fromList fields))
    else Nothing
  where
    decodeField (keyWire, valueWire) = do
      wrapped <- decodeNativeSemanticRecordFieldWire keyWire
      value <- decodeNativeSemanticAtomWire valueWire
      pure (unNativeSemanticRecordFieldText wrapped, value)

-- | Read-only Q/M pairs for the atom-only subset of the *actual native*
-- checked GenericApplicationIdentity semantic-actuals Map. Values of any
-- other SemanticForm constructor fail closed. Map.toAscList is the native
-- key ordering; this does not establish Rocq map/string transport.
encodeNativeGenericAtomActualPairWires
  :: GenericApplicationIdentity -> Maybe [(Text, Text)]
encodeNativeGenericAtomActualPairWires application =
  traverse encodeEntry
    (Map.toAscList (genericApplicationSemanticArguments application))
  where
    encodeEntry (key, form) = do
      valueWire <- encodeNativeSemanticAtomWire form
      pure (encodeNativeGenericStaticParameterKeyWire key, valueWire)

-- | Reconstruct only an UNACCEPTED Map. Strict native key order and uniqueness
-- must hold; roles Q for keys and M for atom values are disjoint. Never return
-- a checked application, assurance, manifest, StageClosure or CertifiedRelease.
decodeNativeGenericAtomActualPairWires
  :: [(Text, Text)] -> Maybe (Map.Map GenericStaticParameterKey SemanticForm)
decodeNativeGenericAtomActualPairWires wires = do
  entries <- traverse decodeEntry wires
  let keys = map fst entries
  if keys == Map.keys (Map.fromList (map (\key -> (key, ())) keys))
    then Just (Map.fromList entries)
    else Nothing
  where
    decodeEntry (keyWire, valueWire) =
      (,) <$> decodeNativeGenericStaticParameterKeyWire keyWire
          <*> decodeNativeSemanticAtomWire valueWire

-- | Bounded whole DATA projection of a checked native GenericApplicationIdentity:
-- D (DeclarationKey), V (InterfaceRevision), and the complete Q/M semantic-
-- actuals association when EVERY SemanticForm value is a SemanticAtom Text.
-- This composition preserves the actual native three-field shape; unlike a
-- scalar-only D/V projection, a change to an atom actual changes the wire.
-- Structured actuals fail closed. No acceptance or provenance is encoded.
encodeNativeGenericAtomApplicationWires
  :: GenericApplicationIdentity -> Maybe (Text, Text, [(Text, Text)])
encodeNativeGenericAtomApplicationWires application = do
  actualWires <- encodeNativeGenericAtomActualPairWires application
  let (declarationWire, interfaceWire) =
        encodeNativeGenericApplicationScalarWires application
  pure (declarationWire, interfaceWire, actualWires)

-- | Decode only a TYPED, UNACCEPTED triple, never GenericApplicationIdentity
-- acceptance, verified generic instantiation or architecture occurrence.
-- The Q/M decoder enforces the native Map ordering and uniqueness. Neither
-- this triple nor a supplied Rocq Prop authenticates manifest or StageClosure.
decodeNativeGenericAtomApplicationWires
  :: (Text, Text, [(Text, Text)])
  -> Maybe (DeclarationKey, InterfaceRevision,
            Map.Map GenericStaticParameterKey SemanticForm)
decodeNativeGenericAtomApplicationWires
  (declarationWire, interfaceWire, actualWires) = do
    (declaration, interfaceRevision) <-
      decodeNativeGenericApplicationScalarWires
        (declarationWire, interfaceWire)
    actuals <- decodeNativeGenericAtomActualPairWires actualWires
    pure (declaration, interfaceRevision, actuals)

-- | The concrete verifier-profile revision is a plain Phase1Stage Text field,
-- not a nominal Haskell revision type. This separate read-only role wrapper
-- gives a lossless data wire without inventing profile acceptance or a
-- native-to-Rocq serializer, and without certifying stage provenance.
newtype NativeVerifierProfileText = NativeVerifierProfileText
  { unNativeVerifierProfileText :: Text }
  deriving (Eq, Show)

-- | Reserved P role; other roles are raw R, lowering L, systems S,
-- common C, closed F, subject B, instance I, realization A.
encodeNativeVerifierProfileWire :: NativeVerifierProfileText -> Text
encodeNativeVerifierProfileWire (NativeVerifierProfileText value) =
  Text.cons 'P' value

decodeNativeVerifierProfileWire :: Text -> Maybe NativeVerifierProfileText
decodeNativeVerifierProfileWire wire =
  case Text.uncons wire of
    Just ('P', payload) -> Just (NativeVerifierProfileText payload)
    _ -> Nothing

-- | Read-only replay of the exact accepted manifest/StageClosure consumer
-- projections. The private constructor does not assert architecture-occurrence
-- provenance or a native-to-Rocq representation.
data NativeManifestStageReplay = NativeManifestStageReplay
  { nativeReplayRawDigest :: NativeRawSystemsDigest
  , nativeReplayLoweringRoot :: NativeLoweringRootDigest
  , nativeReplaySubjectRevision :: SubjectStageRevision
  , nativeReplayInstanceRevision :: InstanceRevision
  , nativeReplayRealizationRevision :: RealizationRevision
  , nativeReplaySystemsRevision :: SystemsArtifactRevision
  , nativeReplayCommonRevision :: Phase1StageContractRevision
  , nativeReplayClosedRevision :: ClosedStageContractRevision
  , nativeReplayVerifierProfile :: Text
  }
  deriving (Eq, Show)

data NativeManifestStageReplayError
  = NativeReplayProducerConsumerDrift
  | NativeReplaySuppliedStageDifferent
  | NativeReplaySuppliedManifestDifferent
  | NativeReplayRawSystemsDifferent NativeRawSystemsDigest NativeRawSystemsDigest
  | NativeReplayLoweringRootDifferent NativeLoweringRootDigest NativeLoweringRootDigest
  | NativeReplayAuthorityCoordinatesDifferent
  deriving (Eq, Show)

-- | Replay actual saved native objects, rather than trust a caller-supplied
-- model equality. The source/manifest producer, accepted VER-010 source and
-- INT-005 release are retained whole by the upstream private witness. The
-- supplied manifest and stage must be those same *whole* objects. This is an
-- equality diagnostic, not an independent acceptor for unverified inputs.
--
-- Candidate manifest digest and lowering root are compared to the raw
-- SystemsArtifact projections BEFORE the full-object candidate equality
-- gate, so an adversarial same-ID but changed digest/root gets its precise
-- domain-specific failure instead of an ambiguous revision mismatch.
replayNativeManifestStageCoordinates
  :: NativeFinalInstanceCorrespondence
  -> AssuranceManifest
  -> StageClosureBundle
  -> Either NativeManifestStageReplayError NativeManifestStageReplay
replayNativeManifestStageCoordinates witness suppliedManifest suppliedStage =
  let producer = nativeCorrespondenceSourceManifestBinding witness
      sourceObject = nativeCorrespondenceCertifiedSource witness
      releaseObject = nativeCorrespondenceCertifiedRelease witness
      storedManifest = nativeCorrespondenceManifest witness
      storedStage = nativeCorrespondenceStageClosure witness
      authority = nativeCorrespondenceAuthority witness
      subject = concreteSubjectStage (stageClosureConcrete suppliedStage)
      common = subjectStageBase subject
      systems = phase1StageSystemsArtifact common
      manifestRaw = NativeRawSystemsDigest
        (manifestImplementationDigest suppliedManifest)
      actualRaw = NativeRawSystemsDigest (systemsArtifactDigest systems)
      manifestRoot = NativeLoweringRootDigest
        (manifestLoweringLedgerRoot suppliedManifest)
      actualRoot = NativeLoweringRootDigest
        (loweringLedgerRoot (systemsArtifactLoweringLedger systems))
      receipt = NativeManifestStageReplay
        actualRaw actualRoot
        (subjectStageRevision subject)
        (phase1StageInstanceRevision common)
        (phase1StageRealizationRevision common)
        (phase1StageSystemsArtifactRevision common)
        (phase1StageContractRevision common)
        (stageClosureContractRevision suppliedStage)
        (phase1StageVerifierProfileRevision common)
  in if sourceManifestBindingSourceAssurance producer
          /= nativeCorrespondenceSourceAssurance witness
       || certifiedApplicationSourceAssurance sourceObject
          /= nativeCorrespondenceSourceAssurance witness
       || sourceManifestBindingManifest producer /= storedManifest
       || certifiedReleaseManifest releaseObject /= storedManifest
       || certifiedApplicationStageClosure sourceObject /= storedStage
       || certifiedReleaseStageClosure releaseObject /= storedStage
       then Left NativeReplayProducerConsumerDrift
     else if suppliedStage /= storedStage
       then Left NativeReplaySuppliedStageDifferent
     else if manifestRaw /= actualRaw
       then Left (NativeReplayRawSystemsDifferent manifestRaw actualRaw)
     else if manifestRoot /= actualRoot
       then Left (NativeReplayLoweringRootDifferent manifestRoot actualRoot)
     else if suppliedManifest /= storedManifest
       then Left NativeReplaySuppliedManifestDifferent
     else if nativeFinalManifestId authority /= manifestId suppliedManifest
       || nativeFinalRawSystemsDigest authority /= unNativeRawSystemsDigest actualRaw
       || nativeFinalLoweringRoot authority /= unNativeLoweringRootDigest actualRoot
       || nativeFinalSubjectRevision authority /= nativeReplaySubjectRevision receipt
       || nativeFinalInstanceRevision authority /= nativeReplayInstanceRevision receipt
       || nativeFinalRealizationRevision authority /= nativeReplayRealizationRevision receipt
       || nativeFinalSystemsRevision authority /= nativeReplaySystemsRevision receipt
       || nativeFinalCommonContractRevision authority /= nativeReplayCommonRevision receipt
       || nativeFinalClosedContractRevision authority /= nativeReplayClosedRevision receipt
       || nativeFinalVerifierProfile authority /= nativeReplayVerifierProfile receipt
       then Left NativeReplayAuthorityCoordinatesDifferent
     else Right receipt

-- | A second, read-only replay gate for full independently accepted *objects*.
-- The earlier manifest/stage replay checked externally supplied manifest and
-- stage coordinates; this gate additionally refuses replacement of the exact
-- checked producer token, accepted VER-010 source envelope, or selected INT-005
-- release envelope even when their projections happen to agree. The receipt's
-- private constructor carries no new acceptance or stage-origin authority.
data NativeExactAcceptedConsumerReplay = NativeExactAcceptedConsumerReplay
  { nativeExactReplayCheckedProducer :: CertifiedSourceManifestBinding
  , nativeExactReplayCertifiedSource :: CertifiedApplicationArtifact
  , nativeExactReplayCertifiedRelease :: CertifiedReleaseArtifact
  , nativeExactReplayCoordinates :: NativeManifestStageReplay
  }
  deriving (Eq, Show)

data NativeExactAcceptedConsumerReplayError
  = NativeExactReplayProducerDifferent
  | NativeExactReplaySourceDifferent
  | NativeExactReplayReleaseDifferent
  | NativeExactReplayCoordinateMismatch NativeManifestStageReplayError
  deriving (Eq, Show)

-- | No caller-supplied full object may be promoted to native acceptance by
-- matching just its manifestId, raw digest, revisions, or release coordinates.
-- Matching exact whole objects allows a diagnostic recheck, not an independent
-- producer or a proof that the architecture occurrence generated StageClosure.
replayNativeExactAcceptedConsumers
  :: NativeFinalInstanceCorrespondence
  -> CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either NativeExactAcceptedConsumerReplayError NativeExactAcceptedConsumerReplay
replayNativeExactAcceptedConsumers witness candidateProducer candidateSource candidateRelease
  | candidateProducer /= nativeCorrespondenceSourceManifestBinding witness =
      Left NativeExactReplayProducerDifferent
  | candidateSource /= nativeCorrespondenceCertifiedSource witness =
      Left NativeExactReplaySourceDifferent
  | candidateRelease /= nativeCorrespondenceCertifiedRelease witness =
      Left NativeExactReplayReleaseDifferent
  | otherwise = do
      coordinates <- either (Left . NativeExactReplayCoordinateMismatch) Right
        (replayNativeManifestStageCoordinates
          witness
          (sourceManifestBindingManifest candidateProducer)
          (certifiedReleaseStageClosure candidateRelease))
      pure (NativeExactAcceptedConsumerReplay
        candidateProducer candidateSource candidateRelease coordinates)

-- | Equality of the architecture occurrence's canonical revision with the
-- retained concrete stage's InstanceRevision. The constructor is private.
-- Crucially, this is a necessary consistency check, NOT evidence that the
-- stage was produced by that occurrence: StageClosure stores no InstanceKey.
data NativeStageRevisionEquality = NativeStageRevisionEquality
  ArchitectureInstanceIdentity InstanceRevision
  deriving (Eq, Show)

nativeStageRevisionEqualityOccurrence
  :: NativeStageRevisionEquality -> ArchitectureInstanceIdentity
nativeStageRevisionEqualityOccurrence
  (NativeStageRevisionEquality occurrence _) = occurrence

nativeStageRevisionEqualityStageRevision
  :: NativeStageRevisionEquality -> InstanceRevision
nativeStageRevisionEqualityStageRevision
  (NativeStageRevisionEquality _ revision) = revision

data NativeStageRevisionEqualityError
  = NativeStageRevisionDifferent InstanceRevision InstanceRevision
  deriving (Eq, Show)

-- | A second, fail-closed gate on an already accepted native witness. It does
-- not retrofit a stage-origin proof into the upstream certified producers.
-- Same revision with a different occurrence key remains insufficient.
checkNativeStageRevisionEquality
  :: NativeFinalInstanceCorrespondence
  -> Either NativeStageRevisionEqualityError NativeStageRevisionEquality
checkNativeStageRevisionEquality witness =
  let occurrence = nativeCorrespondenceArchitectureInstance witness
      expected = identityInstanceRevision occurrence
      actual = nativeFinalInstanceRevision (nativeCorrespondenceAuthority witness)
  in if expected == actual
      then Right (NativeStageRevisionEquality occurrence actual)
      else Left (NativeStageRevisionDifferent expected actual)

data NativeFinalInstanceCorrespondenceError
  = NativeFinalInstanceSourceAssuranceMismatch
  | NativeFinalInstanceSourceRejected SourceManifestBindingError
  | NativeFinalInstanceReleaseRejected SourceManifestBindingError
  deriving (Eq, Show)

-- | Compose, without substituting identity domains:
--   (1) accepted GenericApplicationAssurance and exact semantic actuals;
--   (2) canonical architecture descriptor and instance stored in the bundle;
--   (3) the *actual* INT-002 manifest producer;
--   (4) independently accepted VER-010 source artifact and INT-005 release;
--   (5) full manifest and retained StageClosure equality, including the
--       actual raw Systems digest and lowering root, checked by the adapter.
-- The accepted VER-010 source envelope is retained verbatim after these gates;
-- it cannot be recreated by exporting its component projections alone.
--
-- The downstream native stage's InstanceRevision is NOT asserted equal to the
-- architecture occurrence's InstanceRevision merely because both mention an
-- instance: no such competent bridge is established by this interface.
closeNativeFinalInstanceCorrespondence
  :: GenericApplicationAssurance
  -> ArchitectureInstanceDescriptor
  -> VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either NativeFinalInstanceCorrespondenceError NativeFinalInstanceCorrespondence
closeNativeFinalInstanceCorrespondence
  source descriptor bundle policy context ledger selection sourceArtifact release = do
    -- The producer must use the EXACT accepted source-assurance object,
    -- not merely a second assurance with the same application identity.
    -- This check is necessary, not stage-origin or model-proof authority.
    if source == certifiedApplicationSourceAssurance sourceArtifact
      then Right ()
      else Left NativeFinalInstanceSourceAssuranceMismatch
    produced <- either (Left . NativeFinalInstanceSourceRejected) Right
      (closeSourceManifestBindingForInstance
        source descriptor bundle policy context ledger selection)
    authority <- either (Left . NativeFinalInstanceReleaseRejected) Right
      (bindProducedFinalAuthority produced sourceArtifact release)
    -- Do not lose the checked static/declaration inputs across the *final*
    -- producer-to-consumer witness boundary. The earlier source-manifest
    -- token separately retains this same exact descriptor.
    pure (NativeFinalInstanceCorrespondence
      (sourceManifestBindingSourceAssurance produced)
      (sourceManifestBindingManifest produced)
      descriptor
      produced
      sourceArtifact
      (certifiedReleaseStageClosure release)
      release
      authority)

-- | Candidate TRANSPORT ONLY: a complete atom-only D/V/Q/M application
-- projection alongside two independently named raw manifest digest domains.
-- Its public constructor cannot carry acceptance or stage-origin authority.
data NativeAtomManifestWireCandidate = NativeAtomManifestWireCandidate
  { nativeAtomManifestCandidateApplication :: (Text, Text, [(Text, Text)])
  , nativeAtomManifestCandidateRawWire :: Text
  , nativeAtomManifestCandidateLoweringWire :: Text
  }
  deriving (Eq, Show)

-- | Private diagnostic receipt. It is obtainable only by replaying the exact
-- checked producer and independently accepted VER-010/INT-005 whole objects.
-- All values are native typed data; no native-to-Rocq Text/string or nat bridge
-- is manufactured. The occurrence key is NOT a StageClosure producer proof.
data NativeAtomManifestReplay = NativeAtomManifestReplay
  { nativeAtomManifestReplayApplication ::
      (DeclarationKey, InterfaceRevision, Map.Map GenericStaticParameterKey SemanticForm)
  , nativeAtomManifestReplayRawDigest :: NativeRawSystemsDigest
  , nativeAtomManifestReplayLoweringRoot :: NativeLoweringRootDigest
  , nativeAtomManifestReplayStageCoordinates :: NativeManifestStageReplay
  , nativeAtomManifestReplayCheckedOccurrence :: ArchitectureInstanceIdentity
  }
  deriving (Eq, Show)

data NativeAtomManifestReplayError
  = NativeAtomManifestExactConsumersDifferent NativeExactAcceptedConsumerReplayError
  | NativeAtomManifestStructuredActualsUnsupported
  | NativeAtomManifestApplicationWireMalformed
  | NativeAtomManifestApplicationDifferent
  | NativeAtomManifestRawRoleMalformed
  | NativeAtomManifestLoweringRoleMalformed
  | NativeAtomManifestRawDifferent
  | NativeAtomManifestLoweringDifferent
  | NativeAtomManifestStageCoordinatesDifferent
  deriving (Eq, Show)

-- | Bounded native D/V/Q/M + R/L correspondence across accepted boundaries.
-- First recheck the *whole* checked producer and independently accepted
-- source/release objects, with StageClosure retained exactly. The actual
-- checked GenericApplicationIdentity comes from its accepted source lineage;
-- the R raw Systems digest and L lowering root come from the independently
-- accepted producer manifest and must equal actual typed stage coordinates.
-- Structured SemanticForm actuals fail closed, as do malformed roles and
-- same-D/V-but-changed Q/M associations. The caller's wires are NOT authority.
-- No claim of generic-application acceptance by decode, occurrence-to-stage
-- production, FixedFinalAuthorityAdapter or FinalArtifactCertified follows.
replayNativeAtomManifestCandidate
  :: NativeFinalInstanceCorrespondence
  -> CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> NativeAtomManifestWireCandidate
  -> Either NativeAtomManifestReplayError NativeAtomManifestReplay
replayNativeAtomManifestCandidate witness producer sourceObject releaseObject candidate = do
  exact <- either (Left . NativeAtomManifestExactConsumersDifferent) Right
    (replayNativeExactAcceptedConsumers witness producer sourceObject releaseObject)
  let checkedSource = sourceManifestBindingSourceAssurance
        (nativeExactReplayCheckedProducer exact)
      checkedApplication = genericDischargeApplicationIdentity
        (genericApplicationAssuranceLineage checkedSource)
      manifest = sourceManifestBindingManifest
        (nativeExactReplayCheckedProducer exact)
      coordinates = nativeExactReplayCoordinates exact
      expectedRaw = NativeRawSystemsDigest (manifestImplementationDigest manifest)
      expectedRoot = NativeLoweringRootDigest (manifestLoweringLedgerRoot manifest)
  expectedApplicationWires <- maybe
    (Left NativeAtomManifestStructuredActualsUnsupported) Right
    (encodeNativeGenericAtomApplicationWires checkedApplication)
  decodedApplication <- maybe
    (Left NativeAtomManifestApplicationWireMalformed) Right
    (decodeNativeGenericAtomApplicationWires
      (nativeAtomManifestCandidateApplication candidate))
  if nativeAtomManifestCandidateApplication candidate /= expectedApplicationWires
    then Left NativeAtomManifestApplicationDifferent
    else Right ()
  decodedRaw <- maybe (Left NativeAtomManifestRawRoleMalformed) Right
    (decodeNativeRawSystemsDigestWire (nativeAtomManifestCandidateRawWire candidate))
  decodedRoot <- maybe (Left NativeAtomManifestLoweringRoleMalformed) Right
    (decodeNativeLoweringRootWire (nativeAtomManifestCandidateLoweringWire candidate))
  if decodedRaw /= expectedRaw
    then Left NativeAtomManifestRawDifferent
    else Right ()
  if decodedRoot /= expectedRoot
    then Left NativeAtomManifestLoweringDifferent
    else Right ()
  if decodedRaw /= nativeReplayRawDigest coordinates
      || decodedRoot /= nativeReplayLoweringRoot coordinates
    then Left NativeAtomManifestStageCoordinatesDifferent
    else Right ()
  pure (NativeAtomManifestReplay
    decodedApplication decodedRaw decodedRoot coordinates
    (nativeCorrespondenceArchitectureInstance witness))

-- | Read-only unaccepted S candidate with the already checked D/V/Q/M and
-- independently accepted R/L domains: not a source of stage authority.
data NativeAtomManifestSystemsWireCandidate = NativeAtomManifestSystemsWireCandidate
  { nativeAtomManifestSystemsBaseCandidate :: NativeAtomManifestWireCandidate
  , nativeAtomManifestSystemsRevisionWire :: Text
  } deriving (Eq, Show)

-- | Constructor private: retains typed S from the exact accepted StageClosure.
data NativeAtomManifestSystemsReplay = NativeAtomManifestSystemsReplay
  { nativeAtomManifestSystemsReplayBase :: NativeAtomManifestReplay
  , nativeAtomManifestSystemsReplayRevision :: SystemsArtifactRevision
  } deriving (Eq, Show)

data NativeAtomManifestSystemsReplayError
  = NativeAtomManifestSystemsBaseDifferent NativeAtomManifestReplayError
  | NativeAtomManifestSystemsRoleMalformed
  | NativeAtomManifestSystemsDifferent
  deriving (Eq, Show)

-- | First recheck the entire checked producer and independently accepted
-- VER-010 source / INT-005 CertifiedRelease, then compare S to the actual
-- native normalized SystemsArtifactRevision. Never infer stage provenance.
replayNativeAtomManifestSystemsCandidate
  :: NativeFinalInstanceCorrespondence
  -> CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> NativeAtomManifestSystemsWireCandidate
  -> Either NativeAtomManifestSystemsReplayError NativeAtomManifestSystemsReplay
replayNativeAtomManifestSystemsCandidate witness producer sourceObject releaseObject candidate = do
  baseReceipt <- either (Left . NativeAtomManifestSystemsBaseDifferent) Right
    (replayNativeAtomManifestCandidate witness producer sourceObject releaseObject
       (nativeAtomManifestSystemsBaseCandidate candidate))
  normalized <- maybe (Left NativeAtomManifestSystemsRoleMalformed) Right
    (decodeNativeSystemsRevisionWire (nativeAtomManifestSystemsRevisionWire candidate))
  if normalized /= nativeReplaySystemsRevision
       (nativeAtomManifestReplayStageCoordinates baseReceipt)
    then Left NativeAtomManifestSystemsDifferent
    else pure (NativeAtomManifestSystemsReplay baseReceipt normalized)


-- | Unaccepted C candidate extends the exactly replayed D/V/Q/M, raw R/L,
-- and normalized S coordinate. C is the *common* Phase1StageContractRevision,
-- not the final ClosedStageContractRevision F or any raw manifest digest.
data NativeAtomManifestCommonWireCandidate = NativeAtomManifestCommonWireCandidate
  { nativeAtomManifestCommonBaseCandidate :: NativeAtomManifestSystemsWireCandidate
  , nativeAtomManifestCommonRevisionWire :: Text
  } deriving (Eq, Show)

-- | Private receipt: the accepted objects and exact stage coordinates are
-- still retained by the nested replay. No wire grants stage authority.
data NativeAtomManifestCommonReplay = NativeAtomManifestCommonReplay
  { nativeAtomManifestCommonReplayBase :: NativeAtomManifestSystemsReplay
  , nativeAtomManifestCommonReplayRevision :: Phase1StageContractRevision
  } deriving (Eq, Show)

data NativeAtomManifestCommonReplayError
  = NativeAtomManifestCommonBaseDifferent NativeAtomManifestSystemsReplayError
  | NativeAtomManifestCommonRoleMalformed
  | NativeAtomManifestCommonDifferent
  deriving (Eq, Show)

-- | Recheck checked source-manifest production and exact independent VER-010
-- and INT-005 consumers, then S, before comparing native common C against
-- the same retained StageClosure. Do not derive architecture-stage provenance.
replayNativeAtomManifestCommonCandidate
  :: NativeFinalInstanceCorrespondence
  -> CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> NativeAtomManifestCommonWireCandidate
  -> Either NativeAtomManifestCommonReplayError NativeAtomManifestCommonReplay
replayNativeAtomManifestCommonCandidate witness producer sourceObject releaseObject candidate = do
  baseReceipt <- either (Left . NativeAtomManifestCommonBaseDifferent) Right
    (replayNativeAtomManifestSystemsCandidate witness producer sourceObject releaseObject
       (nativeAtomManifestCommonBaseCandidate candidate))
  common <- maybe (Left NativeAtomManifestCommonRoleMalformed) Right
    (decodeNativeCommonContractRevisionWire (nativeAtomManifestCommonRevisionWire candidate))
  if common /= nativeReplayCommonRevision
       (nativeAtomManifestReplayStageCoordinates
         (nativeAtomManifestSystemsReplayBase baseReceipt))
    then Left NativeAtomManifestCommonDifferent
    else pure (NativeAtomManifestCommonReplay baseReceipt common)

-- | Unaccepted final F extends exact checked D/V/Q/M, independently accepted
-- R/L, normalized S and common C. F is the closed StageClosure contract.
data NativeAtomManifestClosedWireCandidate = NativeAtomManifestClosedWireCandidate
  { nativeAtomManifestClosedBaseCandidate :: NativeAtomManifestCommonWireCandidate
  , nativeAtomManifestClosedRevisionWire :: Text
  } deriving (Eq, Show)

-- | Constructor private; this is diagnostic data, never release authority.
data NativeAtomManifestClosedReplay = NativeAtomManifestClosedReplay
  { nativeAtomManifestClosedReplayBase :: NativeAtomManifestCommonReplay
  , nativeAtomManifestClosedReplayRevision :: ClosedStageContractRevision
  } deriving (Eq, Show)

data NativeAtomManifestClosedReplayError
  = NativeAtomManifestClosedBaseDifferent NativeAtomManifestCommonReplayError
  | NativeAtomManifestClosedRoleMalformed
  | NativeAtomManifestClosedDifferent
  deriving (Eq, Show)

-- | Revalidate the checked producer, exact independent source/release consumer
-- and all prior typed domains before comparing final F from the same concrete
-- accepted StageClosure. No checked occurrence-to-stage origin is inferred.
replayNativeAtomManifestClosedCandidate
  :: NativeFinalInstanceCorrespondence
  -> CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> NativeAtomManifestClosedWireCandidate
  -> Either NativeAtomManifestClosedReplayError NativeAtomManifestClosedReplay
replayNativeAtomManifestClosedCandidate witness producer sourceObject releaseObject candidate = do
  baseReceipt <- either (Left . NativeAtomManifestClosedBaseDifferent) Right
    (replayNativeAtomManifestCommonCandidate witness producer sourceObject releaseObject
       (nativeAtomManifestClosedBaseCandidate candidate))
  closed <- maybe (Left NativeAtomManifestClosedRoleMalformed) Right
    (decodeNativeClosedContractRevisionWire (nativeAtomManifestClosedRevisionWire candidate))
  if closed /= nativeReplayClosedRevision
       (nativeAtomManifestReplayStageCoordinates
         (nativeAtomManifestSystemsReplayBase
           (nativeAtomManifestCommonReplayBase baseReceipt)))
    then Left NativeAtomManifestClosedDifferent
    else pure (NativeAtomManifestClosedReplay baseReceipt closed)

-- | Unaccepted B subject-stage candidate extends exact checked D/V/Q/M,
-- independently accepted raw R/L, normalized S, common C and closed F.
-- B is the concrete SubjectStageRevision, not a contract or an occurrence key.
data NativeAtomManifestSubjectWireCandidate = NativeAtomManifestSubjectWireCandidate
  { nativeAtomManifestSubjectBaseCandidate :: NativeAtomManifestClosedWireCandidate
  , nativeAtomManifestSubjectRevisionWire :: Text
  } deriving (Eq, Show)

-- | Private read-only receipt, retaining the same accepted StageClosure.
data NativeAtomManifestSubjectReplay = NativeAtomManifestSubjectReplay
  { nativeAtomManifestSubjectReplayBase :: NativeAtomManifestClosedReplay
  , nativeAtomManifestSubjectReplayRevision :: SubjectStageRevision
  } deriving (Eq, Show)

data NativeAtomManifestSubjectReplayError
  = NativeAtomManifestSubjectBaseDifferent NativeAtomManifestClosedReplayError
  | NativeAtomManifestSubjectRoleMalformed
  | NativeAtomManifestSubjectDifferent
  deriving (Eq, Show)

-- | Replay the exact checked producer, independently accepted VER-010 source
-- and INT-005 CertifiedRelease/StageClosure, and all D/V/Q/M/R/L/S/C/F
-- comparisons BEFORE checking B against the same native StageClosure.
-- Candidate wires do not reconstruct accepted authority or authenticate
-- architecture occurrence -> StageClosure production.
replayNativeAtomManifestSubjectCandidate
  :: NativeFinalInstanceCorrespondence
  -> CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> NativeAtomManifestSubjectWireCandidate
  -> Either NativeAtomManifestSubjectReplayError NativeAtomManifestSubjectReplay
replayNativeAtomManifestSubjectCandidate witness producer sourceObject releaseObject candidate = do
  baseReceipt <- either (Left . NativeAtomManifestSubjectBaseDifferent) Right
    (replayNativeAtomManifestClosedCandidate witness producer sourceObject releaseObject
       (nativeAtomManifestSubjectBaseCandidate candidate))
  subject <- maybe (Left NativeAtomManifestSubjectRoleMalformed) Right
    (decodeNativeSubjectRevisionWire (nativeAtomManifestSubjectRevisionWire candidate))
  if subject /= nativeReplaySubjectRevision
       (nativeAtomManifestReplayStageCoordinates
         (nativeAtomManifestSystemsReplayBase
           (nativeAtomManifestCommonReplayBase
             (nativeAtomManifestClosedReplayBase baseReceipt))))
    then Left NativeAtomManifestSubjectDifferent
    else pure (NativeAtomManifestSubjectReplay baseReceipt subject)
