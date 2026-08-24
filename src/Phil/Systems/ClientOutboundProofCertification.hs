{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ClientOutboundProofCertification
  ( systemsClientOutboundCertificationSpec
  ) where

import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsClientOutboundCertificationSpec :: RocqCertificationSpec
systemsClientOutboundCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-client-outbound"
  , rocqSpecObligation = ObligationId "PHIL-SYS-CLIENT-OUTBOUND-001"
  , rocqSpecClaim =
      "For the verified current Phase 0 RecognitionFailure successor, the predecessor ClientOutbound witness remains exact: UploadClient retains the exact transport and payload owner; supported_versions() produces the exact VersionSet used to construct exactly one Hello record and send that exact record on the exact client transport; the payload is borrowed exactly once as a non-owning view with no copy, SHA-256 is computed over that exact view, length and kind are projected from the exact payload, exactly one Begin record is constructed from exact length/kind/digest with static digestAlg=sha256 and sent on the exact transport; the three ClientOutbound lowering decisions and no-copy borrow invariant are rebound to the current successor; and no physical Hello/Begin/version-set/payload-kind/digest-provider representation, runtime serialization, or outer framing is claimed."
  , rocqSpecKind = "Systems client outbound Hello/Begin semantic construction"
  , rocqSpecOrigin =
      "src/Phil/Systems/ClientOutbound.hs; src/Phil/Systems/RecognitionFailure.hs; test/ClientOutboundMain.hs; proof/Phil/Systems/ClientOutbound.v"
  , rocqSpecScope =
      "Phil.Systems current RecognitionFailure successor preserving client outbound semantic values and dataflow"
  , rocqSpecRepresentation =
      "explicit VersionSet/Hello and payload-view/SHA256/length/kind/Begin semantic values with exact producer-consumer identities"
  , rocqSpecSubjects =
      [ "UploadClient/client.entry"
      , "client.transport : TransportHandle"
      , "client.payload : OwnedBuffer[Bytes[payload.length]]"
      , "client.supported_versions : RuntimeOpaque[VersionSet]"
      , "client.hello : RuntimeRecord[Hello]"
      , "client.payload_view : BorrowedSlice[client.payload]"
      , "client.payload_length : UInt64"
      , "client.payload_kind : RuntimeOpaque[PayloadKind]"
      , "client.declared_digest : RuntimeOpaque[SHA256Digest]"
      , "client.begin : RuntimeRecord[Begin]"
      , "lower.client.outbound.records"
      , "lower.client.outbound.digest_borrow"
      , "lower.client.outbound.sha256"
      , "invariant.client.payload.digest_borrow_no_copy"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_client_outbound_is_preserved_by_current_successor"
      , "verified_systems_client_outbound_preserves_exact_hello_dataflow"
      , "verified_systems_client_outbound_preserves_exact_begin_dataflow"
      , "verified_systems_client_outbound_binds_decisions_and_borrow_invariant"
      , "verified_systems_client_outbound_claims_no_physical_representation"
      , "systems_client_outbound_hello_drift_is_rejected"
      , "systems_client_outbound_begin_or_copy_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/ClientOutbound.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/ClientOutbound.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-CLIENT-OUTBOUND-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-CLIENT-OUTBOUND-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell ValueId/BlockId identities, operation ordering and multiplicity, use enumeration, RuntimeOpaque/RuntimeRecord/BorrowedSlice roles, lowering-decision rebinding, and the current RecognitionFailure successor's explicit preservation of the ClientOutbound witness remain trust boundaries. Concrete Hello/Begin/version-set/payload-kind representations, SHA-256 provider behavior, serialization, physical I/O, and outer framing are not proved."
  }
