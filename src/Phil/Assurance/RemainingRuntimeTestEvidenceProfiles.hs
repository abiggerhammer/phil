{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RemainingRuntimeTestEvidenceProfiles
  ( knownRemainingRuntimeTestEvidenceCertificationSpec
  , runtimeDigestCertificationSpec
  , runtimeExactReceiveFixtureCertificationSpec
  , runtimeStorageFixtureCertificationSpec
  , runtimeAcceptedFixtureCertificationSpec
  , runtimeRejectedFixtureCertificationSpec
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

knownRemainingRuntimeTestEvidenceCertificationSpec :: Text -> Maybe TestEvidenceCertificationSpec
knownRemainingRuntimeTestEvidenceCertificationSpec profile
  | profile == testSpecProfile runtimeDigestCertificationSpec = Just runtimeDigestCertificationSpec
  | profile == testSpecProfile runtimeExactReceiveFixtureCertificationSpec = Just runtimeExactReceiveFixtureCertificationSpec
  | profile == testSpecProfile runtimeStorageFixtureCertificationSpec = Just runtimeStorageFixtureCertificationSpec
  | profile == testSpecProfile runtimeAcceptedFixtureCertificationSpec = Just runtimeAcceptedFixtureCertificationSpec
  | profile == testSpecProfile runtimeRejectedFixtureCertificationSpec = Just runtimeRejectedFixtureCertificationSpec
  | otherwise = Nothing

runtimeDigestCertificationSpec :: TestEvidenceCertificationSpec
runtimeDigestCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-digest"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-DIGEST-001"
  , testSpecClaim =
      "For the ABI-conforming phil-runtime/phase0/digest-validation-v1 fixture, digest validation consumes the explicit recognized Begin handle and exact payload-owner handle, computes SHA-256 over the exact payload bytes, returns true for the standard-vector match and false for a one-bit expected-digest mismatch, uses no ambient current-record/current-payload/current-digest state, and leaves payload ownership unchanged on digest mismatch for ordinary rejection cleanup."
  , testSpecKind = "Digest validation / SHA-256 provider fixture"
  , testSpecOrigin =
      "runtime/phase0/digest_validation_v1.h; runtime/phase0/digest_validation_v1_smoke.c; runtime/phase0/digest_validation_v1_smoke_main.c; runtime/phase0/digest_validation_v1_bad_ambient.c; scripts/check_runtime_abi.py"
  , testSpecScope = "digest-validation-v1 deterministic executable fixture"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over exact emitted/provider LLVM, linked executable, standard/mismatch vectors, ambient-provider rejection, and execution log"
  , testSpecSubjects =
      [ "explicit recognized Begin handle"
      , "exact payload-owner handle"
      , "SHA-256 abc standard-vector match"
      , "one-bit expected-digest mismatch"
      , "payload owner preserved for rejection cleanup"
      , "ambient/nullary digest-validation provider rejection"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/digest_validation_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-digest-validation.ll"
      , "digest-validation-runtime.ll"
      , "digest-validation-bad-ambient.ll"
      , "phase0-upload-digest-validation-linked.bc"
      , "phase0-upload-digest-validation-smoke"
      , "runtime/phase0/digest_validation_v1.h"
      , "runtime/phase0/digest_validation_v1_smoke.c"
      , "runtime/phase0/digest_validation_v1_bad_ambient.c"
      , "scripts/check_runtime_abi.py"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/RemainingRuntimeTestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:digest-validation-v1:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-DIGEST-001:v1"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-DIGEST-001.differential.v1"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: SHA-256 DigestMatches accepts the exact recognized Begin and received payload"
      , "PASS: SHA-256 mismatch leaves the exact payload owner for generated rejection cleanup"
      , "PASS: runtime ABI checker rejects ambient nullary digest validation"
      ]
  , testSpecForbiddenMarkers = ["FAIL:", "expected ABI checker to reject"]
  , testSpecValidity = runtimeFixtureValidity "digest-validation-v1/executable-smoke/v1"
  , testSpecProducer = "digest-validation-v1 ABI comparison + standard/mismatch-vector executable smoke + ambient-provider rejection"
  , testSpecCheckerProfile =
      "LLVM/Clang 18; scripts/check_runtime_abi.py; native digest_validation_v1_smoke_main.c execution; libcrypto SHA256; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "OpenSSL/libcrypto SHA-256 implementation correctness, C/Clang/LLVM 18, host execution, fixture instrumentation, opaque runtime record/payload representation, expected-digest accessor behavior, and production transport/storage remain explicit tested/runtime boundaries; this is not a cryptographic proof of SHA-256."
  }

runtimeExactReceiveFixtureCertificationSpec :: TestEvidenceCertificationSpec
runtimeExactReceiveFixtureCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-exact-receive-fixture"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-EXACT-001"
  , testSpecClaim =
      "For the deterministic bounded in-memory phil-runtime/phase0/transport-exact-receive-v1 smoke fixture, exact receive consumes the explicit caller-supplied transport handle and requested UInt64 length; exact success copies the requested bytes into the returned opaque payload owner and generated UploadServer later releases that exact owner by identity; EarlyEOF returns the obtained partial bytes in a releasable owner and the generated failure path releases that exact partial owner; and the obsolete ambient length-only provider ABI rejects."
  , testSpecKind = "Explicit exact receive bounded-fixture behavior"
  , testSpecOrigin =
      "runtime/phase0/transport_exact_receive_v1.h; runtime/phase0/transport_exact_receive_v1_smoke.c; runtime/phase0/transport_exact_receive_v1_smoke_main.c; runtime/phase0/transport_exact_receive_v1_bad_ambient.c; scripts/check_runtime_abi.py"
  , testSpecScope = "transport-exact-receive-v1 bounded in-memory executable fixture"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over exact emitted/provider LLVM, linked executable, success/EarlyEOF observations, ambient-provider rejection, and execution log"
  , testSpecSubjects =
      [ "explicit caller-supplied transport handle"
      , "requested UInt64 length"
      , "exact-success payload bytes and owner identity"
      , "EarlyEOF partial-owner identity and cleanup"
      , "ambient length-only provider rejection"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/transport_exact_receive_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-exact-receive.ll"
      , "transport-exact-receive-runtime.ll"
      , "transport-exact-receive-bad-ambient.ll"
      , "phase0-upload-exact-receive-linked.bc"
      , "phase0-upload-exact-receive-smoke"
      , "runtime/phase0/transport_exact_receive_v1.h"
      , "runtime/phase0/transport_exact_receive_v1_smoke.c"
      , "runtime/phase0/transport_exact_receive_v1_bad_ambient.c"
      , "scripts/check_runtime_abi.py"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/RemainingRuntimeTestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:transport-exact-receive-v1:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-EXACT-001:v2"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-EXACT-001.differential.fixture.v2"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: explicit transport exact receive copies the requested payload and releases its owner by identity"
      , "PASS: early EOF returns a partial payload owner and the generated failure path releases that exact handle"
      , "PASS: runtime ABI checker rejects ambient length-only exact receive"
      ]
  , testSpecForbiddenMarkers =
      [ "did not preserve owner/dataflow"
      , "did not release the returned partial owner"
      , "expected ABI checker to reject"
      ]
  , testSpecValidity = runtimeFixtureValidity "transport-exact-receive-v1/bounded-memory-smoke/v2"
  , testSpecProducer = "transport-exact-receive-v1 ABI comparison + bounded success/EarlyEOF executable smoke + ambient-provider rejection"
  , testSpecCheckerProfile =
      "LLVM/Clang 18; scripts/check_runtime_abi.py; native transport_exact_receive_v1_smoke_main.c execution; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "The certified claim is deliberately limited to the bounded in-memory fixture. malloc/free, C/Clang/LLVM 18, host execution, fixture instrumentation, and opaque runtime ownership semantics remain test boundaries. Production sockets/files/TLS, framing/recognition, deadlines/cancellation, digest/storage/send, malicious-provider memory safety, and arbitrary ABI-conforming providers are outside this revision."
  }

runtimeStorageFixtureCertificationSpec :: TestEvidenceCertificationSpec
runtimeStorageFixtureCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-storage-fixture"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-STORAGE-001"
  , testSpecClaim =
      "For the deterministic phil-runtime/phase0/storage-v1 smoke fixture, storage receives the exact payload owner produced by the fixture pipeline after successful digest validation, persists the exact payload bytes on status-1 success, consumes the transferred owner on success and ordinary failure without a generated double release, and causes generated UploadServer to fail closed for reserved status 2 even when fault injection supplies a non-null UploadId; the obsolete ambient nullary storage provider ABI rejects."
  , testSpecKind = "Storage deterministic-fixture persistence and ownership"
  , testSpecOrigin =
      "runtime/phase0/storage_v1.h; runtime/phase0/storage_v1_smoke.c; runtime/phase0/storage_v1_smoke_main.c; runtime/phase0/storage_v1_bad_ambient.c; scripts/check_runtime_abi.py"
  , testSpecScope = "storage-v1 deterministic executable smoke fixture"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over exact emitted/provider LLVM, linked executable, success/failure/reserved-status observations, ambient-provider rejection, and execution log"
  , testSpecSubjects =
      [ "exact persisted payload bytes"
      , "transferred payload-owner consumption on success"
      , "transferred payload-owner consumption on ordinary failure"
      , "reserved status 2 fail-closed with non-null UploadId"
      , "ambient nullary storage provider rejection"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/storage_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-storage.ll"
      , "storage-runtime.ll"
      , "storage-bad-ambient.ll"
      , "phase0-upload-storage-linked.bc"
      , "phase0-upload-storage-smoke"
      , "runtime/phase0/storage_v1.h"
      , "runtime/phase0/storage_v1_smoke.c"
      , "runtime/phase0/storage_v1_bad_ambient.c"
      , "scripts/check_runtime_abi.py"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/RemainingRuntimeTestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:storage-v1:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-STORAGE-001:v2"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-STORAGE-001.differential.fixture.v2"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: storage persists the exact received payload, consumes its owner, and reaches accepted"
      , "PASS: storage failure consumes the exact payload owner without a generated double release"
      , "PASS: reserved storage status fails closed even when fault injection supplies a non-null UploadId"
      , "PASS: runtime ABI checker rejects ambient nullary storage"
      ]
  , testSpecForbiddenMarkers =
      [ "storage success smoke assertion failed"
      , "storage failure ownership assertion failed"
      , "reserved storage status fail-closed assertion failed"
      , "expected ABI checker to reject"
      ]
  , testSpecValidity = runtimeFixtureValidity "storage-v1/deterministic-smoke/v2"
  , testSpecProducer = "storage-v1 ABI comparison + deterministic persistence/ownership executable smoke + ambient-provider rejection"
  , testSpecCheckerProfile =
      "LLVM/Clang 18; scripts/check_runtime_abi.py; native storage_v1_smoke_main.c execution; libcrypto fixture pipeline; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "The certified claim is limited to the deterministic smoke fixture. C allocation/free and instrumentation, host process behavior, C/Clang/LLVM 18, provider-side ownership discipline, opaque UploadId representation/lifetime, and libcrypto fixture dependencies remain test boundaries. Crash consistency, durability, concurrency, production storage backends, UploadId wire encoding, and arbitrary ABI-conforming providers are outside this revision."
  }

runtimeAcceptedFixtureCertificationSpec :: TestEvidenceCertificationSpec
runtimeAcceptedFixtureCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-accepted-fixture"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-ACCEPTED-001"
  , testSpecClaim =
      "For the deterministic phil-runtime/phase0/accepted-response-v1 smoke fixture, the accepted path consumes the explicit server transport and fixture storage-produced UploadId handle and emits exactly 17 payload octets 0x01 || a0 a1 ... af; storage status 0 with null UploadId and reserved status 2 with deliberately non-null UploadId emit zero accepted-response bytes; and the obsolete ambient/nullary accepted-response provider ABI rejects."
  , testSpecKind = "Accepted response deterministic-fixture wire encoding"
  , testSpecOrigin =
      "runtime/phase0/accepted_response_v1.h; runtime/phase0/accepted_response_v1_smoke.c; runtime/phase0/accepted_response_v1_smoke_main.c; runtime/phase0/accepted_response_v1_bad_ambient.c; scripts/check_runtime_abi.py"
  , testSpecScope = "accepted-response-v1 deterministic executable smoke fixture"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over exact emitted/provider LLVM, linked executable, exact 17-octet payload, non-emission cases, ambient-provider rejection, and execution log"
  , testSpecSubjects =
      [ "explicit server transport"
      , "fixture UploadId token a0..af"
      , "exact accepted payload 0x01 || UploadIdToken[16]"
      , "zero accepted bytes on status 0/null UploadId"
      , "zero accepted bytes on reserved status 2/non-null UploadId"
      , "ambient/nullary accepted-response provider rejection"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/accepted_response_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-accepted-response.ll"
      , "accepted-response-runtime.ll"
      , "accepted-response-bad-ambient.ll"
      , "phase0-upload-accepted-response-linked.bc"
      , "phase0-upload-accepted-response-smoke"
      , "runtime/phase0/accepted_response_v1.h"
      , "runtime/phase0/accepted_response_v1_smoke.c"
      , "runtime/phase0/accepted_response_v1_bad_ambient.c"
      , "scripts/check_runtime_abi.py"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/RemainingRuntimeTestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:accepted-response-v1:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-ACCEPTED-001:v2"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-ACCEPTED-001.differential.fixture.v2"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: select accepted(id) encodes exactly 0x01 followed by the 16-octet UploadId token on the exact transport"
      , "PASS: conforming storage failure returns null UploadId and emits no accepted response"
      , "PASS: reserved storage status with a non-null UploadId still emits no accepted response"
      , "PASS: runtime ABI checker rejects ambient nullary accepted-response encoding"
      ]
  , testSpecForbiddenMarkers =
      [ "accepted response success assertion failed"
      , "storage failure accepted-response assertion failed"
      , "reserved storage status accepted-response assertion failed"
      , "expected ABI checker to reject"
      ]
  , testSpecValidity = runtimeFixtureValidity "accepted-response-v1/deterministic-smoke/v2"
  , testSpecProducer = "accepted-response-v1 ABI comparison + deterministic exact-wire executable smoke + ambient-provider rejection"
  , testSpecCheckerProfile =
      "LLVM/Clang 18; scripts/check_runtime_abi.py; native accepted_response_v1_smoke_main.c execution; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "The certified claim is limited to the deterministic fixture and its private UploadId token. C/Clang/LLVM 18, provider-side UploadId representation and encoder implementation, host execution, fixture instrumentation, and libcrypto pipeline dependencies remain test boundaries. Physical write success, outer framing/packetization, UploadId freshness/uniqueness, transport behavior, production I/O, and arbitrary ABI-conforming providers are outside this revision."
  }

runtimeRejectedFixtureCertificationSpec :: TestEvidenceCertificationSpec
runtimeRejectedFixtureCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-rejected-fixture"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-REJECTED-001"
  , testSpecClaim =
      "For the deterministic phil-runtime/phase0/rejected-response-v1 smoke fixture, a real SHA-256 digest-mismatch path releases the exact received payload owner before rejected-response emission, reaches neither storage nor accepted-response emission, passes the exact transport and canonical DigestMismatch reason code to the fixture encoder, emits exactly 0x00 0x01, and rejects the obsolete ambient/nullary rejected-response provider ABI."
  , testSpecKind = "Rejected response deterministic-fixture reason encoding"
  , testSpecOrigin =
      "runtime/phase0/rejected_response_v1.h; runtime/phase0/rejected_response_v1_smoke.c; runtime/phase0/rejected_response_v1_smoke_main.c; runtime/phase0/rejected_response_v1_bad_ambient.c; scripts/check_runtime_abi.py"
  , testSpecScope = "rejected-response-v1 deterministic executable smoke fixture"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over exact emitted/provider LLVM, linked executable, real digest mismatch, exact 00 01 payload, ambient-provider rejection, and execution log"
  , testSpecSubjects =
      [ "real SHA-256 mismatch fixture path"
      , "exact received payload-owner release before emission"
      , "no storage or accepted-response emission"
      , "exact transport and canonical DigestMismatch reason"
      , "exact rejected payload 0x00 0x01"
      , "ambient/nullary rejected-response provider rejection"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/rejected_response_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-rejected-response.ll"
      , "rejected-response-runtime.ll"
      , "rejected-response-bad-ambient.ll"
      , "phase0-upload-rejected-response-linked.bc"
      , "phase0-upload-rejected-response-smoke"
      , "runtime/phase0/rejected_response_v1.h"
      , "runtime/phase0/rejected_response_v1_smoke.c"
      , "runtime/phase0/rejected_response_v1_bad_ambient.c"
      , "scripts/check_runtime_abi.py"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/RemainingRuntimeTestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:rejected-response-v1:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-REJECTED-001:v2"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-REJECTED-001.differential.fixture.v2"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: digest mismatch releases the exact payload owner then emits 00 01 on the exact transport"
      , "PASS: runtime ABI checker rejects ambient nullary rejected-response encoding"
      ]
  , testSpecForbiddenMarkers =
      [ "FAIL:"
      , "expected ABI checker to reject"
      ]
  , testSpecValidity = runtimeFixtureValidity "rejected-response-v1/deterministic-smoke/v2"
  , testSpecProducer = "rejected-response-v1 ABI comparison + real-digest-mismatch exact-wire executable smoke + ambient-provider rejection"
  , testSpecCheckerProfile =
      "LLVM/Clang 18; scripts/check_runtime_abi.py; native rejected_response_v1_smoke_main.c execution; libcrypto SHA256 fixture setup; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "The certified claim is limited to the deterministic fixture. C/Clang/LLVM 18, libcrypto/provider correctness, host execution, fixture instrumentation, physical write success, outer framing/packetization, transport behavior, and production I/O remain explicit test/runtime boundaries. This revision does not quantify over arbitrary ABI-conforming providers."
  }

runtimeFixtureValidity :: Text -> ValidityScope
runtimeFixtureValidity checkerProfile = ValidityScope (Map.fromList
  [ ("evidence_kind", "DifferentialTested")
  , ("checker_profile", checkerProfile)
  , ("llvm_version", "18")
  , ("clang_version", "18")
  , ("target_triple", "x86_64-unknown-linux-gnu")
  , ("certificate_profile", "test-evidence-certificate/v1")
  ])
