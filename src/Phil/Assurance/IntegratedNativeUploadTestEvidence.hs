{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.IntegratedNativeUploadTestEvidence
  ( integratedNativeUploadCertificationSpec
  , integratedNativeUploadInputPaths
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

integratedNativeUploadCertificationSpec :: TestEvidenceCertificationSpec
integratedNativeUploadCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "phase0-integrated-native-upload"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-INTEGRATED-UPLOAD-001"
  , testSpecClaim =
      "For the exact frozen Phase 0 UploadClient/UploadServer source pair, source-to-Systems projection, source-bound control-codec-v1 LLVM target, unchanged shared control-codec provider, in-memory integrated runtime provider, and deterministic native driver, the complete generated/runtime ABI matches all 46 Phil LLVM signatures and native execution exhibits the accepted-upload, digest-rejection, and client-cancellation scenarios with the exact fixture checks encoded by the driver. This is fixture-scoped DifferentialTested evidence, not a universal theorem about native execution, scheduling, networking, persistence, cryptography, or the C runtime."
  , testSpecKind = "Phase 0 integrated native upload execution conformance"
  , testSpecOrigin =
      "examples/upload/client.phil; examples/upload/server.phil; phase0-projection/src/Phil/Phase0UploadProjection.hs; phase0-projection/app/LLVMMain.hs; runtime/phase0/control_codec_v1.c; runtime/phase0/integrated_upload_v1.c; runtime/phase0/integrated_upload_v1_main.c; scripts/check_runtime_abi.py; docs/phase-0/integrated-native-upload-v1.md"
  , testSpecScope =
      "frozen Phase 0 upload reference program executed natively with the exact in-memory loopback fixture on x86_64-unknown-linux-gnu"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over the exact source pair, projection/emitter sources, generated source-bound LLVM/bitcode, provider sources and LLVM/bitcode, complete ABI checker, linked native executable bytes, and successful execution log"
  , testSpecSubjects =
      [ "complete generated/runtime ABI compatibility for all 46 Phil LLVM signatures"
      , "accepted upload reaches exact payload transfer, SHA-256 validation, storage, accepted response, and exact UploadId observation"
      , "digest rejection transfers the payload, rejects the mismatching digest, releases the payload, performs no storage, and returns the rejected response"
      , "client cancellation occurs after negotiation/proceed with no payload transfer, digest validation, storage, or final response"
      , "exact frozen source pair remains embedded in the emitted source-bound LLVM identity"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/integrated_upload_v1_main.c"
  , testSpecInputRefs = map ArtifactRef integratedNativeUploadInputPaths
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:integrated-native-upload:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-INTEGRATED-UPLOAD-001:v1"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-INTEGRATED-UPLOAD-001.differential.v1"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches 46 Phil LLVM ABI signature(s)"
      , "PASS: accepted upload"
      , "PASS: digest rejection"
      , "PASS: client cancellation"
      ]
  , testSpecForbiddenMarkers = ["FAIL:"]
  , testSpecValidity = ValidityScope (Map.fromList
      [ ("evidence_kind", "DifferentialTested")
      , ("checker_profile", "phase0-integrated-native-upload/v1")
      , ("source_pair_digest", "5339e6c7e6520e5495c1d304edcc2427e4bdbe19ce80167af3a314ab2f69e4df")
      , ("source_projection", "surface-to-systems/phase0-upload/v1")
      , ("runtime_abi_profile", "phil-runtime/phase0/control-codec-v1")
      , ("llvm_version", "18")
      , ("clang_version", "18")
      , ("target_triple", "x86_64-unknown-linux-gnu")
      , ("transport_fixture", "in-memory-loopback")
      , ("threading_fixture", "pthreads")
      , ("sha256_fixture", "OpenSSL")
      , ("certificate_profile", "test-evidence-certificate/v1")
      ])
  , testSpecProducer =
      "source-bound LLVM emission + full scripts/check_runtime_abi.py comparison + linked native UploadClient/UploadServer execution"
  , testSpecCheckerProfile =
      "GHC 9.6.7; LLVM/Clang 18; scripts/check_runtime_abi.py full mode; integrated_upload_v1_main.c; pthreads; OpenSSL libcrypto; successful exit plus exact PASS markers; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "This certification establishes only the exact integrated in-memory native fixture claim. It is not a universal proof of the C providers, pthread scheduling or fairness, allocator/pointer lifetime, OpenSSL SHA-256 correctness, operating-system behavior, LLVM/Clang correctness, generic networking/socket behavior, crash durability, filesystem persistence, remote receipt, or a generic Phil runtime. The Haskell projection/emitter, C provider/driver, ABI checker, compiler/linker, host kernel/libc/libpthread/libcrypto, native execution, and test-evidence certifier/manifest verifier remain explicit trust boundaries."
  }

integratedNativeUploadInputPaths :: [Text]
integratedNativeUploadInputPaths =
  [ "examples/upload/client.phil"
  , "examples/upload/server.phil"
  , "phase0-projection/src/Phil/Phase0UploadProjection.hs"
  , "phase0-projection/app/LLVMMain.hs"
  , "phase0-projection/phil-phase0-projection.cabal"
  , "phase0-source-bound.ll"
  , "phase0-source-bound.bc"
  , "runtime/phase0/control_codec_v1.h"
  , "runtime/phase0/control_codec_v1.c"
  , "runtime/phase0/integrated_upload_v1.h"
  , "runtime/phase0/integrated_upload_v1.c"
  , "control-codec-provider.ll"
  , "integrated-upload-provider.ll"
  , "integrated-upload-main.ll"
  , "integrated-provider.ll"
  , "integrated-provider.bc"
  , "phase0-integrated-upload.bc"
  , "phase0-integrated-upload"
  , "scripts/check_runtime_abi.py"
  , "docs/phase-0/integrated-native-upload-v1.md"
  , "src/Phil/Assurance/TestEvidenceCertification.hs"
  , "src/Phil/Assurance/IntegratedNativeUploadTestEvidence.hs"
  , "src/Phil/Assurance/Verify.hs"
  ]
