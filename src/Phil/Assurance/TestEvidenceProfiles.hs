{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.TestEvidenceProfiles
  ( knownPhase0TestEvidenceCertificationSpec
  , runtimeABICertificationSpec
  , runtimeSmokeCertificationSpec
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

knownPhase0TestEvidenceCertificationSpec :: Text -> Maybe TestEvidenceCertificationSpec
knownPhase0TestEvidenceCertificationSpec profile =
  case knownTestEvidenceCertificationSpec profile of
    Just spec -> Just spec
    Nothing
      | profile == testSpecProfile runtimeABICertificationSpec -> Just runtimeABICertificationSpec
      | profile == testSpecProfile runtimeSmokeCertificationSpec -> Just runtimeSmokeCertificationSpec
      | otherwise -> Nothing

runtimeABICertificationSpec :: TestEvidenceCertificationSpec
runtimeABICertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-abi"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-ABI-001"
  , testSpecClaim =
      "The Phase 0 recognized-record-v1 runtime provider used by the executable smoke path must match every emitted Phil phil_* declaration in LLVM result type, argument types, and arity before composition under the default calling convention; missing or incompatible definitions reject, including Begin.length : ptr -> i32 against the required ptr -> i64. Successful llvm-link alone is not accepted as ABI-conformance evidence."
  , testSpecKind = "Runtime ABI conformance"
  , testSpecOrigin =
      "scripts/check_runtime_abi.py; runtime/phase0/recognized_record_v1.h; runtime/phase0/recognized_record_v1_smoke.c; runtime/phase0/recognized_record_v1_bad_accessor.c"
  , testSpecScope = "recognized-record-v1 smoke provider ABI"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over emitted/provider LLVM signatures plus incompatible-provider rejection"
  , testSpecSubjects =
      [ "all emitted Phil phil_* declarations"
      , "recognized-record-v1 smoke provider definitions"
      , "result type / argument types / arity"
      , "Begin.length i64 width-drift rejection"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "scripts/check_runtime_abi.py"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-recognized-record.ll"
      , "recognized-record-runtime.ll"
      , "recognized-record-bad-accessor.ll"
      , "runtime/phase0/recognized_record_v1.h"
      , "runtime/phase0/recognized_record_v1_smoke.c"
      , "runtime/phase0/recognized_record_v1_bad_accessor.c"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/TestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:recognized-record-v1:abi-test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-ABI-001:v1"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-ABI-001.differential.v1"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: runtime ABI checker rejects i64 -> i32 accessor width drift"
      ]
  , testSpecForbiddenMarkers = ["expected ABI checker to reject"]
  , testSpecValidity = ValidityScope (Map.fromList
      [ ("evidence_kind", "DifferentialTested")
      , ("checker_profile", "check_runtime_abi.py/recognized-record-v1")
      , ("llvm_version", "18")
      , ("clang_version", "18")
      , ("target_triple", "x86_64-unknown-linux-gnu")
      , ("certificate_profile", "test-evidence-certificate/v1")
      ])
  , testSpecProducer = "recognized-record-v1 emitted/provider LLVM ABI comparison plus incompatible accessor mutation"
  , testSpecCheckerProfile =
      "scripts/check_runtime_abi.py over emitted/provider LLVM; LLVM/Clang 18; default calling convention; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "The checker parses the emitted textual LLVM forms used by this profile. Linkage and parameter/return attributes remain outside the current ABI dimensions and the default calling convention is assumed. Clang 18 C-to-LLVM lowering, checker correctness, and future ABI-affecting attributes/calling conventions remain explicit trust boundaries."
  }

runtimeSmokeCertificationSpec :: TestEvidenceCertificationSpec
runtimeSmokeCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "runtime-smoke"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-SMOKE-001"
  , testSpecClaim =
      "Linking the certified recognized-record ABI v1 UploadServer with the ABI-conforming Phase 0 smoke provider must execute the intended dependency: success status 1 causes exactly one Begin recognition, exactly one Begin.length accessor on the returned record, and exactly one receive_exact_u64 of the unchanged full-width sentinel 0x0102030405060708; reserved status 2 must fail closed before field access or exact receive."
  , testSpecKind = "Executable ABI smoke"
  , testSpecOrigin =
      "runtime/phase0/recognized_record_v1.h; runtime/phase0/recognized_record_v1_smoke.c; runtime/phase0/recognized_record_v1_smoke_main.c"
  , testSpecScope = "recognized-record-v1 deterministic executable smoke fixture"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over exact linked bitcode/executable and execution log"
  , testSpecSubjects =
      [ "status 1 recognized Begin path"
      , "unchanged full-width Begin.length sentinel 0x0102030405060708"
      , "exact Begin.length accessor dependency"
      , "reserved recognition status 2 fail-closed behavior"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/recognized_record_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef
      [ "phase0-upload-recognized-record.ll"
      , "recognized-record-runtime.ll"
      , "phase0-upload-recognized-record-linked.bc"
      , "phase0-upload-recognized-record-smoke"
      , "runtime/phase0/recognized_record_v1.h"
      , "runtime/phase0/recognized_record_v1_smoke.c"
      , "src/Phil/Assurance/TestEvidenceCertification.hs"
      , "src/Phil/Assurance/TestEvidenceProfiles.hs"
      , "src/Phil/Assurance/Verify.hs"
      ]
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:recognized-record-v1:smoke-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-SMOKE-001:v1"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-SMOKE-001.differential.v1"
  , testSpecExpectedMarkers =
      [ "PASS: recognized Begin.length reaches receive_exact_u64 as the same i64 value"
      , "PASS: malformed Begin recognition status fails closed before projection/receive"
      ]
  , testSpecForbiddenMarkers =
      [ "did not preserve Begin.length"
      , "did not fail closed before field access"
      ]
  , testSpecValidity = ValidityScope (Map.fromList
      [ ("evidence_kind", "DifferentialTested")
      , ("checker_profile", "recognized-record-v1/executable-smoke/v1")
      , ("llvm_version", "18")
      , ("clang_version", "18")
      , ("target_triple", "x86_64-unknown-linux-gnu")
      , ("certificate_profile", "test-evidence-certificate/v1")
      ])
  , testSpecProducer = "linked recognized-record-v1 UploadServer + deterministic smoke provider execution"
  , testSpecCheckerProfile =
      "LLVM/Clang 18 link + native execution of recognized_record_v1_smoke_main.c instrumentation; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "The provider is a deterministic smoke fixture. Transport, framing, policy, digest, storage, and most ordinary protocol calls remain stubs or no-ops. The C provider/harness, LLVM/Clang 18, host execution, and fixture instrumentation remain test boundaries; this does not establish production runtime correctness, record lifetime correctness, or real I/O semantics."
  }
