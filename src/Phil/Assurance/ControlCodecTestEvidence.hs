{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.ControlCodecTestEvidence
  ( controlCodecRuntimeCertificationSpec
  , controlCodecRuntimeInputPaths
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

controlCodecRuntimeCertificationSpec :: TestEvidenceCertificationSpec
controlCodecRuntimeCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "control-codec-runtime"
  , testSpecObligation = ObligationId "PHIL-RUNTIME-CONTROL-CODEC-001"
  , testSpecClaim =
      "For the exact Phase 0 control-codec-v1 shared native provider and deterministic fixture suite, the emitted control-codec LLVM ABI matches the compiled provider signatures under the partial ABI checker, Hello serializes to and round-trips from its exact canonical frame, Begin serializes to and round-trips from its exact canonical frame while preserving the full-width length/kind/digest operands, concatenated frames commit one exact frame at a time, malformed framing is rejected, frame-valid grammar-invalid Hello and Begin payloads produce grammar-specific recognition failures without advancing the transport, and the existing payload/version operand-identity helpers preserve exact handle identity."
  , testSpecKind = "Control codec deterministic native fixture conformance"
  , testSpecOrigin =
      "runtime/phase0/control_codec_v1.h; runtime/phase0/control_codec_v1.c; runtime/phase0/control_codec_v1_smoke.c; runtime/phase0/control_codec_v1_smoke_main.c; scripts/check_runtime_abi.py"
  , testSpecScope = "control-codec-v1 deterministic shared-provider fixture suite"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over emitted/provider LLVM, linked bitcode, exact native executable bytes, codec sources, and successful execution log"
  , testSpecSubjects =
      [ "exact canonical Hello frame bytes and round trip"
      , "exact canonical Begin frame bytes and round trip"
      , "full-width Begin length plus exact opaque kind and SHA-256 digest bytes"
      , "concatenated-frame exact commit boundaries"
      , "magic/version/tag/truncation framing rejection"
      , "grammar-specific Hello recognition failure without transport advance"
      , "grammar-specific Begin recognition failure without transport advance"
      , "payload length/kind/digest and supported-version handle identity helpers"
      , "emitted/provider LLVM result/argument/arity compatibility for provided symbols"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "runtime/phase0/control_codec_v1_smoke_main.c"
  , testSpecInputRefs = map ArtifactRef controlCodecRuntimeInputPaths
  , testSpecResultRef = ArtifactRef "artifact:phil:runtime:phase0:control-codec-v1:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-RUNTIME-CONTROL-CODEC-001:v1"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RUNTIME-CONTROL-CODEC-001.differential.v1"
  , testSpecExpectedMarkers =
      [ "PASS: runtime provider matches "
      , "Phil LLVM ABI signature(s)"
      , "PASS: control-codec-v1 native fixture suite"
      ]
  , testSpecForbiddenMarkers = ["FAIL:", "expected control codec fixture suite to pass"]
  , testSpecValidity = ValidityScope (Map.fromList
      [ ("evidence_kind", "DifferentialTested")
      , ("checker_profile", "control-codec-v1/shared-native-fixtures/v1")
      , ("llvm_version", "18")
      , ("clang_version", "18")
      , ("target_triple", "x86_64-unknown-linux-gnu")
      , ("runtime_abi_profile", "phil-runtime/phase0/control-codec-v1")
      , ("certificate_profile", "test-evidence-certificate/v1")
      ])
  , testSpecProducer =
      "control-codec-v1 emitted/provider LLVM ABI comparison + linked shared-provider native fixture execution"
  , testSpecCheckerProfile =
      "scripts/check_runtime_abi.py --partial + Clang/LLVM 18 + control_codec_v1_smoke_main.c successful execution; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "This certification establishes only the exact deterministic fixture claim bound to the listed source/generated artifacts and executable bytes. It is not a universal proof of the C codec, allocator behavior, pointer lifetime, all malformed inputs, operating-system transport I/O, compiler correctness, or cryptographic SHA-256 computation. The C implementation/harness, Clang/LLVM 18, host execution, libc allocation/memory primitives, ABI checker, and test-evidence certifier/manifest verifier remain explicit trust boundaries."
  }

controlCodecRuntimeInputPaths :: [Text]
controlCodecRuntimeInputPaths =
  [ "phase0-control-codec.ll"
  , "control-codec-runtime.ll"
  , "phase0-control-codec-partially-linked.bc"
  , "control-codec-smoke"
  , "runtime/phase0/control_codec_v1.h"
  , "runtime/phase0/control_codec_v1.c"
  , "runtime/phase0/control_codec_v1_smoke.c"
  , "docs/phase-0/control-codec-v1.md"
  , "src/Phil/LLVM/ControlCodec.hs"
  , "src/Phil/LLVM/IR.hs"
  , "scripts/check_runtime_abi.py"
  , "src/Phil/Assurance/TestEvidenceCertification.hs"
  , "src/Phil/Assurance/ControlCodecTestEvidence.hs"
  , "src/Phil/Assurance/Verify.hs"
  ]
