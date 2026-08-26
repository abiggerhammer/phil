{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [sourcePath, compiledPath, outputPath] -> certifyWith certificationSpec sourcePath compiledPath outputPath
    _ -> hPutStrLn stderr "usage: CERTIFIER SOURCE.v COMPILED.vo OUTPUT.cert" >> exitFailure

certificationSpec :: RocqCertificationSpec
certificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-callable-lowering"
  , rocqSpecObligation = ObligationId "PHIL-CALL-LOWER-001"
  , rocqSpecClaim = "Callable target representation is nonsemantic. An accepted StageContract-side callable lowering preserves the complete source semantic projection exactly, including public callable surface, first-class occurrence, structural mode, capture semantics, internal authority, and live-loan scope, independently of pointer/symbol/tag/representation identity. Every target-introduced effect, failure, assumption, carrier, and attributable cost is explicitly and exactly represented in realization accounting; representation coincidence cannot repair semantic mismatch."
  , rocqSpecKind = "Callable lowering semantic preservation and complete realization accounting"
  , rocqSpecOrigin = "src/Phil/Systems/CallableLowering.hs; test/Phase1CallableLoweringMain.hs; docs/phase-1/callable-lowering-v1.md; proof/Phil/Core/CallableRefinement.v; proof/Phil/Core/CallableLowering.v"
  , rocqSpecScope = "Phase 1 CALL-016 bounded target callable representation-preservation case"
  , rocqSpecRepresentation = "exact source/target callable semantic records, opaque target representation and inspection identity, and exact target-introduced consequence accounting"
  , rocqSpecSubjects = ["SourceCallableLoweringFacts", "TargetCallableLoweringFacts", "CallableRealizationAccounting", "TargetCallableRepresentation"]
  , rocqSpecTheorems =
      [ "accepted_lowering_preserves_complete_source_projection"
      , "accepted_lowering_accounts_every_introduced_consequence_exactly"
      , "representation_choice_is_nonsemantic"
      , "representation_identity_cannot_repair_surface_mismatch"
      , "representation_identity_cannot_repair_occurrence_mismatch"
      , "representation_identity_cannot_repair_capture_mismatch"
      , "representation_identity_cannot_repair_loan_mismatch"
      , "unaccounted_effect_rejects"
      , "unaccounted_failure_rejects"
      , "unaccounted_assumption_rejects"
      , "unaccounted_carrier_rejects"
      , "unaccounted_cost_rejects"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/CallableLowering.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/CallableLowering.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-LOWER-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-LOWER-001.rocq.v1"
  , rocqSpecResidualBoundary = "The normalized theorem models the CALL-016 equality checks and complete realization-accounting shape in Phil.Systems.CallableLowering. Rocq kernel/toolchain correctness and reviewed correspondence from concrete InterfaceRevision/CallableOccurrenceKey/Mode/CaptureOccurrenceKey/LoanScopeKey identities, Haskell Map/Set extensional equality, CostShape equality, exact diagnostic ordering, and StageContract realization-accounting construction remain explicit trust boundaries. The semantic truth/admissibility of target-specific effects, failures, assumptions, carriers, and costs is governed by the wider StageContract/ADR-020 layer. Actual LLVM or other backend closure conversion, machine layout/ABI verification, runtime carrier enforcement, and backend code generation remain downstream obligations rather than part of this representation-preservation theorem."
  }

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
  sourceBytes <- ByteString.readFile sourcePath
  compiledBytes <- ByteString.readFile compiledPath
  case certifyRocqProof spec sourceBytes compiledBytes of
    Left err -> hPutStrLn stderr ("Rocq certification failed: " <> show err) >> exitFailure
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
          ObligationId obligation = rocqCertificateObligation certificate
      ByteString.writeFile outputPath (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn ("certified " <> Text.unpack obligation <> " as ProofAssistantTheorem evidence")
      putStrLn ("certificate artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn ("certificate sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))
