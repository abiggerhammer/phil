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
  { rocqSpecProfile = "phase1-foreign-callable-qualification"
  , rocqSpecObligation = ObligationId "PHIL-CALL-FOREIGN-001"
  , rocqSpecClaim = "A foreign callable is admissible only through explicit qualification bound to one exact foreign implementation artifact and one exact observed semantic surface, with independent evidence for ABI correspondence, resource/lifecycle behavior, effect confinement, authority confinement, and failure behavior. Missing evidence, cross-artifact reuse, or surface mismatch reject. Complete qualification still remains subject to ordinary callable refinement, so it cannot strengthen caller authority, widen effects, add failures, or alter callee lifecycle."
  , rocqSpecKind = "Exact foreign artifact qualification and semantic non-widening"
  , rocqSpecOrigin = "src/Phil/Core/CallableQualification.hs; test/Phase1ForeignCallableQualificationMain.hs; docs/phase-1/foreign-callable-qualification-v1.md; proof/Phil/Core/CallableRefinement.v; proof/Phil/Core/ForeignCallableQualification.v"
  , rocqSpecScope = "Phase 1 CALL-015 foreign callable qualification boundary"
  , rocqSpecRepresentation = "opaque exact foreign artifact identities, exact qualified/observed CallableRefinementSurface equality, five independent evidence dimensions, and certified CALL-012 callable refinement"
  , rocqSpecSubjects = ["ForeignCallableArtifactKey", "ForeignCallableQualification", "ForeignCallableEvidenceKind", "CallableRefinementSurface"]
  , rocqSpecTheorems =
      [ "accepted_qualification_is_bound_to_exact_artifact"
      , "cross_artifact_qualification_reuse_rejects"
      , "accepted_qualification_surface_is_exact"
      , "qualification_surface_mismatch_rejects"
      , "every_evidence_dimension_is_present"
      , "missing_any_evidence_dimension_rejects"
      , "qualification_does_not_bypass_callable_refinement"
      , "qualified_callable_never_strengthens_caller_authority"
      , "qualified_callable_never_widens_effects"
      , "qualified_callable_never_adds_failures"
      , "qualified_callable_preserves_callee_transition"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ForeignCallableQualification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ForeignCallableQualification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-FOREIGN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-FOREIGN-001.rocq.v1"
  , rocqSpecResidualBoundary = "PHIL-CALL-REFINE-001's certified CALL-012 theorem family supplies callable non-widening after qualification, while PHIL-AUTH-CONFINE-001 supplies the public/internal authority confinement foundation. Rocq kernel/toolchain correctness and reviewed correspondence from concrete ForeignCallableArtifactKey/Text identity, Haskell Map evidence coverage, exact artifact/surface equality, missing-evidence diagnostics, and checkCallableRefinement composition remain explicit trust boundaries. The semantic truth and competence of external evidence references, foreign-code analysis, runtime sandboxing/confinement, ABI evidence generation, provider-wide qualification, and final foreign-callable syntax remain explicit assurance/TCB boundaries rather than internally derived facts."
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
