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
    [sourcePath, compiledPath, outputPath] ->
      certifyWith certificationSpec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr "usage: CERTIFIER SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

certificationSpec :: RocqCertificationSpec
certificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-context-join"
  , rocqSpecObligation = ObligationId "PHIL-CTX-JOIN-001"
  , rocqSpecClaim =
      "Every successful continuing ResourceContext join is loan-free, converges unrestricted and linear bindings exactly across all continuing inputs, and retains an affine binding exactly when the first branch and every remaining branch retain that binding at the same type under the implemented left-fold semantics."
  , rocqSpecKind = "Resource context join and conservative structural residue"
  , rocqSpecOrigin =
      "src/Phil/Core/Context.hs::{joinContinuing,ensureNoEscapingLoans,ensureSameUnrestricted,ensureSameLinear,intersectAffine}; test/Main.hs; proof/Phil/Core/Context.v; proof/Phil/Core/ContextJoin.v; proof/Phil/Core/ContextJoinCertification.v"
  , rocqSpecScope =
      "Phase 1 continuing Γ/A/Δ ResourceContext join semantics"
  , rocqSpecRepresentation =
      "proof-oriented extensional ResourceContext model with the actual affine left-fold survival relation"
  , rocqSpecSubjects =
      [ "ResourceContext"
      , "unrestrictedBindings"
      , "affineBindings"
      , "linearBindings"
      , "sharedLoans"
      , "joinContinuing"
      ]
  , rocqSpecTheorems =
      [ "certified_context_join_inputs_have_no_loans"
      , "certified_context_join_output_has_no_loans"
      , "certified_context_join_unrestricted_converges"
      , "certified_context_join_linear_converges"
      , "certified_context_join_affine_some_exact"
      , "certified_context_join_affine_retained_is_common"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ContextJoinCertification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ContextJoinCertification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CTX-JOIN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CTX-JOIN-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "The certified wrapper reuses the landed ContextJoin.v theorems directly and introduces no second join relation. That landed model follows the successful path through the current Haskell left fold, including its asymmetry: once an affine name has dropped from the accumulated intersection, later differences at that name are irrelevant. Rocq kernel/toolchain correctness and reviewed correspondence from concrete Name/Ty equality, Haskell Map/Set representation, Map.intersection and firstTypeMismatch behavior, list-fold evaluation, and exact CheckError diagnostic selection remain explicit trust boundaries. Process control-path selection and terminal-path exclusion belong to PHIL-PROC-JOIN-001."
  }

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
  sourceBytes <- ByteString.readFile sourcePath
  compiledBytes <- ByteString.readFile compiledPath
  case certifyRocqProof spec sourceBytes compiledBytes of
    Left err -> do
      hPutStrLn stderr ("Rocq certification failed: " <> show err)
      exitFailure
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
          ObligationId obligation = rocqCertificateObligation certificate
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn ("certified " <> Text.unpack obligation <> " as ProofAssistantTheorem evidence")
      putStrLn ("certificate artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn ("certificate sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))
