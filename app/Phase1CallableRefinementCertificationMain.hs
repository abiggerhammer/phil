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
      hPutStrLn stderr
        "usage: CERTIFIER SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

certificationSpec :: RocqCertificationSpec
certificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-callable-refinement"
  , rocqSpecObligation = ObligationId "PHIL-CALL-REFINE-001"
  , rocqSpecClaim =
      "An actual callable may substitute for an expected callable only with exact machine shape, no stronger caller-authority requirement, no wider public may-effect or modeled failure set, and the exact callee lifecycle transition; callable interface revision identity remains distinct from checked substitutability."
  , rocqSpecKind = "Callable higher-order semantic refinement and non-widening"
  , rocqSpecOrigin =
      "src/Phil/Core/CallableRefinement.hs; test/Phase1CallableRefinementMain.hs; proof/Phil/Core/CallableEffects.v; proof/Phil/Core/CallableLifecycle.v; proof/Phil/Core/CallableRefinement.v"
  , rocqSpecScope =
      "Phase 1 CALL-012 higher-order callable semantic refinement"
  , rocqSpecRepresentation =
      "opaque interface and machine-shape atoms, extensional authority/effect/failure sets, and explicit callee transition identity"
  , rocqSpecSubjects =
      [ "CallableRefinementSurface"
      , "CallableMachineShape"
      , "CallableAuthorityRequirement"
      , "SemanticEffect"
      , "CallableFailure"
      , "CalleeTransition"
      ]
  , rocqSpecTheorems =
      [ "set_subset_reflexive"
      , "set_subset_transitive"
      , "callable_refinement_is_reflexive"
      , "callable_refinement_is_transitive"
      , "refinement_preserves_machine_shape"
      , "refinement_never_strengthens_caller_authority"
      , "refinement_never_widens_effects"
      , "refinement_never_adds_failures"
      , "refinement_requires_exact_callee_transition"
      , "distinct_interface_revisions_may_refine"
      , "interface_revision_is_noninterfering"
      , "narrower_actual_is_admissible"
      , "stronger_authority_cannot_refine"
      , "wider_effect_cannot_refine"
      , "extra_failure_cannot_refine"
      , "lifecycle_adaptation_is_never_implicit"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/CallableRefinement.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/CallableRefinement.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-REFINE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-REFINE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-CALL-EFFECT-001 and PHIL-CALL-LIFE-001 supply the effect-bound and lifecycle semantic foundations consumed here; PHIL-CALL-MODE-001 supplies their restricted-capture predecessor. Rocq kernel/toolchain correctness and reviewed correspondence from concrete Text/Set identities, CallableMachineShape construction, Haskell Set subset/difference/canonicalization, failure representation, checker ordering, and exact diagnostics remain explicit trust boundaries. Preconditions, result guarantees, resource telescopes, assumptions, costs, final syntax, target closure conversion, ABI lowering, and runtime enforcement remain outside this theorem family."
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
      putStrLn
        ("certified " <> Text.unpack obligation <>
          " as ProofAssistantTheorem evidence")
      putStrLn
        ("certificate artifact: " <>
          Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn
        ("certificate sha256: " <>
          Text.unpack (unDigest (artifactDigest artifact)))
