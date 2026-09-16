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
      certifyWith phase1CallableEffectCertificationSpec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1CallableEffectCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1CallableEffectCertificationSpec :: RocqCertificationSpec
phase1CallableEffectCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-callable-effect"
  , rocqSpecObligation = ObligationId "PHIL-CALL-EFFECT-001"
  , rocqSpecClaim =
      "Possessing, passing, storing, or returning a callable does not propagate its invocation effects; reachable invocation contributes the callable's exact stabilized public may-effect bound by canonical set union. A callable implementation may have an equal or narrower inferred effect footprint while retaining the exact public interface and public bound, but any inferred effect absent from that bound rejects with the exact undeclared effect delta rather than silently widening or revising the public contract."
  , rocqSpecKind = "Callable invocation effect propagation and public effect-bound refinement"
  , rocqSpecOrigin =
      "src/Phil/Core/Callable.hs::{inferReachableCallableEffects,checkCallableEffectBound}; test/Phase1CallableCaptureEffectsMain.hs; test/Phase1CallableEffectBoundMain.hs; proof/Phil/Core/CallableEffects.v"
  , rocqSpecScope =
      "Phase 1 CALL-004, CALL-005, and CALL-011 callable may-effect semantics"
  , rocqSpecRepresentation =
      "extensional semantic effect predicates, canonical union, reachable callable-use events, and exact inferred/public checked effect surfaces"
  , rocqSpecSubjects =
      [ "SemanticEffect"
      , "CallableUse"
      , "CallableContract.effectBound"
      , "CheckedCallableEffects"
      , "InterfaceRevision"
      ]
  , rocqSpecTheorems =
      [ "possession_is_effect_neutral"
      , "pass_store_return_are_effect_neutral"
      , "reachable_invocation_adds_exact_public_bound"
      , "repeated_invocation_is_idempotent"
      , "two_invocation_effect_union_is_order_independent"
      , "effect_union_is_commutative"
      , "effect_union_is_associative"
      , "every_effect_set_is_subset_of_itself"
      , "empty_footprint_is_subset_of_every_public_bound"
      , "subset_footprint_constructs_checked_effect_bound"
      , "accepted_effect_check_preserves_interface_identity"
      , "accepted_effect_check_preserves_inferred_footprint"
      , "accepted_effect_check_preserves_stabilized_public_bound"
      , "narrower_body_may_satisfy_wider_public_bound"
      , "undeclared_effect_witness_rejects_bound"
      , "effect_delta_is_exact_undeclared_set"
      , "effect_neutral_higher_order_use_fits_pure_bound"
      , "invocation_widening_cannot_silently_revise_enclosing_bound"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/CallableEffects.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/CallableEffects.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-EFFECT-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-EFFECT-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness and reviewed correspondence from concrete SemanticEffect/Text identities, Haskell Set union/subset/difference/canonicalization, checked control-flow reachability, list traversal, InterfaceRevision representation, and exact widening diagnostics to the normalized extensional model remain explicit trust boundaries. Provider/foreign effects remain constrained by provider qualification. Callable lifecycle/resource transitions, authority, assumptions, final syntax, target closure conversion, and target/runtime effect enforcement remain outside this theorem family."
  }

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
  sourceBytes <- ByteString.readFile sourcePath
  compiledBytes <- ByteString.readFile compiledPath
  case packageTrustedRocqProof spec sourceBytes compiledBytes of
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
