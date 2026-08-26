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
      certifyWith phase1CallableLifecycleCertificationSpec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1CallableLifecycleCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1CallableLifecycleCertificationSpec :: RocqCertificationSpec
phase1CallableLifecycleCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-callable-lifecycle"
  , rocqSpecObligation = ObligationId "PHIL-CALL-LIFE-001"
  , rocqSpecClaim =
      "Callable availability is keyed by exact ownership occurrence independently of public callable interface identity. PreserveCallee retains the exact predecessor and requires exact restricted-capture residue with no successor; ConsumeCallee requires no retained predecessor residue or successor and removes the predecessor; ReplaceCallee requires no retained predecessor residue and exactly one fresh, distinct successor matching the declared interface revision and state identity, removes the predecessor, installs the successor, and never resurrects the predecessor merely because the public interface is equal."
  , rocqSpecKind = "Callable lifecycle, ownership occurrence, and callee transition"
  , rocqSpecOrigin =
      "src/Phil/Core/Callable.hs::{invokeCallableOccurrence,singletonCallableResourceState,lookupCallableOccurrence}; test/Phase1CallableTransitionsMain.hs; proof/Phil/Core/CallableMode.v; proof/Phil/Core/CallableLifecycle.v"
  , rocqSpecScope =
      "Phase 1 CALL-006 through CALL-009 PreserveCallee, ConsumeCallee, and ReplaceCallee ownership semantics"
  , rocqSpecRepresentation =
      "normalized callable occurrence atoms, extensional availability/capture predicates, optional successor records, exact interface atoms, and explicit optional state indices"
  , rocqSpecSubjects =
      [ "CallableOccurrenceKey"
      , "CallableStateKey"
      , "CalleeTransition"
      , "CallableOccurrence"
      , "CallableResourceState"
      , "CallableInvocationBodySummary"
      , "ClosureCaptureSummary.restricted residue"
      ]
  , rocqSpecTheorems =
      [ "preserve_requires_exact_restricted_residue"
      , "preserve_rejects_missing_restricted_capture"
      , "preserve_rejects_successor"
      , "preserve_keeps_resource_state_exact"
      , "preserve_keeps_predecessor_available"
      , "preserving_invocation_is_repeatable"
      , "consume_requires_empty_restricted_residue"
      , "consume_rejects_retained_restricted_capture"
      , "consume_rejects_successor"
      , "consume_removes_predecessor"
      , "consume_preserves_other_occurrences"
      , "consumed_predecessor_cannot_be_reused"
      , "replace_requires_successor"
      , "replace_requires_distinct_successor_occurrence"
      , "replace_requires_fresh_successor_occurrence"
      , "replace_requires_exact_successor_interface"
      , "replace_requires_exact_successor_state"
      , "replace_rejects_missing_successor"
      , "replace_rejects_predecessor_key_reuse"
      , "replace_rejects_already_available_successor"
      , "replace_rejects_interface_mismatch"
      , "replace_rejects_state_mismatch"
      , "replacement_installs_successor"
      , "replacement_removes_predecessor"
      , "replacement_preserves_unrelated_occurrences"
      , "equal_interface_replacement_does_not_resurrect_predecessor"
      , "equal_interface_does_not_identify_occurrences"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/CallableLifecycle.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/CallableLifecycle.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-LIFE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-LIFE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-CALL-MODE-001 supplies the restricted capture identities whose exact post-body residue is consumed here. Rocq kernel/toolchain correctness and reviewed correspondence from concrete CallableOccurrenceKey/CallableStateKey/InterfaceRevision/Text identities, Haskell Map lookup/delete/insert/freshness, Set equality/emptiness, Maybe successor representation, and exact transition diagnostics to the normalized model remain explicit trust boundaries. Complete per-outcome resource redistribution, callable body correctness, scoped-loan escape, authority/evidence semantics, source syntax, recursion, provider/foreign qualification, target closure conversion, ABI details, and runtime enforcement remain outside this theorem family."
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
