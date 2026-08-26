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
  { rocqSpecProfile = "phase1-resource-join"
  , rocqSpecObligation = ObligationId "PHIL-RES-JOIN-001"
  , rocqSpecClaim =
      "Continuing joins conserve linear ownership exactly. Core process joining admits only continuing ResourceContexts and normalizes every Continue path to one joined context whose linear bindings agree with every continuing predecessor. A successful generalized state projection binds every live linear owner to exactly one post-state slot and binds no owner that was not live on that predecessor; fixed-subject slots require exact semantic-subject continuity or explicit accepted succession evidence, while abstract slots may select branch-local mutually exclusive owners. Omission, duplication, fresh owner invention, and equal-typed wrong-subject impersonation are rejected."
  , rocqSpecKind = "Resource join conservation, exact owner accounting, and semantic-subject continuity"
  , rocqSpecOrigin =
      "src/Phil/Systems/ControlStateProjection.hs::{checkStateProjection,checkStateBoundaryProjections}; src/Phil/Systems/SubjectCorrespondence.hs; src/Phil/Systems/ProtocolStateCorrespondence.hs; test/Main.hs; test/ProcessMain.hs; test/Phase1SubjectCorrespondenceMain.hs; test/Phase1ControlStateProjectionMain.hs; test/Phase1ProtocolStateCorrespondenceMain.hs; proof/Phil/Core/ContextJoin.v; proof/Phil/Core/ProcessJoin.v; proof/Phil/Core/ResourceJoin.v"
  , rocqSpecScope =
      "Phase 1 RES-001 through RES-004 continuing join conservation and subject-identity discipline"
  , rocqSpecRepresentation =
      "extensional live-owner predicates, functional post-state slot bindings, opaque semantic-subject/type atoms, explicit succession evidence, Core ResourceContext joins, and process Continue-path projection"
  , rocqSpecSubjects =
      [ "ResourceProjection"
      , "projectionIncomingLinear"
      , "projectionBindings"
      , "ResourceSlotRequirement"
      , "SuccessionEvidence"
      , "ContextJoinSuccess"
      , "ProcessJoinSuccess"
      , "StateBoundaryContract"
      , "StateProjection"
      , "SourceSubjectKey"
      , "ProtocolTransitionBinding"
      ]
  , rocqSpecTheorems =
      [ "resource_projection_linear_owner_set_exact"
      , "resource_projection_linear_owner_bound_once"
      , "resource_projection_rejects_linear_omission"
      , "resource_projection_rejects_invented_linear_owner"
      , "fixed_subject_characterization"
      , "fixed_subject_accepts_exact_continuity"
      , "fixed_subject_accepts_explicit_succession"
      , "successful_fixed_slot_is_subject_justified"
      , "equal_type_does_not_justify_wrong_subject"
      , "branch_owner_selection_is_bounded"
      , "abstract_slot_accepts_mutually_exclusive_owner"
      , "core_join_conserves_linear_bindings"
      , "process_join_conserves_continuing_linear_bindings"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ResourceJoin.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ResourceJoin.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-RES-JOIN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-RES-JOIN-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-CTX-JOIN-001 and PHIL-PROC-JOIN-001 supply the Core continuing-path and ResourceContext join foundations. SYS-008 checkStateProjection supplies the concrete Phase 1 exact-subject, exact-slot-domain, restricted-owner uniqueness, and live-linear coverage checks; SYS-004 supplies explicit stable-subject correspondence. The theorem parameter SuccessionEvidence abstracts an already accepted semantic succession relation; SYS-009 provides the bounded Phase 1 protocol-endpoint witness with exact predecessor/successor occurrence identity, unique consumption/production, and acyclic lineage. The current Haskell stage stack verifies state projection and protocol succession as adjacent compositional layers rather than exposing one monolithic JoinContract API that threads arbitrary succession evidence directly into checkStateProjection; that reviewed cross-layer correspondence remains an explicit trust boundary. Rocq kernel/toolchain correctness, concrete Map/Set equality, Systems value lookup and role classification, CFG-edge validation, exact diagnostic ordering, finite subject indexes, and mapping from source semantic subjects/protocol occurrences to the normalized atoms remain explicit trust boundaries. Target phi/block-argument representation, branch-local scope discharge, loop transport, unresolved-obligation preservation, and foreign-provider truth remain outside this theorem family."
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
