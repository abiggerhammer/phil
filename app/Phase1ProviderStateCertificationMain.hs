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
    _ -> hPutStrLn stderr
      "usage: CERTIFIER SOURCE.v COMPILED.vo OUTPUT.cert" >> exitFailure

certificationSpec :: RocqCertificationSpec
certificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-provider-state-laws-lifecycle"
  , rocqSpecObligation = ObligationId "PHIL-PROV-STATE-001"
  , rocqSpecClaim = "Stateful provider qualification extends the already-qualified PROV-001–005 semantic relation without changing provider identity. Visible implementation initial states have an exact total correspondence into admissible related abstract initial states; every reachable implementation transition uses an explicitly qualified operation/outcome and simulates an allowed public transition for every related abstract pre-state. Provider-wide history laws evaluate only exact public events obtained through the qualified outcome map and use deterministic missing-transition-is-illegal monitors. Lifecycle qualification requires exact interruption-point coverage, already-qualified operations, one exact public observation boundary, and every modeled observation to lie inside the declared observable-state, cleanup-residue, and retry-disposition allowances."
  , rocqSpecKind = "Provider state simulation, public-history law preservation, and lifecycle/interruption qualification"
  , rocqSpecOrigin = "src/Phil/Core/ProviderStateQualification.hs; src/Phil/Core/ProviderLawQualification.hs; src/Phil/Core/ProviderLifecycleQualification.hs; test/Phase1ProviderStateQualificationMain.hs; test/Phase1ProviderLawQualificationMain.hs; test/Phase1ProviderLifecycleQualificationMain.hs; docs/phase-1/provider-state-simulation-v1.md; docs/phase-1/provider-wide-laws-v1.md; docs/phase-1/provider-lifecycle-v1.md; proof/Phil/Core/ProviderQualification.v; proof/Phil/Core/ProviderStateQualification.v"
  , rocqSpecScope = "Phase 1 PROV-006 through PROV-008 provider state, law, and lifecycle semantic core"
  , rocqSpecRepresentation = "exact abstract/concrete state relation predicates, exact qualified operation/outcome maps, deterministic public-history transition functions, exact lifecycle point maps, and predicate-valued lifecycle allowance/observation sets"
  , rocqSpecSubjects =
      [ "ProviderStateRefinement"
      , "ProviderStateRelationRevision"
      , "ProviderLaw"
      , "ProviderLawRevision"
      , "ProviderLifecycleContract"
      , "ProviderLifecycleModel"
      , "ProviderLifecycleRevision"
      ]
  , rocqSpecTheorems =
      [ "provider_state_initial_domain_is_exact"
      , "missing_provider_initial_correspondence_rejects"
      , "unexpected_provider_initial_correspondence_rejects"
      , "provider_initial_pair_is_admissible_and_related"
      , "provider_state_transition_has_qualified_outcome"
      , "provider_state_transition_starts_inside_relation"
      , "provider_state_simulates_every_related_prestate"
      , "provider_law_empty_trace_accepts"
      , "accepted_provider_law_trace_has_exact_translation"
      , "provider_law_translation_preserves_operation"
      , "provider_law_translation_uses_exact_outcome_mapping"
      , "unqualified_first_provider_event_rejects"
      , "unmapped_first_provider_outcome_rejects"
      , "missing_provider_law_transition_rejects"
      , "provider_law_run_is_deterministic"
      , "missing_provider_lifecycle_point_rejects"
      , "unexpected_provider_lifecycle_point_rejects"
      , "qualified_provider_lifecycle_point_uses_qualified_operation"
      , "qualified_provider_lifecycle_observation_is_exact"
      , "forbidden_provider_observable_state_rejects"
      , "forbidden_provider_cleanup_residue_rejects"
      , "forbidden_provider_retry_disposition_rejects"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ProviderStateQualification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ProviderStateQualification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROV-STATE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROV-STATE-001.rocq.v1"
  , rocqSpecResidualBoundary = "PHIL-PROV-QUAL-001 supplies the certified PROV-001–005 semantic operation/outcome correspondence consumed by this normalized model; its production path is additionally Implementation Refined by PHIL-PROV-QUAL-IMPL-001. The proof does not infer that finite implementation-transition sets, law trace corpora, or interruption models exhaust all reachable behavior. Coverage/completeness must come from proof, model checking, exhaustive exploration, translation validation, platform evidence, or another named qualification basis. Rocq kernel/toolchain correctness and reviewed correspondence from concrete Text keys, Haskell Map/Set ordering/equality/traversal, list monitor execution, exact diagnostics, ProviderResourceResidue equality, and construction of crash/interference models remain explicit trust or evidence boundaries. Provider authority/evidence qualification, contextual admission, ArchitectureRealization selection, target lifecycle preservation, final syntax, and runtime/backend correctness remain downstream."
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
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn ("certified " <> Text.unpack obligation <> " as ProofAssistantTheorem evidence")
      putStrLn ("certificate artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn ("certificate sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))
