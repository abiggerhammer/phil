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
  { rocqSpecProfile = "phase1-provider-qualification"
  , rocqSpecObligation = ObligationId "PHIL-PROV-QUAL-001"
  , rocqSpecClaim = "Provider qualification is a total explicit semantic relation, not a nominal/signature/symbol relation. Exact provider contract and implementation revisions are required; every public operation has an explicit correspondence to an exact implementation entry; each corresponding callable semantically refines the public callable contract, requires no stronger preconditions, and maps every implementation outcome explicitly to an existing public outcome with exact branch-sensitive resource residue. Unexpected operation correspondence rejects, implementation symbols are nonsemantic, and qualification cannot widen authority, effects, or failures."
  , rocqSpecKind = "Total explicit provider semantic refinement and exact per-outcome resource correspondence"
  , rocqSpecOrigin = "src/Phil/Core/ProviderQualification.hs; test/Phase1ProviderQualificationMain.hs; docs/phase-1/provider-semantic-qualification-v1.md; proof/Phil/Core/CallableRefinement.v; proof/Phil/Core/ResourceJoin.v; proof/Phil/Core/ProviderQualification.v"
  , rocqSpecScope = "Phase 1 PROV-001 through PROV-005 semantic provider qualification kernel"
  , rocqSpecRepresentation = "functional exact operation/entry/outcome maps, exact revision atoms, certified CALL-012 refinement surfaces, opaque exact resource residues, and symbol metadata excluded from semantic qualification"
  , rocqSpecSubjects = ["ProviderContract", "ProviderImplementation", "ProviderQualificationClaim", "ProviderOperationCorrespondence", "ProviderResourceResidue", "CallableRefinementSurface"]
  , rocqSpecTheorems =
      [ "qualified_provider_has_exact_contract_revision"
      , "qualified_provider_has_exact_implementation_revision"
      , "every_public_operation_has_explicit_correspondence"
      , "missing_public_operation_correspondence_rejects"
      , "unexpected_operation_correspondence_rejects"
      , "qualified_operation_uses_callable_refinement"
      , "qualified_operation_has_no_stronger_preconditions"
      , "every_implementation_outcome_is_explicitly_mapped"
      , "every_declared_outcome_mapping_has_exact_resource_residue"
      , "exact_resource_residue_preserves_all_categories"
      , "implementation_symbols_are_nonsemantic"
      , "qualified_operation_never_strengthens_authority"
      , "qualified_operation_never_widens_effects"
      , "qualified_operation_never_adds_failures"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ProviderQualification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ProviderQualification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROV-QUAL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROV-QUAL-001.rocq.v1"
  , rocqSpecResidualBoundary = "PHIL-CALL-REFINE-001's certified CALL-012 core supplies callable semantic non-widening and PHIL-RES-JOIN-001 supplies the exact resource-conservation meaning consumed by per-outcome residue equality. The normalized proof treats concrete provider/resource/outcome identities extensionally. Rocq kernel/toolchain correctness and reviewed correspondence from Haskell Map/Set equality and traversal, exact InterfaceRevision/DefinitionRevision/Text keys, checkCallableRefinement composition, outcome-map diagnostics, and ProviderResourceResidue field equality remain explicit trust boundaries. Provider-wide state simulation/laws/lifecycle, richer authority/evidence qualification, conditional dependency closure, concrete foreign artifact truth, contextual build admission, ArchitectureRealization selection, final syntax, and target ABI realization are separate later provider obligations rather than hidden premises of PROV-001–005."
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
