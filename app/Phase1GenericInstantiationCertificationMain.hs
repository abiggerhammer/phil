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
      certifyWith phase1GenericInstantiationCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1GenericInstantiationCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1GenericInstantiationCertificationSpec :: RocqCertificationSpec
phase1GenericInstantiationCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-generic-instantiation"
  , rocqSpecObligation = ObligationId "PHIL-GEN-INST-001"
  , rocqSpecClaim =
      "Generic instantiation gives every exact public requirement one explicit disposition and accepts no duplicate or unexposed disposition. Structural permissions require an admitting mode; provider contracts require the exact InterfaceRevision or an already checked refinement targeting that exact revision; proposition evidence names the exact required proposition; provider availability does not discharge proposition laws; unmet requirements do not become assumptions implicitly; and assumption-dependent or exported dispositions are accepted only under an explicit permitting policy."
  , rocqSpecKind = "Exact generic requirement discharge"
  , rocqSpecOrigin =
      "src/Phil/Core/Generic.hs::{checkGenericInstantiation,normalizeDispositions,checkRequirementDisposition,checkRequirementSpecific}; test/Phase1GenericInstantiationMain.hs; proof/Phil/Core/GenericStructural.v; proof/Phil/Core/GenericRequirements.v; proof/Phil/Core/GenericInstantiation.v"
  , rocqSpecScope =
      "Phase 1 bounded generic instantiation over exact structural, provider-contract, and proposition requirements"
  , rocqSpecRepresentation =
      "normalized exact requirement/disposition domain plus per-disposition validity under an explicit assumption/export policy"
  , rocqSpecSubjects =
      [ "GenericRequirement"
      , "GenericRequirementDisposition"
      , "GenericInstantiationPolicy"
      , "GenericInstantiationRecord"
      , "CheckedProviderRefinement target relation"
      ]
  , rocqSpecTheorems =
      [ "accepted_instantiation_has_no_duplicate_requirement_keys"
      , "accepted_instantiation_has_disposition_for_every_requirement"
      , "accepted_instantiation_has_no_unexposed_disposition"
      , "missing_requirement_never_becomes_implicit_assumption"
      , "duplicate_requirement_dispositions_reject"
      , "unexposed_requirement_disposition_rejects"
      , "accepted_disposition_is_valid"
      , "exact_provider_satisfaction_requires_exact_interface"
      , "merely_different_nominal_provider_does_not_satisfy"
      , "checked_provider_refinement_must_target_exact_required_interface"
      , "provider_binding_does_not_discharge_proposition_requirement"
      , "proposition_evidence_must_name_exact_proposition"
      , "evidence_for_other_proposition_rejects"
      , "strict_policy_rejects_assumption_disposition"
      , "explicit_assumption_policy_admits_assumption_disposition"
      , "strict_policy_rejects_export_disposition"
      , "explicit_export_policy_admits_export_disposition"
      , "affine_satisfies_structural_weakening_requirement"
      , "linear_rejects_structural_weakening_requirement"
      , "wrong_disposition_kind_rejects"
      , "strict_accepted_instantiation_contains_no_assumptions"
      , "strict_accepted_instantiation_contains_no_exports"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/GenericInstantiation.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/GenericInstantiation.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-GEN-INST-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-GEN-INST-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-GEN-STRUCT-001 and PHIL-GEN-REQ-001 supply the imported structural/public-requirement algebra. Rocq kernel/toolchain correctness and reviewed correspondence from Phil.Core.Generic's concrete GenericRequirement Set, Map-normalized disposition table, InterfaceRevision/Proposition identities, and error ordering to the normalized proof model remain explicit trust boundaries. CheckedProviderRefinement soundness is inherited from the competent provider/ADR-021 layer. Proposition truth/subject validity, callable/static-contract requirements, runtime/deployment dispositions, final syntax, and lowering are outside this theorem family."
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
