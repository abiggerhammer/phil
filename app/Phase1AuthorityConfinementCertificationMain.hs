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
      certifyWith phase1AuthorityConfinementCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1AuthorityConfinementCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1AuthorityConfinementCertificationSpec :: RocqCertificationSpec
phase1AuthorityConfinementCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-authority-confinement"
  , rocqSpecObligation = ObligationId "PHIL-AUTH-CONFINE-001"
  , rocqSpecClaim =
      "Pure-Phil closure authority is confined only when public mediated authority and exercised authority are actually reachable and every exercised authority operation stays within the public surface; negative-authority claims are decided from exact reachable authority rather than from narrow public behavior. Provider implementations may contain authority absent from the client-visible provider surface only when their internal-authority inventory has an admissible basis and every extra internal grant has an exact admissible disposition. Statically confined pure-Phil authority must be reachable internally while absent from checked public mediation and checked exercise. Opaque foreign authority inventories require explicit evidence, assumption, or TCB basis; static Phil confinement and ABI-derived absence are insufficient. External-evidence, assumption, and TCB dispositions are explicit conditional facts rather than proofs of their underlying conditions."
  , rocqSpecKind = "Reachable closure and provider/foreign authority confinement"
  , rocqSpecOrigin =
      "src/Phil/Core/AuthorityConfinement.hs::{authorityUsesForSurface,reachableAuthorityUses,checkClosureAuthorityConfinement,checkNegativeAuthorityClaim}; src/Phil/Core/ProviderAuthorityQualification.hs::{semanticProviderAuthoritySubject,checkProviderAuthorityQualification}; test/Phase1AuthorityConfinementMain.hs; test/Phase1ProviderAuthorityQualificationMain.hs; proof/Phil/Core/AuthorityAttenuation.v; proof/Phil/Core/AuthorityConfinement.v"
  , rocqSpecScope =
      "Phase 1 pure-Phil closure authority reachability/confinement plus provider and opaque-foreign authority inventory/disposition qualification, layered on certified possession and attenuation"
  , rocqSpecRepresentation =
      "normalized subject-operation authority identities, extensional reachable/public/exercised/internal authority predicates, exact provider subject lineage, inventory-basis classes, and per-extra-authority disposition functions"
  , rocqSpecSubjects =
      [ "AuthorityUse"
      , "ClosureAuthorityConfinementSpec"
      , "NegativeAuthorityClaim"
      , "ProviderAuthoritySubject"
      , "ProviderAuthorityInventoryBasis"
      , "ProviderExtraAuthorityDisposition"
      , "ProviderAuthorityQualificationSpec"
      ]
  , rocqSpecTheorems =
      [ "closure_public_authority_must_be_reachable"
      , "closure_exercised_authority_must_be_reachable"
      , "closure_exercise_must_stay_within_public_authority"
      , "broader_internal_authority_may_be_confined"
      , "negative_authority_claim_checks_reachable_authority"
      , "hidden_reachable_authority_refutes_negative_claim"
      , "public_absence_alone_cannot_establish_negative_authority"
      , "authority_use_subject_is_identity_bearing"
      , "semantic_provider_authority_binds_exact_revisions"
      , "semantic_provider_requires_pure_phil_inventory_basis"
      , "opaque_provider_cannot_claim_pure_phil_inventory"
      , "foreign_provider_inventory_requires_evidence_assumption_or_tcb"
      , "abi_shape_never_establishes_authority_inventory"
      , "provider_static_reachability_must_be_declared_internal"
      , "provider_static_public_authority_must_be_client_visible"
      , "provider_static_exercise_must_be_client_visible"
      , "every_extra_internal_authority_has_exact_disposition"
      , "dispositions_cannot_be_invented_for_non_extra_authority"
      , "every_recorded_extra_disposition_must_be_admissible"
      , "pure_static_confinement_requires_hidden_reachable_unexercised_authority"
      , "opaque_foreign_authority_cannot_use_static_phil_confinement"
      , "abi_absence_is_never_confinement_evidence"
      , "external_confinement_is_explicit_conditional_disposition"
      , "assumption_dependent_authority_is_explicit_conditional_disposition"
      , "tcb_authority_boundary_is_explicit_conditional_disposition"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/AuthorityConfinement.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/AuthorityConfinement.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-AUTH-CONFINE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-AUTH-CONFINE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-AUTH-POSSESS-001 and PHIL-AUTH-ATTEN-001 supply the imported authority identity/visibility chain. Rocq kernel/toolchain correctness and reviewed correspondence from concrete AuthorityUse/AuthorityReachabilityOrigin Text identities, Haskell Set union/difference/canonicalization, Map disposition-domain checking and ordering, list-fold aggregation of checked closure summaries, ProviderAuthoritySubject keys, and exact Haskell diagnostics to the normalized extensional model remain explicit trust boundaries. The provider semantic subject is conditional on an already accepted PROV-001--005 CheckedProviderSemanticQualification; soundness of that provider qualification remains owned by PHIL-PROV-QUAL-001. External confinement evidence truth, environmental assumptions, TCB applicability, OS/process sandbox behavior, and current build-admission policy are not proven here: evidence/assumption/TCB dispositions are certified only as explicit conditional qualification forms. Systems/StageContract preservation, final syntax, and concrete foreign/runtime enforcement remain outside this theorem family."
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
