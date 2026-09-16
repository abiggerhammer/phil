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
      certifyWith phase1AuthorityAttenuationCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1AuthorityAttenuationCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1AuthorityAttenuationCertificationSpec :: RocqCertificationSpec
phase1AuthorityAttenuationCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-authority-attenuation"
  , rocqSpecObligation = ObligationId "PHIL-AUTH-ATTEN-001"
  , rocqSpecClaim =
      "Authority visible across a semantic boundary preserves the exact semantic subject and never exceeds the authority operations available at the source. Changing authority contracts requires an exact attenuation witness bound to the source contract, target contract, subject, and complete target-visible operation set; an unchanged contract cannot silently change its authority surface. Generic, callable, provider, architecture, and other semantic boundaries share the same non-widening rule. After control-flow reconvergence, visible authority must be present on every continuing branch and branch-local authority is never unioned. Projection from an actually possessed capability preserves its semantic contract, subject, and operations while authority visibility remains independent of structural mode."
  , rocqSpecKind = "Explicit authority attenuation and semantic non-widening"
  , rocqSpecOrigin =
      "src/Phil/Core/AuthorityAttenuation.hs::{authoritySurfaceFromCapability,checkExplicitAuthorityAttenuation,checkAuthorityBoundary,checkAuthorityJoin}; test/Phase1AuthorityAttenuationMain.hs; proof/Phil/Core/AuthorityPossession.v; proof/Phil/Core/AuthorityAttenuation.v"
  , rocqSpecScope =
      "Phase 1 pure-Phil semantic authority visibility across explicit attenuation boundaries and continuing-branch joins, layered on certified authority possession"
  , rocqSpecRepresentation =
      "normalized opaque contract/subject atoms, extensional operation predicates, one boundary-independent non-widening relation, and keyed continuing-branch authority availability"
  , rocqSpecSubjects =
      [ "AuthoritySurface"
      , "AuthorityAttenuationWitness"
      , "AuthorityBoundaryKind"
      , "AuthorityCapability"
      , "semantic authority contract/subject/operation"
      ]
  , rocqSpecTheorems =
      [ "capability_projection_preserves_semantic_surface"
      , "authority_surface_projection_is_mode_independent"
      , "explicit_attenuation_preserves_exact_subject"
      , "explicit_attenuation_never_widens"
      , "attenuation_witness_binds_source_contract"
      , "attenuation_witness_binds_target_contract"
      , "attenuation_witness_binds_subject"
      , "attenuation_witness_binds_visible_operations"
      , "exact_narrowing_constructs_checked_attenuation"
      , "authority_boundary_preserves_exact_subject"
      , "authority_boundary_never_widens"
      , "same_contract_boundary_preserves_operation_surface"
      , "contract_change_requires_exact_attenuation_witness"
      , "boundary_kind_does_not_change_authority_rule"
      , "authority_join_requires_continuing_branch"
      , "authority_join_preserves_subject_on_every_branch"
      , "authority_join_preserves_contract_on_every_branch"
      , "authority_join_never_unions_branch_local_authority"
      , "branch_local_absence_blocks_join_visibility"
      , "common_authority_may_join"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/AuthorityAttenuation.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/AuthorityAttenuation.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-AUTH-ATTEN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-AUTH-ATTEN-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-AUTH-POSSESS-001 supplies the imported normalized capability model and PHIL-GEN-STRUCT-001 supplies its structural mode algebra. Rocq kernel/toolchain correctness and reviewed correspondence from concrete AuthorityContractKey/AuthoritySubjectKey/AuthorityOperationKey Text identity, Haskell Set subset/difference/equality and canonicalization, list/fold join implementation, exact diagnostics/error ordering, and Maybe attenuation-witness representation to the normalized extensional model remain explicit trust boundaries. Construction, borrowing, moving, copying, or consumption of a derived attenuated capability occurrence is outside this visibility theorem; closure/provider reachable-authority confinement, foreign ambient-authority evidence (AUTH-006), final syntax, and Systems/StageContract lowering remain outside this theorem family."
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
