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
      certifyWith phase1GenericIdentityCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1GenericIdentityCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1GenericIdentityCertificationSpec :: RocqCertificationSpec
phase1GenericIdentityCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-generic-identity"
  , rocqSpecObligation = ObligationId "PHIL-GEN-ID-001"
  , rocqSpecClaim =
      "Ordinary generic application identity is applicative and determined by declaration lineage, exact public InterfaceRevision, and the extensional identity-bearing semantic argument mapping. Argument source order is nonsemantic and duplicate semantic parameter keys reject. DefinitionRevision and accepted requirement-discharge evidence are downstream discharge-lineage facts rather than semantic application identity; replacing accepted evidence therefore preserves the application while changing lineage. An evidence/provider/contract object explicitly passed as a semantic argument changes application identity normally. Equal generic applications embedded at distinct architecture occurrence slots remain distinct occurrences."
  , rocqSpecKind = "Generic semantic application identity and discharge lineage"
  , rocqSpecOrigin =
      "src/Phil/Core/Generic.hs::{deriveGenericApplicationIdentity,genericApplicationSemanticForm,deriveGenericDischargeLineage}; src/Phil/Core/Static.hs::{instantiateArchitecture,InstanceKey}; test/Phase1GenericIdentityMain.hs; proof/Phil/Core/GenericIdentity.v"
  , rocqSpecScope =
      "Phase 1 ordinary generic semantic application identity, discharge lineage separation, and preservation of architecture occurrence generativity"
  , rocqSpecRepresentation =
      "normalized declaration/interface identity plus extensional semantic-argument lookup relation, with definition/evidence lineage represented separately"
  , rocqSpecSubjects =
      [ "GenericApplicationIdentity"
      , "GenericDischargeLineage"
      , "semantic argument mapping"
      , "DefinitionRevision"
      , "architecture occurrence slot identity"
      ]
  , rocqSpecTheorems =
      [ "ordinary_generic_application_is_applicative"
      , "two_distinct_argument_orders_are_equivalent"
      , "semantic_argument_order_is_nonsemantic"
      , "duplicate_semantic_argument_keys_reject"
      , "declaration_key_is_part_of_application_identity"
      , "interface_revision_is_part_of_application_identity"
      , "identity_bearing_semantic_argument_changes_application"
      , "discharge_evidence_replacement_preserves_semantic_application"
      , "discharge_evidence_replacement_changes_lineage"
      , "definition_revision_is_not_semantic_application_identity"
      , "definition_revision_change_changes_discharge_lineage"
      , "discharge_metadata_is_downstream_of_application_identity"
      , "equal_application_at_distinct_occurrence_slots_remains_generative"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/GenericIdentity.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/GenericIdentity.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-GEN-ID-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-GEN-ID-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-GEN-STRUCT-001, PHIL-GEN-REQ-001, and PHIL-GEN-INST-001 supply the preceding generic proof chain. Rocq kernel/toolchain correctness and reviewed correspondence from Haskell Map canonicalization, GenericStaticParameterKey/SemanticForm representation, semantic-form serialization, and architecture InstanceKey derivation to the normalized model remain explicit trust boundaries. Hash/canonicalization collision resistance remains a representation assumption. GEN-011 target strengthening belongs to the StageContract/ADR-020 verifier and is outside this theorem family, as are conditional generic assurance reuse, final syntax, and generic lowering."
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
