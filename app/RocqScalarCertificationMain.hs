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
      certifyWith coreScalarCertificationSpec sourcePath compiledPath outputPath
    [profileText, sourcePath, compiledPath, outputPath] ->
      case certificationSpecFor (Text.pack profileText) of
        Nothing -> do
          hPutStrLn stderr ("unknown Rocq certification profile: " <> profileText)
          exitFailure
        Just spec -> certifyWith spec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: phil-certify-core-scalar [PROFILE] SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

certificationSpecFor :: Text.Text -> Maybe RocqCertificationSpec
certificationSpecFor profile
  | profile == rocqSpecProfile phase1ArchImportCertificationSpec =
      Just phase1ArchImportCertificationSpec
  | profile == rocqSpecProfile phase1GenericStructuralCertificationSpec =
      Just phase1GenericStructuralCertificationSpec
  | profile == rocqSpecProfile phase1GenericRequirementsCertificationSpec =
      Just phase1GenericRequirementsCertificationSpec
  | otherwise =
      case knownRocqCertificationSpec profile of
        Just spec -> Just spec
        Nothing -> case knownRecognizedRecordRocqCertificationSpec profile of
          Just spec -> Just spec
          Nothing -> case knownExactReceiveRocqCertificationSpec profile of
            Just spec -> Just spec
            Nothing -> knownDigestValidationRocqCertificationSpec profile

phase1ArchImportCertificationSpec :: RocqCertificationSpec
phase1ArchImportCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-arch-import"
  , rocqSpecObligation = ObligationId "PHIL-ARCH-IMPORT-001"
  , rocqSpecClaim =
      "Importing or resolving a declaration changes name availability only: a successful import preserves the exact already-checked DeclarationIdentity and grants no capability authority, satisfies no provider requirement, accepts no assumption, discharges no obligation, instantiates no architecture occurrence, selects no realization, and creates no runtime effect. Module locators do not define semantic identity once the same checked declaration has been selected; duplicate local names and unknown exports fail closed without a successor resolver state."
  , rocqSpecKind = "Architecture import authority noninterference"
  , rocqSpecOrigin =
      "src/Phil/Surface/Check.hs::{ResolutionScope,declareModule,insertLocalDeclaration,resolveImports,lookupResolvedDeclaration}; test/Phase1ImportNoninterferenceMain.hs; proof/Phil/Surface/ImportNoninterference.v"
  , rocqSpecScope =
      "Phase 1 authority-neutral module/import resolution over already checked DeclarationIdentity values"
  , rocqSpecRepresentation =
      "normalized local-name to DeclarationIdentity resolver state with explicit non-resolution semantic residue"
  , rocqSpecSubjects =
      [ "ResolutionScope"
      , "DeclarationIdentity"
      , "module/export selection"
      , "authority/provider/assumption/obligation noninterference"
      , "architecture occurrence/realization/runtime noninterference"
      ]
  , rocqSpecTheorems =
      [ "successful_import_preserves_exact_declaration_identity"
      , "successful_import_changes_name_availability_only"
      , "successful_import_grants_no_capability_authority"
      , "successful_import_satisfies_no_provider_requirement"
      , "successful_import_accepts_no_assumption"
      , "successful_import_discharges_no_obligation"
      , "successful_import_instantiates_no_architecture_occurrence"
      , "successful_import_creates_no_realization"
      , "successful_import_creates_no_runtime_effect"
      , "module_locator_does_not_define_resolved_identity"
      , "duplicate_resolution_name_fails_closed"
      , "unknown_export_fails_closed"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Surface/ImportNoninterference.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Surface/ImportNoninterference.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-ARCH-IMPORT-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-ARCH-IMPORT-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness and the reviewed correspondence from Phil.Surface.Check's concrete Text/Map/fold/module-table resolver to the normalized proof model remain explicit trust boundaries. Final Phil import syntax, package/version solving, repository provenance, and declaration-checking soundness are outside this theorem family."
  }

phase1GenericStructuralCertificationSpec :: RocqCertificationSpec
phase1GenericStructuralCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-generic-structural"
  , rocqSpecObligation = ObligationId "PHIL-GEN-STRUCT-001"
  , rocqSpecClaim =
      "A generic may transfer an abstract value without copy/drop authority. Duplicating an abstract value induces contraction/copy requirements; discarding it induces weakening/drop requirements. Instantiation succeeds only when the actual structural mode satisfies the induced requirements."
  , rocqSpecKind = "Generic structural polymorphism"
  , rocqSpecOrigin =
      "src/Phil/Core/Generic.hs::{inferGenericStructuralRequirements,modeAllowsStructuralPermission,checkGenericStructuralActual}; test/Phase1GenericStructuralMain.hs; proof/Phil/Core/GenericStructural.v"
  , rocqSpecScope =
      "Phase 1 bounded generic structural checker over already resolved abstract value parameters"
  , rocqSpecRepresentation =
      "normalized weakening/contraction requirement set and unrestricted/affine/linear mode satisfaction algebra"
  , rocqSpecSubjects =
      [ "GenericStructuralUse"
      , "GenericStructuralRequirements"
      , "StructuralPermission"
      , "Mode"
      ]
  , rocqSpecTheorems =
      [ "transfer_requires_no_structural_permission"
      , "discard_induces_weakening"
      , "duplication_induces_contraction"
      , "transfer_only_has_empty_requirements"
      , "linear_actual_satisfies_pure_transfer"
      , "discard_requires_exactly_weakening_from_empty"
      , "unrestricted_satisfies_weakening"
      , "affine_satisfies_weakening"
      , "linear_rejects_weakening"
      , "duplication_requires_exactly_contraction_from_empty"
      , "unrestricted_satisfies_contraction"
      , "affine_rejects_contraction"
      , "linear_rejects_contraction"
      , "duplicate_and_discard_require_both_permissions"
      , "unrestricted_satisfies_both_permissions"
      , "affine_rejects_both_permissions"
      , "linear_rejects_both_permissions"
      , "structural_use_accumulation_commutes"
      , "two_use_inference_is_order_independent"
      , "unrestricted_satisfies_every_structural_requirement"
      , "linear_satisfies_only_empty_structural_requirements"
      , "affine_satisfaction_excludes_contraction"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/GenericStructural.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/GenericStructural.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-GEN-STRUCT-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-GEN-STRUCT-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness and reviewed correspondence from Phil.Core.Generic's concrete GenericValueParameterKey/Text, Map/Set normalization and checked use-event traversal to the normalized proof model remain explicit trust boundaries. Full generic binder representation and resource-context plumbing are outside this theorem family."
  }

phase1GenericRequirementsCertificationSpec :: RocqCertificationSpec
phase1GenericRequirementsCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-generic-requirements"
  , rocqSpecObligation = ObligationId "PHIL-GEN-REQ-001"
  , rocqSpecClaim =
      "The checked body-induced generic structural requirement set is the minimum public requirement set when no explicit public contract is supplied. An explicit public contract may be stronger, but must cover every body-induced permission. Body revisions may change the inferred minimum while preserving a stable public contract only while the revised minimum remains covered; omitted explicit permissions are empty and body growth beyond the published contract rejects."
  , rocqSpecKind = "Stable generic public structural requirements"
  , rocqSpecOrigin =
      "src/Phil/Core/Generic.hs::{checkGenericStructuralInterface,normalizePublishedRequirements,ensurePublishedCoversInduced}; test/Phase1GenericRequirementsMain.hs; proof/Phil/Core/GenericStructural.v; proof/Phil/Core/GenericRequirements.v"
  , rocqSpecScope =
      "Phase 1 bounded structural portion of generic public requirements over already resolved abstract value parameters"
  , rocqSpecRepresentation =
      "normalized weakening/contraction minimum and published requirement sets with componentwise coverage"
  , rocqSpecSubjects =
      [ "CheckedGenericStructuralInterface"
      , "GenericStructuralRequirements"
      , "published structural contract"
      , "body-induced minimum"
      ]
  , rocqSpecTheorems =
      [ "implicit_public_contract_is_exact_inferred_minimum"
      , "explicit_public_contract_is_preserved_when_it_covers_body"
      , "published_contract_may_be_stronger_than_body"
      , "body_evolution_within_stable_weakening_contract_is_accepted"
      , "body_evolution_within_stable_full_contract_is_accepted"
      , "body_cannot_outgrow_published_weakening_contract"
      , "omitted_explicit_permission_is_semantically_empty"
      , "published_contract_acceptance_means_componentwise_coverage"
      , "accepted_published_contract_contains_induced_weakening"
      , "accepted_published_contract_contains_induced_contraction"
      , "accepted_contract_remains_stable_across_covered_body_revision"
      , "structural_inference_order_independence_preserves_publication"
      , "unrestricted_actual_satisfies_any_accepted_public_contract"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/GenericRequirements.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/GenericRequirements.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-GEN-REQ-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-GEN-REQ-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-GEN-STRUCT-001 supplies the imported structural algebra. Rocq kernel/toolchain correctness and reviewed correspondence from Phil.Core.Generic's concrete parameter-key maps, Set normalization, explicit-vs-implicit published-list normalization, and duplicate/unknown-key checks to the normalized proof model remain explicit trust boundaries. Provider/callable/proposition requirements and final generic syntax are outside this theorem family."
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
