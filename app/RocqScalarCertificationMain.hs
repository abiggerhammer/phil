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
