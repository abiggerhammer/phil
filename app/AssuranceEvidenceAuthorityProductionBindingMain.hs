{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance
import Phil.Assurance.EvidenceAuthorityKernelBridge
  ( artifactAuthorityKernelAccepts
  , runtimeAuthorityKernelAccepts
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "bridge accepts exact artifact authority facts" $
        artifactAuthorityKernelAccepts True True True
    , test "bridge rejects undeclared artifact" $
        not (artifactAuthorityKernelAccepts False True True)
    , test "bridge rejects artifact identity mismatch" $
        not (artifactAuthorityKernelAccepts True False True)
    , test "bridge rejects artifact digest mismatch" $
        not (artifactAuthorityKernelAccepts True True False)
    , test "bridge accepts exact runtime authority facts" $
        runtimeAuthorityKernelAccepts True True True True True
    , test "bridge rejects missing runtime mechanism" $
        not (runtimeAuthorityKernelAccepts False True True True True)
    , test "bridge rejects incomplete runtime mechanism" $
        not (runtimeAuthorityKernelAccepts True False True True True)
    , test "bridge rejects missing runtime residue" $
        not (runtimeAuthorityKernelAccepts True True False True True)
    , test "bridge rejects missing runtime cost reference" $
        not (runtimeAuthorityKernelAccepts True True True False True)
    , test "bridge rejects unknown runtime cost reference" $
        not (runtimeAuthorityKernelAccepts True True True True False)
    , test "production reference manifest still verifies" referenceManifestVerifies
    , test "production preserves required-artifact diagnostic" requiredArtifactRejects
    , test "production preserves artifact-digest diagnostic" artifactDigestRejects
    , test "production preserves missing-runtime-mechanism diagnostic" runtimeMechanismRejects
    , test "production preserves missing-runtime-residue diagnostic" runtimeResidueRejects
    , test "production preserves missing-runtime-cost diagnostic" runtimeCostRejects
    , test "production preserves incomplete-runtime diagnostic" runtimeIncompleteRejects
    ]
  if and results then pure () else exitFailure

referenceManifestVerifies :: Bool
referenceManifestVerifies =
  verifyManifest phase0UploadVerificationContext phase0UploadLedger phase0UploadManifest == Right ()

requiredArtifactRejects :: Bool
requiredArtifactRejects =
  let entryId = EvidenceEntryId "evidence.upload.version.server.kernel"
      badLedger = adjustEvidence entryId
        (\entry -> entry
          { evidenceAssuranceKind = PropertyTested
          , evidenceArtifact = Nothing
          })
        phase0UploadLedger
      manifest = sealManifest badLedger phase0UploadManifest
  in case verifyManifest phase0UploadVerificationContext badLedger manifest of
      Left (EvidenceKindRequiresArtifact key PropertyTested) -> key == entryId
      _ -> False

artifactDigestRejects :: Bool
artifactDigestRejects =
  let entryId = EvidenceEntryId "evidence.upload.version.server.kernel"
      artifact = ArtifactIdentity (ArtifactRef "artifact:test") (digestText "declared")
      badLedger = adjustEvidence entryId
        (\entry -> entry
          { evidenceAssuranceKind = PropertyTested
          , evidenceArtifact = Just artifact
          })
        phase0UploadLedger
      context = phase0UploadVerificationContext
        { verificationAvailableArtifacts =
            Map.singleton (ArtifactRef "artifact:test") (digestText "actual") }
      manifest = sealManifest badLedger phase0UploadManifest
  in case verifyManifest context badLedger manifest of
      Left ArtifactDigestMismatch {} -> True
      _ -> False

runtimeMechanismRejects :: Bool
runtimeMechanismRejects =
  expectRuntimeError mutate matches
  where
    mutate entry = entry { evidenceRuntimeMechanism = Nothing }
    matches err = case err of
      RuntimeEvidenceMissingMechanism _ -> True
      _ -> False

runtimeResidueRejects :: Bool
runtimeResidueRejects =
  expectRuntimeError mutate matches
  where
    mutate entry = entry { evidenceRuntimeResidue = [] }
    matches err = case err of
      RuntimeEvidenceMissingResidue _ -> True
      _ -> False

runtimeCostRejects :: Bool
runtimeCostRejects =
  expectRuntimeError mutate matches
  where
    mutate entry = entry { evidenceCostRefs = [] }
    matches err = case err of
      RuntimeEvidenceMissingCostRef _ -> True
      _ -> False

runtimeIncompleteRejects :: Bool
runtimeIncompleteRejects =
  expectRuntimeError mutate matches
  where
    mutate entry = entry
      { evidenceRuntimeMechanism = fmap
          (\mechanism -> mechanism { runtimeFailureContract = "" })
          (evidenceRuntimeMechanism entry)
      }
    matches err = case err of
      RuntimeMechanismIncomplete _ -> True
      _ -> False

expectRuntimeError
  :: (EvidenceEntry -> EvidenceEntry)
  -> (ManifestError -> Bool)
  -> Bool
expectRuntimeError mutate matches =
  let entryId = EvidenceEntryId "evidence.upload.ingress.hello.runtime"
      badLedger = adjustEvidence entryId mutate phase0UploadLedger
      manifest = sealManifest badLedger phase0UploadManifest
  in case verifyManifest phase0UploadVerificationContext badLedger manifest of
      Left err -> matches err
      Right () -> False

sealManifest :: AssuranceLedger -> AssuranceManifest -> AssuranceManifest
sealManifest ledger manifest = manifest { manifestId = deriveManifestId ledger manifest }

adjustEvidence
  :: EvidenceEntryId
  -> (EvidenceEntry -> EvidenceEntry)
  -> AssuranceLedger
  -> AssuranceLedger
adjustEvidence key modify ledger = ledger
  { ledgerEvidence = Map.adjust update key (ledgerEvidence ledger) }
  where
    update entry =
      let changed = modify entry
      in changed { evidenceEntryDigest = deriveEvidenceEntryDigest changed }

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS: " else "FAIL: ") <> label)
  pure result
