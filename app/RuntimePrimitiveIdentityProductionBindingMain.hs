{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Map.Strict as Map
import Phil.Assurance.Types
  ( EvidenceEntryId (..)
  , RevisionId (..)
  )
import Phil.Examples.Phase1.RuntimePrimitiveWitnesses
  ( steveRuntimePrimitiveStage
  , uploadRuntimePrimitiveStage
  )
import Phil.Systems.IR
  ( RuntimeSiteRef (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageBundle (..)
  , RuntimeSiteBinding (..)
  )
import Phil.Systems.RuntimePrimitiveIdentityCertification
import Phil.Systems.RuntimePrimitiveReuse

main :: IO ()
main = do
  uploadStage <- requireStage "upload" uploadRuntimePrimitiveStage
  steveStage <- requireStage "Steve" steveRuntimePrimitiveStage

  uploadCertified <- requireCertified "upload" uploadStage
  assertPass "production target runtime primitive certifies upload exact site domain"
    (Map.keysSet (certifiedRuntimePrimitiveEntries uploadCertified)
      == Map.keysSet (runtimePrimitiveStageSites uploadStage))

  steveCertified <- requireCertified "Steve" steveStage
  assertPass "production target runtime primitive certifies Steve empty site domain"
    (Map.null (certifiedRuntimePrimitiveEntries steveCertified))

  sourceRef <- requireFirstSourceSite uploadStage
  let originalEntry = targetRuntimePrimitiveEntry sourceRef
      revisedRef = sourceRef
        { runtimeSiteRevision = RevisionId "assurance.revision.changed" }
      reEvidenceRef = sourceRef
        { runtimeSiteEvidence = EvidenceEntryId "assurance.evidence.changed" }
  assertPass "target-neutral primitive entry ignores assurance revision identity"
    (targetRuntimePrimitiveEntry revisedRef == originalEntry)
  assertPass "target-neutral primitive entry ignores assurance evidence identity"
    (targetRuntimePrimitiveEntry reEvidenceRef == originalEntry)

  assertNativeProfileRelabelRejected uploadStage
  assertKernelAcceptsExactFacts
  assertKernelRejectsPhysicalProfileDrift
  assertKernelRejectsAssuranceEncoding

requireStage
  :: String
  -> Either String RuntimePrimitiveStageBundle
  -> IO RuntimePrimitiveStageBundle
requireStage label result = case result of
  Left err -> fail (label <> " witness construction failed: " <> err)
  Right stage -> pure stage

requireCertified
  :: String
  -> RuntimePrimitiveStageBundle
  -> IO CertifiedRuntimePrimitiveStage
requireCertified label stage = case certifyRuntimePrimitiveStage stage of
  Left err -> fail (label <> " production certification failed: " <> show err)
  Right certified -> pure certified

requireFirstSourceSite :: RuntimePrimitiveStageBundle -> IO RuntimeSiteRef
requireFirstSourceSite stage =
  case Map.elems (runtimeClaimStageSites (runtimePrimitiveStageBase stage)) of
    [] -> fail "upload witness unexpectedly has no source runtime sites"
    binding : _ -> pure (runtimeSiteBindingRef binding)

assertNativeProfileRelabelRejected :: RuntimePrimitiveStageBundle -> IO ()
assertNativeProfileRelabelRejected stage =
  case Map.minViewWithKey (runtimePrimitiveStageSites stage) of
    Nothing -> fail "upload witness unexpectedly has no primitive sites"
    Just ((siteKey, binding), remainingSites) -> do
      let relabeledBinding = binding
            { runtimePrimitiveSiteProfile =
                RuntimePrimitiveProfileRef "invented.target.profile" }
          relabeledSites = Map.insert siteKey relabeledBinding remainingSites
          relabeledStage = makeRuntimePrimitiveStageBundle
            (runtimePrimitiveStageBase stage)
            relabeledSites
            (deriveRuntimePrimitiveReverse relabeledSites)
      case certifyRuntimePrimitiveStage relabeledStage of
        Left (RuntimePrimitiveIdentityNativeError
          (RuntimePrimitiveProfileMismatch _ _ _)) ->
            pass "native SYS-016 profile relabel diagnostic precedes kernel admission"
        other -> fail
          ("expected native RuntimePrimitiveProfileMismatch, got " <> show other)

assertKernelAcceptsExactFacts :: IO ()
assertKernelAcceptsExactFacts =
  case verifyRuntimePrimitiveIdentityKernelFacts
    (RuntimePrimitiveIdentityKernelFacts True True) of
      Right () -> pass "exact target runtime primitive kernel facts are accepted"
      Left err -> fail ("exact kernel facts unexpectedly rejected: " <> show err)

assertKernelRejectsPhysicalProfileDrift :: IO ()
assertKernelRejectsPhysicalProfileDrift =
  case verifyRuntimePrimitiveIdentityKernelFacts
    (RuntimePrimitiveIdentityKernelFacts False True) of
      Left (RuntimePrimitiveIdentityKernelDisagreement _) ->
        pass "target runtime primitive kernel rejects physical/profile drift"
      other -> fail ("expected physical/profile kernel disagreement, got " <> show other)

assertKernelRejectsAssuranceEncoding :: IO ()
assertKernelRejectsAssuranceEncoding =
  case verifyRuntimePrimitiveIdentityKernelFacts
    (RuntimePrimitiveIdentityKernelFacts True False) of
      Left (RuntimePrimitiveIdentityKernelDisagreement _) ->
        pass "target runtime primitive kernel rejects assurance-derived entry identity"
      other -> fail ("expected assurance-encoding kernel disagreement, got " <> show other)

assertPass :: String -> Bool -> IO ()
assertPass label condition
  | condition = pass label
  | otherwise = fail ("FAIL: " <> label)

pass :: String -> IO ()
pass label = putStrLn ("PASS: " <> label)
