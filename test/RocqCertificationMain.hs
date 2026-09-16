{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "core scalar Rocq certificate closes its manifest"
        (certificateCloses coreScalarCertificationSpec)
    , test "Systems field projection Rocq certificate closes its manifest"
        (certificateCloses systemsFieldProjectionCertificationSpec)
    , test "LLVM field projection Rocq certificate closes its manifest"
        (certificateCloses llvmFieldProjectionCertificationSpec)
    , test "Systems recognized-record Rocq certificate closes its manifest"
        (certificateCloses systemsRecognizedRecordCertificationSpec)
    , test "LLVM recognized-record ABI Rocq certificate closes its manifest"
        (certificateCloses llvmRecognizedRecordABICertificationSpec)
    , test "LLVM runtime-symbol Rocq certificate closes its manifest"
        (certificateCloses llvmRuntimeSymbolCertificationSpec)
    , test "LLVM exact-receive Rocq certificate closes its manifest"
        (certificateCloses llvmExactReceiveCertificationSpec)
    , test "Systems digest-validation Rocq certificate closes its manifest"
        (certificateCloses systemsDigestValidationCertificationSpec)
    , test "LLVM digest-validation Rocq certificate closes its manifest"
        (certificateCloses llvmDigestValidationCertificationSpec)
    , test "known Rocq certification profiles resolve" knownProfilesResolve
    , test "proof-bound recognized-record certification closes"
        recognizedRecordProofCertificationCloses
    , test "proof-bound recognized-record certification checks proof artifact digests"
        recognizedRecordProofArtifactTamperRejects
    , test "proof-bound exact-receive certification closes"
        exactReceiveProofCertificationCloses
    , test "proof-bound exact-receive certification checks proof artifact digests"
        exactReceiveProofArtifactTamperRejects
    , test "proof-bound digest-validation certification closes"
        digestValidationProofCertificationCloses
    , test "proof-bound digest-validation certification checks proof artifact digests"
        digestValidationProofArtifactTamperRejects
    , test "missing expected theorem rejects certification" missingTheoremRejects
    , test "cross-profile obligation marker rejects certification" wrongMarkerRejects
    , test "compiled proof object is content-bound" compiledObjectIsBound
    , test "trusted Rocq packaging names its external-check precondition" trustedPackagingNamesPrecondition
    , test "certificate artifact digest is checked by the manifest" certificateTamperRejects
    ]
  if and results then pure () else exitFailure

certificateCloses :: RocqCertificationSpec -> Bool
certificateCloses spec = case candidate spec "compiled-one" of
  Left _ -> False
  Right bundle ->
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle) == Right ()

knownProfilesResolve :: Bool
knownProfilesResolve =
  all resolvesLegacy
    [ coreScalarCertificationSpec
    , systemsFieldProjectionCertificationSpec
    , llvmFieldProjectionCertificationSpec
    ]
  && all resolvesRecognizedRecord
    [ systemsRecognizedRecordCertificationSpec
    , llvmRecognizedRecordABICertificationSpec
    , llvmRuntimeSymbolCertificationSpec
    ]
  && knownExactReceiveRocqCertificationSpec
      (rocqSpecProfile llvmExactReceiveCertificationSpec)
      == Just llvmExactReceiveCertificationSpec
  && all resolvesDigest
    [ systemsDigestValidationCertificationSpec
    , llvmDigestValidationCertificationSpec
    ]
  where
    resolvesLegacy spec =
      knownRocqCertificationSpec (rocqSpecProfile spec) == Just spec
    resolvesRecognizedRecord spec =
      knownRecognizedRecordRocqCertificationSpec (rocqSpecProfile spec) == Just spec
    resolvesDigest spec =
      knownDigestValidationRocqCertificationSpec (rocqSpecProfile spec) == Just spec

recognizedRecordProofCertificationCloses :: Bool
recognizedRecordProofCertificationCloses =
  case recognizedRecordProofCandidates of
    Just (systemsProof, abiProof, symbolProof) ->
      verifyPhase0RecognizedRecordProofCertification systemsProof abiProof symbolProof == Right ()
    Nothing -> False

recognizedRecordProofArtifactTamperRejects :: Bool
recognizedRecordProofArtifactTamperRejects =
  case recognizedRecordProofCandidates of
    Nothing -> False
    Just (systemsProof, abiProof, symbolProof) ->
      case phase0RecognizedRecordProofCertification systemsProof abiProof symbolProof of
        Left _ -> False
        Right bundle ->
          let artifact = rocqBundleCertificateArtifact systemsProof
              context0 = recognizedRecordProofCertificationContext bundle
              context = context0
                { verificationAvailableArtifacts = Map.insert
                    (artifactReference artifact)
                    (digestText "tampered-proof-certificate")
                    (verificationAvailableArtifacts context0)
                }
          in case verifyManifest
              context
              (recognizedRecordProofCertificationLedger bundle)
              (recognizedRecordProofCertificationManifest bundle) of
              Left ArtifactDigestMismatch {} -> True
              _ -> False

recognizedRecordProofCandidates
  :: Maybe (RocqCertificationBundle, RocqCertificationBundle, RocqCertificationBundle)
recognizedRecordProofCandidates = do
  systemsProof <- either (const Nothing) Just
    (candidate systemsRecognizedRecordCertificationSpec "systems-compiled")
  abiProof <- either (const Nothing) Just
    (candidate llvmRecognizedRecordABICertificationSpec "abi-compiled")
  symbolProof <- either (const Nothing) Just
    (candidate llvmRuntimeSymbolCertificationSpec "symbol-compiled")
  pure (systemsProof, abiProof, symbolProof)

exactReceiveProofCertificationCloses :: Bool
exactReceiveProofCertificationCloses =
  case exactReceiveProofCandidates of
    Just (exactProof, abiProof, symbolProof) ->
      verifyPhase0ExactReceiveProofCertification exactProof abiProof symbolProof == Right ()
    Nothing -> False

exactReceiveProofArtifactTamperRejects :: Bool
exactReceiveProofArtifactTamperRejects =
  case exactReceiveProofCandidates of
    Nothing -> False
    Just (exactProof, abiProof, symbolProof) ->
      case phase0ExactReceiveProofCertification exactProof abiProof symbolProof of
        Left _ -> False
        Right bundle ->
          let artifact = rocqBundleCertificateArtifact exactProof
              context0 = exactReceiveProofCertificationContext bundle
              context = context0
                { verificationAvailableArtifacts = Map.insert
                    (artifactReference artifact)
                    (digestText "tampered-exact-receive-proof-certificate")
                    (verificationAvailableArtifacts context0)
                }
          in case verifyManifest
              context
              (exactReceiveProofCertificationLedger bundle)
              (exactReceiveProofCertificationManifest bundle) of
              Left ArtifactDigestMismatch {} -> True
              _ -> False

exactReceiveProofCandidates
  :: Maybe (RocqCertificationBundle, RocqCertificationBundle, RocqCertificationBundle)
exactReceiveProofCandidates = do
  exactProof <- either (const Nothing) Just
    (candidate llvmExactReceiveCertificationSpec "exact-receive-compiled")
  abiProof <- either (const Nothing) Just
    (candidate llvmRecognizedRecordABICertificationSpec "abi-compiled")
  symbolProof <- either (const Nothing) Just
    (candidate llvmRuntimeSymbolCertificationSpec "symbol-compiled")
  pure (exactProof, abiProof, symbolProof)

digestValidationProofCertificationCloses :: Bool
digestValidationProofCertificationCloses =
  case digestValidationProofCandidates of
    Just (systemsDigestProof, llvmDigestProof, systemsRecordProof, exactProof, abiProof, symbolProof) ->
      verifyPhase0DigestValidationProofCertification
        systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof == Right ()
    Nothing -> False

digestValidationProofArtifactTamperRejects :: Bool
digestValidationProofArtifactTamperRejects =
  case digestValidationProofCandidates of
    Nothing -> False
    Just (systemsDigestProof, llvmDigestProof, systemsRecordProof, exactProof, abiProof, symbolProof) ->
      case phase0DigestValidationProofCertification
          systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof of
        Left _ -> False
        Right bundle ->
          let artifact = rocqBundleCertificateArtifact systemsDigestProof
              context0 = digestValidationProofCertificationContext bundle
              context = context0
                { verificationAvailableArtifacts = Map.insert
                    (artifactReference artifact)
                    (digestText "tampered-systems-digest-proof-certificate")
                    (verificationAvailableArtifacts context0)
                }
          in case verifyManifest
              context
              (digestValidationProofCertificationLedger bundle)
              (digestValidationProofCertificationManifest bundle) of
              Left ArtifactDigestMismatch {} -> True
              _ -> False

digestValidationProofCandidates
  :: Maybe
      ( RocqCertificationBundle
      , RocqCertificationBundle
      , RocqCertificationBundle
      , RocqCertificationBundle
      , RocqCertificationBundle
      , RocqCertificationBundle
      )
digestValidationProofCandidates = do
  systemsDigestProof <- either (const Nothing) Just
    (candidate systemsDigestValidationCertificationSpec "systems-digest-compiled")
  llvmDigestProof <- either (const Nothing) Just
    (candidate llvmDigestValidationCertificationSpec "llvm-digest-compiled")
  systemsRecordProof <- either (const Nothing) Just
    (candidate systemsRecognizedRecordCertificationSpec "systems-record-compiled")
  exactProof <- either (const Nothing) Just
    (candidate llvmExactReceiveCertificationSpec "exact-receive-compiled")
  abiProof <- either (const Nothing) Just
    (candidate llvmRecognizedRecordABICertificationSpec "abi-compiled")
  symbolProof <- either (const Nothing) Just
    (candidate llvmRuntimeSymbolCertificationSpec "symbol-compiled")
  pure
    ( systemsDigestProof
    , llvmDigestProof
    , systemsRecordProof
    , exactProof
    , abiProof
    , symbolProof
    )

missingTheoremRejects :: Bool
missingTheoremRejects =
  case packageTrustedRocqProof
      coreScalarCertificationSpec
      (ByteString.pack (Text.unpack sourceWithoutLastCoreTheorem))
      (ByteString.pack "compiled") of
    Left (RocqExpectedTheoremMissing "uint_at_modulus_is_invalid") -> True
    _ -> False

wrongMarkerRejects :: Bool
wrongMarkerRejects =
  case packageTrustedRocqProof
      systemsFieldProjectionCertificationSpec
      (ByteString.pack (Text.unpack (validSourceFor coreScalarCertificationSpec)))
      (ByteString.pack "compiled") of
    Left (RocqObligationMarkerMissing "PHIL-SYS-FIELD-PROJ-001") -> True
    _ -> False

compiledObjectIsBound :: Bool
compiledObjectIsBound = case
    ( candidate systemsFieldProjectionCertificationSpec "compiled-one"
    , candidate systemsFieldProjectionCertificationSpec "compiled-two"
    ) of
  (Right first, Right second) ->
    artifactDigest (rocqBundleCertificateArtifact first)
      /= artifactDigest (rocqBundleCertificateArtifact second)
  _ -> False

trustedPackagingNamesPrecondition :: Bool
trustedPackagingNamesPrecondition = case candidate coreScalarCertificationSpec "compiled-one" of
  Left _ -> False
  Right bundle ->
    "trusted-packaging" `Text.isInfixOf`
      rocqCertificateCheckerProfile (rocqBundleCertificate bundle)
      && all
        (Text.isInfixOf "explicit caller precondition" . evidenceChecker)
        (Map.elems (ledgerEvidence (rocqBundleLedger bundle)))

certificateTamperRejects :: Bool
certificateTamperRejects = case candidate llvmFieldProjectionCertificationSpec "compiled-one" of
  Left _ -> False
  Right bundle ->
    let artifact = rocqBundleCertificateArtifact bundle
        context = (rocqBundleVerificationContext bundle)
          { verificationAvailableArtifacts = Map.singleton
              (artifactReference artifact)
              (digestText "tampered")
          }
    in case verifyManifest context (rocqBundleLedger bundle) (rocqBundleManifest bundle) of
        Left ArtifactDigestMismatch {} -> True
        _ -> False

candidate
  :: RocqCertificationSpec
  -> String
  -> Either RocqCertificationError RocqCertificationBundle
candidate spec compiled = packageTrustedRocqProof
  spec
  (ByteString.pack (Text.unpack (validSourceFor spec)))
  (ByteString.pack compiled)

validSourceFor :: RocqCertificationSpec -> Text
validSourceFor spec = Text.unlines
  (marker : map ("Theorem " <>) (rocqSpecTheorems spec))
  where
    ObligationId obligation = rocqSpecObligation spec
    marker = "(* " <> obligation <> " *)"

sourceWithoutLastCoreTheorem :: Text
sourceWithoutLastCoreTheorem = Text.unlines
  (marker : map ("Theorem " <>) (init coreScalarTheorems))
  where
    ObligationId obligation = rocqSpecObligation coreScalarCertificationSpec
    marker = "(* " <> obligation <> " *)"

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS " else "FAIL ") <> label)
  pure result
