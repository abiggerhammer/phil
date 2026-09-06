{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.LLVM
import Phil.LLVM.BeginPolicyChoiceProofCertification
import Phil.LLVM.ExactSendProofCertification
import Phil.LLVM.HelloPolicyValidationProofCertification
import Phil.LLVM.PayloadCancelChoiceProofCertification
import Phil.LLVM.VersionSessionChoiceLoweringProofCertification
import Phil.LLVM.VersionSessionChoiceProofBoundCertification
import Phil.LLVM.VersionSessionChoiceProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let root = "rocq-exact-send" </> "proof" </> "Phil"
      output = "exact-send-certificates"

  systemsExactSendProof <- certify systemsExactSendCertificationSpec
    (root </> "Systems" </> "ExactSend.v")
    (root </> "Systems" </> "ExactSend.vo")
  llvmExactSendProof <- certify llvmExactSendCertificationSpec
    (root </> "LLVM" </> "ExactSend.v")
    (root </> "LLVM" </> "ExactSend.vo")

  systemsHelloPolicyProof <- certify systemsHelloPolicyValidationCertificationSpec
    (root </> "Systems" </> "HelloPolicyValidation.v")
    (root </> "Systems" </> "HelloPolicyValidation.vo")
  llvmHelloPolicyProof <- certify llvmHelloPolicyValidationCertificationSpec
    (root </> "LLVM" </> "HelloPolicyValidation.v")
    (root </> "LLVM" </> "HelloPolicyValidation.vo")

  systemsBeginPolicyProof <- certify systemsBeginPolicyChoiceCertificationSpec
    (root </> "Systems" </> "BeginPolicySessionChoice.v")
    (root </> "Systems" </> "BeginPolicySessionChoice.vo")
  llvmBeginPolicyProof <- certify llvmBeginPolicyChoiceCertificationSpec
    (root </> "LLVM" </> "BeginPolicyChoice.v")
    (root </> "LLVM" </> "BeginPolicyChoice.vo")

  systemsOperandsProof <- certify systemsVersionChoiceOperandsCertificationSpec
    (root </> "Systems" </> "VersionChoiceOperands.v")
    (root </> "Systems" </> "VersionChoiceOperands.vo")
  llvmLoweringProof <- certify llvmVersionSessionChoiceLoweringCertificationSpec
    (root </> "LLVM" </> "VersionSessionChoiceLowering.v")
    (root </> "LLVM" </> "VersionSessionChoiceLowering.vo")
  systemsVersionProof <- certify systemsVersionSessionChoiceCertificationSpec
    (root </> "Systems" </> "VersionSessionChoice.v")
    (root </> "Systems" </> "VersionSessionChoice.vo")

  systemsPayloadCancelProof <- certify systemsPayloadCancelChoiceCertificationSpec
    (root </> "Systems" </> "PayloadCancelChoice.v")
    (root </> "Systems" </> "PayloadCancelChoice.vo")
  llvmPayloadCancelProof <- certify llvmPayloadCancelChoiceCertificationSpec
    (root </> "LLVM" </> "PayloadCancelChoice.v")
    (root </> "LLVM" </> "PayloadCancelChoice.vo")
  systemsFinalProof <- certify systemsFinalResponseCertificationSpec
    (root </> "Systems" </> "FinalResponse.v")
    (root </> "Systems" </> "FinalResponse.vo")
  llvmFinalProof <- certify llvmFinalResponseCertificationSpec
    (root </> "LLVM" </> "FinalResponseReceive.v")
    (root </> "LLVM" </> "FinalResponseReceive.vo")
  systemsRejectedProof <- certify systemsRejectedResponseCertificationSpec
    (root </> "Systems" </> "RejectedResponse.v")
    (root </> "Systems" </> "RejectedResponse.vo")
  llvmRejectedProof <- certify llvmRejectedResponseCertificationSpec
    (root </> "LLVM" </> "RejectedResponse.v")
    (root </> "LLVM" </> "RejectedResponse.vo")
  systemsAcceptedProof <- certify systemsAcceptedResponseCertificationSpec
    (root </> "Systems" </> "AcceptedResponse.v")
    (root </> "Systems" </> "AcceptedResponse.vo")
  llvmAcceptedProof <- certify llvmAcceptedResponseCertificationSpec
    (root </> "LLVM" </> "AcceptedResponse.v")
    (root </> "LLVM" </> "AcceptedResponse.vo")
  systemsStorageProof <- certify systemsStorageCertificationSpec
    (root </> "Systems" </> "Storage.v")
    (root </> "Systems" </> "Storage.vo")
  llvmStorageProof <- certify llvmStorageCertificationSpec
    (root </> "LLVM" </> "Storage.v")
    (root </> "LLVM" </> "Storage.vo")
  systemsDigestProof <- certify systemsDigestValidationCertificationSpec
    (root </> "Systems" </> "DigestValidation.v")
    (root </> "Systems" </> "DigestValidation.vo")
  llvmDigestProof <- certify llvmDigestValidationCertificationSpec
    (root </> "LLVM" </> "DigestValidation.v")
    (root </> "LLVM" </> "DigestValidation.vo")
  systemsRecordProof <- certify systemsRecognizedRecordCertificationSpec
    (root </> "Systems" </> "RecognizedRecord.v")
    (root </> "Systems" </> "RecognizedRecord.vo")
  exactProof <- certify llvmExactReceiveCertificationSpec
    (root </> "LLVM" </> "ExactReceive.v")
    (root </> "LLVM" </> "ExactReceive.vo")
  abiProof <- certify llvmRecognizedRecordABICertificationSpec
    (root </> "LLVM" </> "RecognizedRecordABI.v")
    (root </> "LLVM" </> "RecognizedRecordABI.vo")
  symbolProof <- certify llvmRuntimeSymbolCertificationSpec
    (root </> "LLVM" </> "RuntimeSymbolIdentity.v")
    (root </> "LLVM" </> "RuntimeSymbolIdentity.vo")

  payloadPredecessor <- case phase0PayloadCancelChoiceProofCertification
      systemsPayloadCancelProof llvmPayloadCancelProof
      systemsFinalProof llvmFinalProof
      systemsRejectedProof llvmRejectedProof
      systemsAcceptedProof llvmAcceptedProof
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof of
    Left err -> failWith ("predecessor PHIL-LLVM-CERT-009 reproduction failed: " <> show err)
    Right bundle -> pure bundle

  versionPredecessor <- case phase0VersionSessionChoiceProofBoundCertification
      systemsOperandsProof llvmLoweringProof systemsVersionProof payloadPredecessor of
    Left err -> failWith ("predecessor PHIL-LLVM-CERT-010 reproduction failed: " <> show err)
    Right bundle -> pure bundle

  beginPredecessor <- case phase0BeginPolicyChoiceProofCertification
      systemsBeginPolicyProof llvmBeginPolicyProof versionPredecessor of
    Left err -> failWith ("predecessor PHIL-LLVM-CERT-011 reproduction failed: " <> show err)
    Right bundle -> pure bundle

  helloPredecessor <- case phase0HelloPolicyValidationProofCertification
      systemsHelloPolicyProof llvmHelloPolicyProof beginPredecessor of
    Left err -> failWith ("predecessor PHIL-LLVM-CERT-012 reproduction failed: " <> show err)
    Right bundle -> pure bundle

  final <- case phase0ExactSendProofCertification
      systemsExactSendProof llvmExactSendProof helloPredecessor of
    Left err -> failWith ("proof-bound PHIL-LLVM-CERT-013 failed: " <> show err)
    Right bundle -> pure bundle

  mapM_ (uncurry (writeProofCertificate output))
    [ ("PHIL-SYS-EXACT-SEND-001.rocq.cert", systemsExactSendProof)
    , ("PHIL-LLVM-EXACT-SEND-001.rocq.cert", llvmExactSendProof)
    ]

  let predecessorText = renderHelloPolicyValidationProofCertification helloPredecessor
      predecessorArtifact = helloPolicyProofArtifact helloPredecessor
      finalText = renderExactSendProofCertification final
      finalArtifact = exactSendProofArtifact final
  ByteString.writeFile (output </> "PHIL-LLVM-CERT-012.proof-bound.cert")
    (TextEncoding.encodeUtf8 predecessorText)
  ByteString.writeFile (output </> "PHIL-LLVM-CERT-013.proof-bound.cert")
    (TextEncoding.encodeUtf8 finalText)

  putStrLn "reproduced proof-bound PHIL-LLVM-CERT-012 predecessor authority"
  putStrLn ("predecessor certificate sha256: " <>
    Text.unpack (unDigest (artifactDigest predecessorArtifact)))
  putStrLn "certified PHIL-LLVM-CERT-013 over current client-outbound successor"
  putStrLn ("certificate artifact: " <>
    Text.unpack (unArtifactRef (artifactReference finalArtifact)))
  putStrLn ("certificate sha256: " <>
    Text.unpack (unDigest (artifactDigest finalArtifact)))

certify :: RocqCertificationSpec -> FilePath -> FilePath -> IO RocqCertificationBundle
certify spec sourcePath objectPath = do
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case packageTrustedRocqProof spec sourceBytes objectBytes of
    Left err -> failWith ("Rocq certification failed: " <> show err)
    Right bundle -> pure bundle

writeProofCertificate :: FilePath -> FilePath -> RocqCertificationBundle -> IO ()
writeProofCertificate output name bundle = do
  let text = renderRocqProofCertificate (rocqBundleCertificate bundle)
      artifact = rocqBundleCertificateArtifact bundle
  ByteString.writeFile (output </> name) (TextEncoding.encodeUtf8 text)
  putStrLn
    ("proof certificate: " <>
      Text.unpack (unArtifactRef (artifactReference artifact)) <>
      " sha256=" <> Text.unpack (unDigest (artifactDigest artifact)))

(</>) :: FilePath -> FilePath -> FilePath
left </> right = left <> "/" <> right

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
