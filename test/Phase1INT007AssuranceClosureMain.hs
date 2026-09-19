{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types
  ( AssuranceLedger
  , AssuranceManifest (..)
  )
import Phil.Assurance.Verify (verifyManifest)
import Phil.Handoff.Phase1AssuranceClosure
import Phil.Test.Phase1.CertifiedReleaseWitnesses
  ( certifyConventionalFixture
  )
import Phil.Test.Phase1.ManifestWitnesses
  ( RealManifestFixture (..)
  , steveRealManifestFixture
  , uploadRealManifestFixture
  )
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)

data WitnessClosure = WitnessClosure
  { witnessLabel :: String
  , witnessPrefix :: FilePath
  , witnessFixture :: RealManifestFixture
  , witnessTCB :: Phase1ResidualTCB
  }

main :: IO ()
main = do
  uploadClient <- TextIO.readFile "examples/upload/client.phil"
  uploadServer <- TextIO.readFile "examples/upload/server.phil"
  stevePut <- TextIO.readFile "examples/steve/put.phil"
  steveGet <- TextIO.readFile "examples/steve/get.phil"

  upload <- requireWitness
    "Upload"
    "handoff/phase1/witnesses/upload"
    (uploadRealManifestFixture uploadClient uploadServer)
  steve <- requireWitness
    "Steve"
    "handoff/phase1/witnesses/steve"
    (steveRealManifestFixture stevePut steveGet)

  witnessResults <- mapM checkWitness [upload, steve]
  negativeResults <- sequence
    [ test "INT-007 assurance-manifest identity drift fails closed"
        (manifestIdentityDriftRejects upload)
    , test "INT-007 assurance-manifest unknown ledger reference fails closed"
        (unknownEvidenceRejects upload)
    , test "INT-007 residual TCB kind-domain drift fails closed"
        (tcbKindDomainDriftRejects upload)
    ]

  if and witnessResults && and negativeResults
    then pure ()
    else exitFailure

requireWitness
  :: String
  -> FilePath
  -> Either String RealManifestFixture
  -> IO WitnessClosure
requireWitness label prefix result = case result of
  Left detail -> do
    putStrLn ("FAIL: INT-007 " <> label <> " final manifest fixture -- " <> detail)
    exitFailure
  Right fixture ->
    case certifyConventionalFixture fixture of
      Left errorValue -> do
        putStrLn ("FAIL: INT-007 " <> label <> " certified release -- " <> show errorValue)
        exitFailure
      Right release -> pure WitnessClosure
        { witnessLabel = label
        , witnessPrefix = prefix
        , witnessFixture = fixture
        , witnessTCB = derivePhase1ResidualTCB release
        }

checkWitness :: WitnessClosure -> IO Bool
checkWitness witness = do
  let fixture = witnessFixture witness
      manifest = realFixtureManifest fixture
      ledger = realFixtureLedger fixture
      context = realFixtureContext fixture
      manifestPath = witnessPrefix witness <> "-assurance-manifest-v1.tsv"
      tcbPath = witnessPrefix witness <> "-residual-tcb-v1.tsv"

  manifestResult <- compareManifest
    (witnessLabel witness) manifestPath ledger manifest
  replayResult <- case verifyManifest context ledger manifest of
    Left errorValue -> do
      putStrLn ("FAIL: INT-007 " <> witnessLabel witness
        <> " final AssuranceManifest replay -- " <> show errorValue)
      pure False
    Right () -> do
      putStrLn ("PASS: INT-007 " <> witnessLabel witness
        <> " final AssuranceManifest replays exactly")
      pure True

  tcbResult <- compareTCB
    (witnessLabel witness) tcbPath (witnessTCB witness)

  let bound =
        residualTCBManifestId (witnessTCB witness) == manifestId manifest
  if bound
    then putStrLn ("PASS: INT-007 " <> witnessLabel witness
      <> " residual TCB binds the exact final AssuranceManifest")
    else putStrLn ("FAIL: INT-007 " <> witnessLabel witness
      <> " residual TCB manifest binding drift")

  pure (manifestResult && replayResult && tcbResult && bound)

compareManifest
  :: String
  -> FilePath
  -> AssuranceLedger
  -> AssuranceManifest
  -> IO Bool
compareManifest label path ledger actual = do
  expectedSource <- TextIO.readFile path
  case decodePhase1AssuranceManifest ledger expectedSource of
    Left errorValue -> do
      writeDiscovery label "assurance-manifest" (renderPhase1AssuranceManifest actual)
      putStrLn ("FAIL: INT-007 " <> label
        <> " final AssuranceManifest decode/drift -- " <> show errorValue)
      pure False
    Right expected
      | expected == actual -> do
          putStrLn ("PASS: INT-007 " <> label
            <> " final AssuranceManifest reconstructs exactly")
          pure True
      | otherwise -> do
          writeDiscovery label "assurance-manifest" (renderPhase1AssuranceManifest actual)
          putStrLn ("FAIL: INT-007 " <> label
            <> " final AssuranceManifest drift")
          pure False

compareTCB :: String -> FilePath -> Phase1ResidualTCB -> IO Bool
compareTCB label path actual = do
  expectedSource <- TextIO.readFile path
  case decodePhase1ResidualTCB expectedSource of
    Left errorValue -> do
      writeDiscovery label "residual-tcb" (renderPhase1ResidualTCB actual)
      putStrLn ("FAIL: INT-007 " <> label
        <> " residual TCB decode/drift -- " <> show errorValue)
      pure False
    Right expected
      | expected == actual -> do
          putStrLn ("PASS: INT-007 " <> label
            <> " residual TCB reconstructs exactly")
          pure True
      | otherwise -> do
          writeDiscovery label "residual-tcb" (renderPhase1ResidualTCB actual)
          putStrLn ("FAIL: INT-007 " <> label <> " residual TCB drift")
          pure False

writeDiscovery :: String -> String -> Text.Text -> IO ()
writeDiscovery label kind rendered = do
  let path = "dist/int007-assurance-closure-discovery/"
        <> label <> "-" <> kind <> "-v1.tsv"
  createDirectoryIfMissing True (takeDirectory path)
  TextIO.writeFile path rendered

manifestIdentityDriftRejects :: WitnessClosure -> Either String ()
manifestIdentityDriftRejects witness =
  expectManifestFailure ledger changed
  where
    fixture = witnessFixture witness
    ledger = realFixtureLedger fixture
    source = renderPhase1AssuranceManifest (realFixtureManifest fixture)
    changed = replaceFirstDigest "manifest-id" source

unknownEvidenceRejects :: WitnessClosure -> Either String ()
unknownEvidenceRejects witness =
  expectManifestFailure ledger changed
  where
    fixture = witnessFixture witness
    ledger = realFixtureLedger fixture
    source = renderPhase1AssuranceManifest (realFixtureManifest fixture)
    changed = source <> "evidence\tevidence.int007.unknown\n"

tcbKindDomainDriftRejects :: WitnessClosure -> Either String ()
tcbKindDomainDriftRejects witness =
  case Text.lines source of
    header : manifestLine : profileLine : rest ->
      expectTCBFailure (Text.unlines
        ([header, manifestLine, profileLine] <> filter (not . isRuntimeKind) rest))
    _ -> Left "unexpected residual TCB rendering"
  where
    source = renderPhase1ResidualTCB (witnessTCB witness)
    isRuntimeKind line = line == "required-kind\truntime"

replaceFirstDigest :: Text.Text -> Text.Text -> Text.Text
replaceFirstDigest key source = Text.unlines (map replaceLine (Text.lines source))
  where
    replaceLine line
      | (key <> "\t") `Text.isPrefixOf` line =
          key <> "\tsha256:" <> Text.replicate 64 "0"
      | otherwise = line

expectManifestFailure
  :: AssuranceLedger
  -> Text.Text
  -> Either String ()
expectManifestFailure ledger source =
  case decodePhase1AssuranceManifest ledger source of
    Left _ -> Right ()
    Right value -> Left
      ("expected final AssuranceManifest rejection, decoded: " <> show value)

expectTCBFailure :: Text.Text -> Either String ()
expectTCBFailure source = case decodePhase1ResidualTCB source of
  Left _ -> Right ()
  Right value -> Left ("expected residual TCB rejection, decoded: " <> show value)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
