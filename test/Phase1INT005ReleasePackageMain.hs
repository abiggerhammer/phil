{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types
  ( AssuranceLedger (..)
  , AssuranceManifest (..)
  , AssuranceUse (..)
  , Digest (..)
  , EvidenceEntry (..)
  )
import Phil.LLVM.IR
  ( LLVMArtifact (..)
  , LLVMEmissionContract (..)
  )
import Phil.Test.Phase1.CertifiedReleaseWitnesses
  ( certifyConventionalFixture
  )
import Phil.Test.Phase1.ManifestWitnesses
  ( RealManifestFixture (..)
  , steveRealManifestFixture
  , uploadRealManifestFixture
  )
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , certifiedReleaseLLVMArtifact
  , certifiedReleaseManifest
  , certifiedReleaseTrustBoundaries
  )
import Phil.Verification.ReleasePackage
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  uploadClient <- TextIO.readFile "examples/upload/client.phil"
  uploadServer <- TextIO.readFile "examples/upload/server.phil"
  stevePut <- TextIO.readFile "examples/steve/put.phil"
  steveGet <- TextIO.readFile "examples/steve/get.phil"
  let uploadFixture = uploadRealManifestFixture uploadClient uploadServer
      steveFixture = steveRealManifestFixture stevePut steveGet
  args <- getArgs
  case args of
    [] -> runChecks uploadFixture steveFixture
    ["emit", "upload"] -> emitPackage uploadFixture
    ["emit", "steve"] -> emitPackage steveFixture
    _ -> do
      putStrLn "usage: Phase1INT005ReleasePackageMain.hs [emit upload|emit steve]"
      exitFailure

runChecks
  :: Either String RealManifestFixture
  -> Either String RealManifestFixture
  -> IO ()
runChecks uploadResult steveResult = do
  upload <- requireFixture "Upload" uploadResult
  steve <- requireFixture "Steve" steveResult
  uploadRelease <- requireRelease "Upload" upload
  steveRelease <- requireRelease "Steve" steve
  uploadPackage <- requirePackage "Upload" upload uploadRelease
  stevePackage <- requirePackage "Steve" steve steveRelease
  results <- sequence
    [ test "INT-005 Upload release package binds exact certified release"
        (packageMatches upload uploadRelease uploadPackage)
    , test "INT-005 Steve release package binds exact certified release"
        (packageMatches steve steveRelease stevePackage)
    , test "INT-005 release package rendering is deterministic"
        (deterministic steve steveRelease stevePackage)
    , test "INT-005 witness release packages have distinct identities"
        (certifiedReleasePackageId uploadPackage /= certifiedReleasePackageId stevePackage)
    , test "INT-005 release package rejects a foreign assurance ledger"
        (foreignLedgerRejected upload steveRelease)
    ]
  if and results then pure () else exitFailure

emitPackage :: Either String RealManifestFixture -> IO ()
emitPackage result = do
  fixture <- requireFixture "requested witness" result
  release <- requireRelease "requested witness" fixture
  package <- requirePackage "requested witness" fixture release
  TextIO.putStr (renderCertifiedReleasePackage package)

requireFixture :: String -> Either String RealManifestFixture -> IO RealManifestFixture
requireFixture label result = case result of
  Left detail -> do
    putStrLn ("FAIL: INT-005 " <> label <> " manifest fixture -- " <> detail)
    exitFailure
  Right fixture -> pure fixture

requireRelease :: String -> RealManifestFixture -> IO CertifiedReleaseArtifact
requireRelease label fixture = case certifyConventionalFixture fixture of
  Left err -> do
    putStrLn ("FAIL: INT-005 " <> label <> " certified release -- " <> show err)
    exitFailure
  Right release -> pure release

requirePackage
  :: String
  -> RealManifestFixture
  -> CertifiedReleaseArtifact
  -> IO CertifiedReleasePackage
requirePackage label fixture release =
  case buildCertifiedReleasePackage (realFixtureLedger fixture) release of
    Left err -> do
      putStrLn ("FAIL: INT-005 " <> label <> " release package -- " <> show err)
      exitFailure
    Right package -> pure package

test :: String -> Bool -> IO Bool
test label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok

packageMatches
  :: RealManifestFixture
  -> CertifiedReleaseArtifact
  -> CertifiedReleasePackage
  -> Bool
packageMatches fixture release package = and
  [ certifiedReleasePackageManifestId package == manifestId manifest
  , certifiedReleasePackageLoweringLedgerRoot package
      == manifestLoweringLedgerRoot manifest
  , certifiedReleasePackageLLVMTargetDigest package
      == llvmContractTargetDigest (llvmArtifactContract llvm)
  , certifiedReleasePackageTrustBoundaryIds package
      == Map.keysSet (certifiedReleaseTrustBoundaries release)
  , certifiedReleasePackageLoweringDecisionCount package > 0
  , certifiedReleasePackageCostRefs package == expectedCostRefs fixture
  , Text.isInfixOf
      ("package\tid=" <> unDigest (certifiedReleasePackageId package)) rendered
  , all (\boundary -> Text.isInfixOf boundary rendered)
      [ "compiler-checker"
      , "llvm-toolchain"
      , "runtime"
      , "providers"
      , "external-checkers"
      , "target-assumptions"
      ]
  , Text.isInfixOf "lowering-decision\t" rendered
  ]
  where
    manifest = certifiedReleaseManifest release
    llvm = certifiedReleaseLLVMArtifact release
    rendered = renderCertifiedReleasePackage package

deterministic
  :: RealManifestFixture
  -> CertifiedReleaseArtifact
  -> CertifiedReleasePackage
  -> Bool
deterministic fixture release expected =
  case buildCertifiedReleasePackage (realFixtureLedger fixture) release of
    Left _ -> False
    Right actual ->
      certifiedReleasePackageId actual == certifiedReleasePackageId expected
        && renderCertifiedReleasePackage actual == renderCertifiedReleasePackage expected

foreignLedgerRejected
  :: RealManifestFixture
  -> CertifiedReleaseArtifact
  -> Bool
foreignLedgerRejected foreignFixture release =
  case buildCertifiedReleasePackage (realFixtureLedger foreignFixture) release of
    Left (ReleasePackageManifestLedgerMismatch _ _) -> True
    Left (ReleasePackageMissingEvidence _) -> True
    Left (ReleasePackageMissingAssuranceUse _) -> True
    Right _ -> False

expectedCostRefs :: RealManifestFixture -> Set Text.Text
expectedCostRefs fixture = Set.union evidenceCosts useCosts
  where
    ledger = realFixtureLedger fixture
    manifest = realFixtureManifest fixture
    evidenceCosts = Set.fromList
      [ costRef
      | entryId <- Set.toAscList (manifestEvidenceEntries manifest)
      , Just entry <- [Map.lookup entryId (ledgerEvidence ledger)]
      , costRef <- evidenceCostRefs entry
      ]
    useCosts = Set.fromList
      [ useCostRef use
      | useId <- Set.toAscList (manifestAssuranceUses manifest)
      , Just use@RetainedRuntimeUse {} <- [Map.lookup useId (ledgerUses ledger)]
      ]
