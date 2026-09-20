{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest (..))
import Phil.Verification.DistributionRelease
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-011 Linux distribution release identity is deterministic"
        deterministicRelease
    , test "INT-011 distribution release binds exact compiler and handoff digests"
        exactBindings
    , test "INT-011 distribution release rejects malformed source commit"
        malformedCommitRejects
    , test "INT-011 distribution release rejects duplicate TCB identity"
        duplicateTrustRejects
    , test "INT-011 distribution release requires the complete TCB kind domain"
        missingTrustKindRejects
    , test "INT-011 archive binding is deterministic and exact"
        deterministicArchiveBinding
    , test "INT-011 rendered release ID round-trips independently"
        renderedReleaseIdRoundTrips
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

deterministicRelease :: Either String ()
deterministicRelease = do
  first <- releaseFixture
  second <- releaseFixture
  assert (first == second) "same distribution inputs produced distinct release objects"
  assert
    (renderPhase1DistributionRelease first == renderPhase1DistributionRelease second)
    "same distribution inputs produced distinct canonical rendering"

exactBindings :: Either String ()
exactBindings = do
  release <- releaseFixture
  assert
    (distributionReleaseHandoffManifestDigest release == handoffDigest)
    "release changed frozen handoff manifest identity"
  assert
    (distributionReleaseCompilerDigest release == compilerDigest)
    "release changed packaged compiler identity"
  assert
    (distributionReleaseTarget release == "x86_64-unknown-linux-gnu")
    "release changed selected distribution target"
  assert
    (distributionReleaseSourceCommit release == sourceCommit)
    "release changed source commit"
  assert
    (Map.keysSet (distributionReleaseTrustBoundaries release)
      == Set.fromList
          [ DistributionTrustBoundaryId "compiler-checker"
          , DistributionTrustBoundaryId "build-toolchain"
          , DistributionTrustBoundaryId "llvm-toolchain"
          , DistributionTrustBoundaryId "target-assumptions"
          ])
    "release changed explicit residual distribution TCB"

malformedCommitRejects :: Either String ()
malformedCommitRejects =
  case buildPhase1DistributionRelease
      packageName version target "not-a-commit"
      handoffDigest compilerDigest phase1LinuxDistributionTrust of
    Left DistributionReleaseMalformedSourceCommit {} -> Right ()
    other -> Left ("malformed source commit did not reject exactly: " <> show other)

duplicateTrustRejects :: Either String ()
duplicateTrustRejects =
  case phase1LinuxDistributionTrust of
    [] -> Left "Linux trust fixture unexpectedly empty"
    first : _ ->
      case buildPhase1DistributionRelease
          packageName version target sourceCommit
          handoffDigest compilerDigest
          (phase1LinuxDistributionTrust <> [first]) of
        Left (DistributionReleaseDuplicateTrustBoundary duplicateId)
          | duplicateId == distributionTrustBoundaryId first -> Right ()
        other -> Left ("duplicate distribution trust identity did not reject: " <> show other)

missingTrustKindRejects :: Either String ()
missingTrustKindRejects =
  let reduced = filter
        ((/= DistributionTargetAssumptionTrust) . distributionTrustKind)
        phase1LinuxDistributionTrust
      actualKinds = Set.delete
        DistributionTargetAssumptionTrust
        requiredPhase1DistributionTrustKinds
  in case buildPhase1DistributionRelease
      packageName version target sourceCommit
      handoffDigest compilerDigest reduced of
      Left (DistributionReleaseTrustKindDomainMismatch expected actual)
        | expected == requiredPhase1DistributionTrustKinds
        , actual == actualKinds -> Right ()
      other -> Left ("incomplete distribution trust domain did not reject: " <> show other)

deterministicArchiveBinding :: Either String ()
deterministicArchiveBinding = do
  release <- releaseFixture
  first <- mapLeft show $ buildPhase1DistributionArchive
    (distributionReleaseId release)
    archiveName
    archiveDigest
    packageManifestDigest
  second <- mapLeft show $ buildPhase1DistributionArchive
    (distributionReleaseId release)
    archiveName
    archiveDigest
    packageManifestDigest
  assert (first == second) "same archive inputs produced distinct bindings"
  assert
    (distributionArchiveReleaseId first == distributionReleaseId release)
    "archive binding changed distribution release identity"
  assert
    (distributionArchiveDigest first == archiveDigest)
    "archive binding changed archive digest"
  assert
    (distributionArchivePackageManifestDigest first == packageManifestDigest)
    "archive binding changed package-manifest digest"
  assert
    (renderPhase1DistributionArchive first == renderPhase1DistributionArchive second)
    "same archive inputs produced distinct canonical rendering"

renderedReleaseIdRoundTrips :: Either String ()
renderedReleaseIdRoundTrips = do
  release <- releaseFixture
  parsed <- mapLeft show $
    parseRenderedDistributionReleaseId (renderPhase1DistributionRelease release)
  assert
    (parsed == distributionReleaseId release)
    "rendered release did not expose the exact canonical release identity"

releaseFixture :: Either String Phase1DistributionRelease
releaseFixture = mapLeft show $ buildPhase1DistributionRelease
  packageName version target sourceCommit
  handoffDigest compilerDigest phase1LinuxDistributionTrust

packageName, version, target, sourceCommit, archiveName :: Text.Text
packageName = "phil"
version = "0.1.0-phase1"
target = "x86_64-unknown-linux-gnu"
sourceCommit = Text.replicate 40 "a"
archiveName = "phil-0.1.0-phase1-x86_64-linux.tar.gz"

handoffDigest, compilerDigest, archiveDigest, packageManifestDigest :: Digest
handoffDigest = digestOf '1'
compilerDigest = digestOf '2'
archiveDigest = digestOf '3'
packageManifestDigest = digestOf '4'

digestOf :: Char -> Digest
digestOf character = Digest (Text.replicate 64 (Text.singleton character))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
