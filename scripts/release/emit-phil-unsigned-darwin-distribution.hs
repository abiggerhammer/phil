{-# LANGUAGE OverloadedStrings #-}

-- P11: typed, fail-closed trust profile for UNSIGNED Phil Darwin staging.
-- Keep the established signed/notarized distribution emitter untouched.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types (Digest (..))
import Phil.Handoff.Phase1Manifest (sha256File)
import Phil.Verification.DistributionRelease
import System.Environment (getArgs)
import System.Exit (die)

signedBasis :: Text
signedBasis =
  "native signed philc executable is built by the conventional Haskell and Apple host toolchains"

unsignedBasis :: Text
unsignedBasis =
  "native unsigned philc executable is built by the conventional Haskell and Apple host toolchains; Developer ID signing and notarization are not asserted"

-- Reuse every trusted name/kind/revision and non-build basis. Exactly one
-- known signed-only basis may be replaced; upstream changes fail closed.
unsignedDarwinTrust :: Either String [DistributionTrustBoundary]
unsignedDarwinTrust =
  case filter ((== DistributionBuildToolchainTrust) . distributionTrustKind)
       phase1DarwinDistributionTrust of
    [original]
      | distributionTrustBasis original == signedBasis
      , length phase1DarwinDistributionTrust == 4
      , Set.fromList (map distributionTrustKind phase1DarwinDistributionTrust)
          == requiredPhase1DistributionTrustKinds ->
          Right
            [ if distributionTrustKind boundary == DistributionBuildToolchainTrust
                then boundary {distributionTrustBasis = unsignedBasis}
                else boundary
            | boundary <- phase1DarwinDistributionTrust
            ]
    _ -> Left "unsigned Darwin release: unexpected signed trust-profile shape/basis"

buildUnsigned
  :: Text -> Text -> Digest -> Digest
  -> Either String Phase1DistributionRelease
buildUnsigned version commit handoff compiler = do
  trust <- unsignedDarwinTrust
  either (Left . show) Right $
    buildPhase1DistributionRelease
      "phil" version "aarch64-apple-darwin" commit handoff compiler trust

fileDigest :: FilePath -> IO Digest
fileDigest path = do
  result <- sha256File path
  raw <- either (die . Text.unpack) pure result
  either (die . show) pure (parseSha256Digest raw)

check :: Bool -> String -> IO ()
check condition description =
  unless condition (die ("P11 unsigned Darwin trust self-test: " <> description))

selfTest :: IO ()
selfTest = do
  trust <- either die pure unsignedDarwinTrust
  let signed = phase1DarwinDistributionTrust
      changed = length [() | (before, after) <- zip signed trust, before /= after]
      unchangedFields boundary =
        ( distributionTrustBoundaryId boundary
        , distributionTrustKind boundary
        , distributionTrustName boundary
        , distributionTrustRevision boundary
        )
      testCommit = Text.replicate 40 "a"
      handoff = Digest (Text.replicate 64 "1")
      compiler = Digest (Text.replicate 64 "2")
  check (length trust == 4) "TCB domain changed"
  check (Set.fromList (map distributionTrustKind trust)
           == requiredPhase1DistributionTrustKinds) "TCB kind coverage changed"
  check (changed == 1) "expected exactly one trust basis change"
  check (map unchangedFields signed == map unchangedFields trust)
    "changed a trust ID, kind, name or revision"
  unsigned <- either die pure (buildUnsigned "0.1.0-phase1" testCommit handoff compiler)
  original <- either (die . show) pure $
    buildPhase1DistributionRelease "phil" "0.1.0-phase1"
      "aarch64-apple-darwin" testCommit handoff compiler signed
  let rendered = renderPhase1DistributionRelease unsigned
      model = distributionReleaseTrustBoundaries unsigned
  check (distributionReleaseId unsigned /= distributionReleaseId original)
    "unsigned record reused a signed-record identity"
  check (distributionReleaseHandoffManifestDigest unsigned == handoff
           && distributionReleaseCompilerDigest unsigned == compiler)
    "modified actual handoff/compiler digest bindings"
  check (distributionReleaseSourceCommit unsigned == testCommit
           && distributionReleaseTarget unsigned == "aarch64-apple-darwin")
    "modified exact source/target binding"
  check (Map.size model == 4) "incomplete canonical TCB record"
  check (case Map.lookup (DistributionTrustBoundaryId "build-toolchain") model of
           Just boundary -> distributionTrustBasis boundary == unsignedBasis
           Nothing -> False)
    "unsigned build-toolchain basis not encoded canonically"
  check (Text.isInfixOf unsignedBasis rendered
           && not (Text.isInfixOf signedBasis rendered))
    "rendered unsigned record asserts signing"
  check (parseRenderedDistributionReleaseId rendered
           == Right (distributionReleaseId unsigned))
    "canonical release identity failed to round-trip"
  let forged = [ if distributionTrustKind boundary == DistributionBuildToolchainTrust
                   then boundary {distributionTrustBasis = signedBasis}
                   else boundary
               | boundary <- trust ]
  forgedRelease <- either (die . show) pure $
    buildPhase1DistributionRelease "phil" "0.1.0-phase1"
      "aarch64-apple-darwin" testCommit handoff compiler forged
  check (distributionReleaseId forgedRelease /= distributionReleaseId unsigned)
    "forged signing claim failed to change release identity"
  putStrLn "PASS: P11 unsigned Darwin trust profile and signed-claim negative"

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--self-test"] -> selfTest
    [version, commit, handoffPath, compilerPath] -> do
      handoff <- fileDigest handoffPath
      compiler <- fileDigest compilerPath
      release <- either die pure $
        buildUnsigned (Text.pack version) (Text.pack commit) handoff compiler
      TextIO.putStr (renderPhase1DistributionRelease release)
    _ -> die "usage: emit-phil-unsigned-darwin-distribution.hs --self-test | VERSION SOURCE_COMMIT HANDOFF_PATH COMPILER_PATH"
