{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Phil.Assurance.Types (AssuranceManifest (..), deriveManifestId)
import Phil.Assurance.Verify (verifyManifest)
import Phil.LLVM.IR (LLVMArtifact (..), LLVMEmissionContract (..))
import Phil.Systems.StageClosure (verifyStageClosureBundle)
import Phil.Test.Phase1.CertifiedReleaseWitnesses
import Phil.Test.Phase1.ManifestWitnesses
import Phil.Verification.CertifiedRelease
import Phil.Verification.ReleasePackage
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>))

-- All positive manifests, stages and LLVM objects come from the actual fixed
-- Upload/Steve source-checking factories. Cross-pairs use independently valid
-- complete objects, not malformed stages or invented certification results.
-- The source-to-fixed-witness mapping and residual trust are caller premises;
-- this driver does not claim a general source compiler or inspect LLVM internals.

type Check = Either String ()
right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Check
ensure True _ = Right ()
ensure False detail = Left detail
exact :: (Eq e, Show e, Show a) => e -> Either e a -> Check
exact expected outcome = case outcome of
  Left actual | actual == expected -> Right ()
  _ -> Left ("expected " <> show expected <> ", got " <> show outcome)

valid :: RealManifestFixture -> Either String CertifiedReleaseArtifact
valid fixture = do
  right $ verifyManifest (realFixtureContext fixture) (realFixtureLedger fixture)
    (realFixtureManifest fixture)
  right $ verifyStageClosureBundle (realFixtureStage fixture)
  right $ certifyConventionalFixture fixture

retained :: RealManifestFixture -> Check
retained fixture = do
  certified <- valid fixture
  ensure (certifiedReleaseManifest certified == realFixtureManifest fixture
    && certifiedReleaseStageClosure certified == realFixtureStage fixture
    && certifiedReleaseLLVMArtifact certified == fixtureLLVMArtifact fixture
    && certifiedReleaseProfile certified == conventionalReleaseProfile (realFixtureManifest fixture)
    && Map.elems (certifiedReleaseTrustBoundaries certified)
      == Map.elems (Map.fromList [(releaseTrustBoundaryId t,t) | t <- conventionalTrust]))
    "certification changed a retained input or trust record"

crossStage :: RealManifestFixture -> RealManifestFixture -> Check
crossStage original other = do
  _ <- valid original
  foreignRelease <- valid other
  let manifest = realFixtureManifest original
      foreignLLVM = certifiedReleaseLLVMArtifact foreignRelease
      wanted = llvmContractSourceDigest (llvmArtifactContract foreignLLVM)
      got = manifestImplementationDigest manifest
  ensure (wanted /= got) "stage fixtures do not have different Systems identities"
  exact (CertifiedReleaseManifestImplementationDigestMismatch wanted got) $
    certifyReleaseArtifact (conventionalReleaseProfile manifest)
      (realFixtureContext original) (realFixtureLedger original) manifest
      (certifiedReleaseStageClosure foreignRelease) foreignLLVM conventionalTrust

crossLLVM :: RealManifestFixture -> RealManifestFixture -> Check
crossLLVM original other = do
  _ <- valid original
  foreignRelease <- valid other
  let manifest = realFixtureManifest original
      foreignLLVM = certifiedReleaseLLVMArtifact foreignRelease
      wanted = manifestImplementationDigest manifest
      got = llvmContractSourceDigest (llvmArtifactContract foreignLLVM)
  ensure (wanted /= got) "LLVM source identities are not distinct"
  exact (CertifiedReleaseLLVMSourceDigestMismatch wanted got) $
    certifyReleaseArtifact (conventionalReleaseProfile manifest)
      (realFixtureContext original) (realFixtureLedger original) manifest
      (realFixtureStage original) foreignLLVM conventionalTrust

package :: RealManifestFixture -> Either String CertifiedReleasePackage
package fixture = valid fixture >>= right . buildCertifiedReleasePackage (realFixtureLedger fixture)

packageIdentity :: RealManifestFixture -> RealManifestFixture -> Check
packageIdentity upload steve = do
  left <- package upload
  rightPackage <- package steve
  ensure (certifiedReleasePackageId left /= certifiedReleasePackageId rightPackage)
    "independent witness packages lost their distinct identities"
  ensure (certifiedReleasePackageManifestId left == manifestId (realFixtureManifest upload)
    && certifiedReleasePackageLLVMTargetDigest left
      == llvmContractTargetDigest (llvmArtifactContract (fixtureLLVMArtifact upload))
    && certifiedReleasePackageLoweringLedgerRoot left
      == manifestLoweringLedgerRoot (realFixtureManifest upload)
    && certifiedReleasePackageLoweringDecisionCount left > 0)
    "package does not retain the actual release coordinates"

foreignLedger :: RealManifestFixture -> RealManifestFixture -> Check
foreignLedger original other = do
  release <- valid original
  _ <- valid other
  let manifest = certifiedReleaseManifest release
      ledger = realFixtureLedger other
      expected = manifestId manifest
      actual = deriveManifestId ledger manifest
  ensure (actual /= expected) "foreign ledger did not change this manifest's derivation"
  exact (ReleasePackageManifestLedgerMismatch expected actual) $
    buildCertifiedReleasePackage ledger release

wrongProfile :: RealManifestFixture -> Check
wrongProfile fixture = do
  _ <- valid fixture
  let manifest = realFixtureManifest fixture
      name = "independent-other-target"
      profile = (conventionalReleaseProfile manifest) { releaseProfileManifestTarget = name }
  exact (CertifiedReleaseManifestTargetMismatch name (manifestTarget manifest)) $
    certifyReleaseArtifact profile (realFixtureContext fixture) (realFixtureLedger fixture)
      manifest (realFixtureStage fixture) (fixtureLLVMArtifact fixture) conventionalTrust

missingTrust :: RealManifestFixture -> Check
missingTrust fixture = do
  _ <- valid fixture
  let manifest = realFixtureManifest fixture
      profile = conventionalReleaseProfile manifest
      trust = filter ((/= RuntimeTrust) . releaseTrustKind) conventionalTrust
      kinds = Set.fromList (map releaseTrustKind trust)
  exact (CertifiedReleaseTrustKindDomainMismatch (releaseProfileRequiredTrustKinds profile) kinds) $
    certifyReleaseArtifact profile (realFixtureContext fixture) (realFixtureLedger fixture)
      manifest (realFixtureStage fixture) (fixtureLLVMArtifact fixture) trust

whitespacePreservation :: Text.Text -> Text.Text -> RealManifestFixture -> Check
whitespacePreservation client server original = do
  updated <- right $ uploadRealManifestFixture (client <> "\n") ("\n" <> server)
  release <- valid updated
  ensure (certifiedReleaseStageClosure release == realFixtureStage original
    && certifiedReleaseLLVMArtifact release == fixtureLLVMArtifact original)
    "legitimate whitespace changed the fixed witness implementation"
  -- Deliberately no assumption that textual source hashes equal semantic IDs.

repeatedPackage :: RealManifestFixture -> Check
repeatedPackage fixture = do
  a <- package fixture
  b <- package fixture
  ensure (a == b && renderCertifiedReleasePackage a == renderCertifiedReleasePackage b)
    "same exact release inputs did not produce the same package"

main :: IO ()
main = do
  args <- getArgs
  out <- case args of
    [directory] -> pure directory
    _ -> fail "usage: ReleaseAssociationReview EXPECTED_OUTPUT_DIRECTORY"
  client <- TIO.readFile "examples/upload/client.phil"
  server <- TIO.readFile "examples/upload/server.phil"
  putSource <- TIO.readFile "examples/steve/put.phil"
  getSource <- TIO.readFile "examples/steve/get.phil"
  upload <- either fail pure (uploadRealManifestFixture client server)
  steve <- either fail pure (steveRealManifestFixture putSource getSource)
  outcomes <- sequence
    [ test "C01" "actual Upload certification retains exact inputs" (retained upload)
    , test "C02" "actual Steve comparison independently certifies" (retained steve)
    , test "C03" "package coordinates retain their correct distinct domains" (packageIdentity upload steve)
    , test "C04" "Upload manifest rejects independently valid Steve stage" (crossStage upload steve)
    , test "C05" "Steve manifest rejects independently valid Upload stage" (crossStage steve upload)
    , test "C06" "Upload stage rejects independently valid Steve LLVM" (crossLLVM upload steve)
    , test "C07" "Steve stage rejects independently valid Upload LLVM" (crossLLVM steve upload)
    , test "C08" "exact package rejects a separately valid foreign ledger" (foreignLedger steve upload)
    , test "C09" "manifest target remains tied to the supplied release profile" (wrongProfile upload)
    , test "C10" "required trust kind cannot disappear" (missingTrust upload)
    , test "C11" "legitimate source whitespace remains admissible" (whitespacePreservation client server upload)
    , test "C12" "repeat construction from exact inputs is deterministic" (repeatedPackage upload)
    ]
  createDirectoryIfMissing True out
  mapM_ (writeExpected out) [("upload",upload),("steve",steve)]
  putStrLn "COMPLETE association_groups=12"
  unless (and outcomes) exitFailure

writeExpected :: FilePath -> (String, RealManifestFixture) -> IO ()
writeExpected out (name,fixture) = do
  release <- either fail pure (valid fixture)
  metadata <- either fail pure (package fixture)
  TIO.writeFile (out </> (name <> ".ll")) (llvmArtifactText (certifiedReleaseLLVMArtifact release))
  TIO.writeFile (out </> (name <> ".release-package")) (renderCertifiedReleasePackage metadata)
  writeFile (out </> (name <> ".identities.txt")) (unlines
    [ "manifest=" <> show (manifestId (certifiedReleaseManifest release))
    , "systems=" <> show (manifestImplementationDigest (certifiedReleaseManifest release))
    , "lowering=" <> show (manifestLoweringLedgerRoot (certifiedReleaseManifest release))
    , "llvm-module=" <> show (certifiedReleasePackageLLVMTargetDigest metadata)
    , "package=" <> show (certifiedReleasePackageId metadata)
    ])

test :: String -> String -> Check -> IO Bool
test key label outcome = case outcome of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
