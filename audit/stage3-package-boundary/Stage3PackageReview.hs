{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Exception (IOException, try)
import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified PackageFixture as P
import qualified PingFixture as F
import Phil.Assurance.Types (Digest)
import Phil.Core.Authority (AuthorityExerciseSource (..))
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static (DeclarationKey (..), DefinitionRevision (..))
import Phil.Handoff.Phase1Manifest (sha256File)
import Phil.Handoff.Phase1VerificationBundle
import Phil.Handoff.Phase1WholeSourceVerification
import Phil.IO.Console (ConsoleWriteOutcome (..))
import Phil.Surface.GrammarV1.BoundedPingRuntime
import Phil.Surface.GrammarV1.BoundedPingSourceValues
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import Phil.Verification (AssurancePolicyRevision (..), VerificationObligationGraph (..))
import Phil.Verification.Bundle (VerificationBundle (..))
import Phil.Verification.GrammarV1WholeSource
import System.Directory (copyFile, createDirectoryIfMissing, makeAbsolute, withCurrentDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>), takeDirectory)

-- The two imported modules are unchanged permanent tests apart from their
-- module/export names. checkStage is the actual descriptor acceptance caller.
-- Runtime fixture roots, count association, console outcomes and regenerated
-- reference summaries remain explicit audit packaging, not a compiler export.
-- Only scratch copies of the four shipped Stage 3 files are modified.

descriptorPath, primaryPath, supplementPath, summaryPath :: FilePath
descriptorPath = "handoff/phase1/ping/stage3-verification-v1.tsv"
primaryPath = "handoff/phase1/ping/stage3-bounded.phil"
supplementPath = "handoff/phase1/ping/stage3-round.phil"
summaryPath = "handoff/phase1/ping/stage3-bounded-verification-bundle-v1.tsv"

require :: Bool -> String -> IO ()
require condition detail = unless condition (ioError (userError detail))

must :: Show e => Either e a -> IO a
must = either (ioError . userError . show) pure

fresh :: FilePath -> FilePath -> String -> IO FilePath
fresh source scratch name = do
  let root = scratch </> name
  forM_ [descriptorPath,primaryPath,supplementPath,summaryPath] $ \path -> do
    createDirectoryIfMissing True (takeDirectory (root </> path))
    copyFile (source </> path) (root </> path)
  pure root

descriptor :: FilePath -> IO Phase1WholeSourceVerificationDescriptor
descriptor root = TIO.readFile (root </> descriptorPath)
  >>= must . decodePhase1WholeSourceVerificationDescriptor

materialize :: FilePath -> IO (GrammarV1WholeSourceVerificationSpec,Text)
materialize root = descriptor root
  >>= materializePhase1WholeSourceVerificationDescriptor root >>= must

bundleAt :: FilePath -> IO VerificationBundle
bundleAt root = materialize root >>= must . grammarV1WholeSourceVerificationBundle . fst

entry :: FilePath -> String -> IO Bool
entry root label = withCurrentDirectory root (P.checkStage label descriptorPath)

alter :: FilePath -> FilePath -> (Text -> Text) -> IO ()
alter root path transform = do
  original <- TIO.readFile (root </> path)
  let changed = transform original
  require (changed /= original) ("fixture made no change: " <> path)
  TIO.writeFile (root </> path) changed

refreshDigest :: FilePath -> FilePath -> IO ()
refreshDigest root path = do
  digest <- sha256File (root </> path) >>= must
  source <- TIO.readFile (root </> descriptorPath)
  let rows = Text.lines source
      matches row = case Text.splitOn "\t" row of
        [tag,_,p,_] -> tag `elem` ["primary","supplemental"] && p == Text.pack path
        _ -> False
      update row = case Text.splitOn "\t" row of
        [tag,label,p,_] | matches row -> Text.intercalate "\t" [tag,label,p,digest]
        _ -> row
  require (length (filter matches rows) == 1) "digest update lacks one exact source record"
  TIO.writeFile (root </> descriptorPath) (Text.unlines (map update rows))

regenerateReference :: FilePath -> IO ()
regenerateReference root = do
  b <- bundleAt root
  -- This intentionally models a package author's refreshed reference output.
  -- Agreement with it is not independent proof of executable body semantics.
  TIO.writeFile (root </> summaryPath)
    (renderPhase1VerificationBundleSummary (derivePhase1VerificationBundleSummary b))

emptyAssurance :: VerificationBundle -> IO ()
emptyAssurance b = do
  let graph = verificationBundleObligationGraph b
  require (Map.null (verificationGraphNodes graph)
    && Set.null (verificationGraphDependencies graph)
    && Set.null (verificationGraphCertificationScope graph)
    && Map.null (verificationBundleAcceptedEvidence b))
    "bounded reconstruction invented residual/evidence credit"

sourceDigest :: VerificationBundle -> Digest
sourceDigest = verificationBundleSourceRevision

roundText :: GrammarV1WholeSourceVerificationSpec -> IO Text
roundText spec = case wholeSourceSupplementalUnits spec of
  [("bounded-round",source)] -> pure source
  other -> ioError (userError ("unexpected supplemental inventory: " <> show other))

runMaterialized :: GrammarV1WholeSourceVerificationSpec -> Integer -> Integer -> Text -> IO ()
runMaterialized spec count request reply = do
  require (wholeSourcePrimaryText spec == F.source)
    "fixture coordinates are not the exact materialized primary source"
  fx <- must F.sourceFixture
  source <- roundText spec
  values <- must (F.roundValuesFromSource source)
  authority <- must F.stdoutAuthority
  let plan = F.fixturePlan fx
      input = GrammarV1RootCountValue (boundedPingRuntimeCountOccurrence plan)
        (ScalarUIntLiteral 32 count)
  (closed,evidence) <- must $ grammarV1RunBoundedPingFromSource
    (F.fixtureInstance fx) (F.fixtureNetwork fx) (F.fixtureCommunication fx)
    plan input values (PossessedCapability F.stdoutCapability) authority ConsoleWriteSucceeded
  let iterations = boundedPingEvidenceIterations evidence
      before = [count,count-1 .. 1]
  require (boundedPingEvidenceInitialCount evidence == count) "input count changed"
  require (map boundedPingIterationRemainingBefore iterations == before) "wrong before-count chain"
  require (map boundedPingIterationRemainingAfter iterations == map (subtract 1) before) "wrong returned successor chain"
  require (all ((== ScalarUIntLiteral 8 request) . boundedPingIterationRequestValue) iterations) "request not source-derived"
  require (all ((== reply) . boundedPingIterationReplyText) iterations) "reply not source-derived"
  must (F.assertBackedgeChain iterations)
  must (F.assertClosedAndTerminal fx closed evidence)

staleDigest :: FilePath -> FilePath -> IO ()
staleDigest root path = do
  original <- descriptor root
  let refs = wholeSourceDescriptorPrimary original : wholeSourceDescriptorSupplemental original
      selected = filter ((== path) . wholeSourceFilePath) refs
  ref <- case selected of
    [r] -> pure r
    _ -> ioError (userError "stale digest fixture did not select one source")
  alter root path (<> "\n")
  actual <- sha256File (root </> path) >>= must
  response <- materializePhase1WholeSourceVerificationDescriptor root original
  case response of
    Left (WholeSourceDescriptorDigestMismatch p expected got) ->
      require (p == path && expected == wholeSourceFileSha256 ref && got == actual && got /= expected)
        "wrong digest-rejection attribution"
    other -> ioError (userError ("stale bytes did not reject at digest gate: " <> show other))

main :: IO ()
main = do
  args <- getArgs
  (source,scratch) <- case args of
    [s,t] -> (,) <$> makeAbsolute s <*> makeAbsolute t
    _ -> ioError (userError "usage: Stage3PackageReview SUBJECT_ROOT SCRATCH_ROOT")
  results <- sequence
    [ test "P01" "shipped descriptor retains exact source roles and target keys" $ do
        d <- descriptor source
        require (wholeSourceFilePath (wholeSourceDescriptorPrimary d) == primaryPath) "primary changed"
        require (map wholeSourceFileLabel (wholeSourceDescriptorSupplemental d) == ["bounded-round"]
          && map wholeSourceFilePath (wholeSourceDescriptorSupplemental d) == [supplementPath]) "supplement roles changed"
        require (wholeSourceDescriptorArchitectureKey d == DeclarationKey "architecture.BoundedPing"
          && wholeSourceDescriptorArchitectureRevision d == DefinitionRevision "architecture.bounded-ping.v1"
          && wholeSourceDescriptorProgramKey d == DeclarationKey "program.main"
          && wholeSourceDescriptorPolicyRevision d == AssurancePolicyRevision "phase1.int007.ping.stage3.verification.v1") "target contract changed"
    , test "P02" "actual shipped accepting caller reconstructs exact empty-assurance summary" $ do
        (spec,expectedSource) <- materialize source
        require (wholeSourcePrimaryText spec == F.source) "primary fixture mismatch"
        supplement <- roundText spec
        require (supplement == F.roundSource) "supplement fixture mismatch"
        b <- must $ grammarV1WholeSourceVerificationBundle spec
        expected <- must $ decodePhase1VerificationBundleSummary expectedSource
        require (derivePhase1VerificationBundleSummary b == expected) "canonical summary mismatch"
        emptyAssurance b
        entry source "audit.canonical" >>= flip require "actual checkStage rejected canonical package"
    , test "P03" "duplicate primary record rejects in actual descriptor decoder" $ do
        text <- TIO.readFile (source </> descriptorPath)
        let rows = filter (Text.isPrefixOf "primary\t") (Text.lines text)
        row <- case rows of [r] -> pure r; _ -> ioError (userError "missing unique primary")
        case decodePhase1WholeSourceVerificationDescriptor (text <> row <> "\n") of
          Left WholeSourceDescriptorDuplicatePrimary -> pure ()
          other -> ioError (userError ("wrong duplicate-primary result: " <> show other))
    , test "P04" "duplicate source path rejects before materialization" $ do
        d <- descriptor source
        text <- TIO.readFile (source </> descriptorPath)
        let p = wholeSourceDescriptorPrimary d
            extra = Text.intercalate "\t" ["supplemental","extra",Text.pack primaryPath,wholeSourceFileSha256 p]
        case decodePhase1WholeSourceVerificationDescriptor (text <> extra <> "\n") of
          Left (WholeSourceDescriptorDuplicateSourcePath path) -> require (path == primaryPath) "wrong duplicate path"
          other -> ioError (userError ("wrong duplicate-path result: " <> show other))
    , test "P05" "stale primary hash rejects before source interpretation" $
        fresh source scratch "stale-primary" >>= flip staleDigest primaryPath
    , test "P06" "stale supplemental hash rejects before source interpretation" $
        fresh source scratch "stale-supplement" >>= flip staleDigest supplementPath
    , test "P07" "matching hash does not bypass supplemental syntax checking" $ do
        root <- fresh source scratch "malformed-supplement"
        TIO.writeFile (root </> supplementPath) "component {"
        refreshDigest root supplementPath
        (spec,_) <- materialize root
        case grammarV1WholeSourceVerificationBundle spec of
          Left (WholeSourceSupplementalParseError label _) -> require (label == "bounded-round") "wrong parse-error label"
          other -> ioError (userError ("matching hash bypassed parser: " <> show other))
    , test "P08" "program target must match the checked primary architecture" $ do
        root <- fresh source scratch "wrong-program-target"
        alter root primaryPath (Text.replace "instantiate BoundedPing" "instantiate OtherArchitecture")
        refreshDigest root primaryPath
        (spec,_) <- materialize root
        case grammarV1WholeSourceVerificationBundle spec of
          Left (WholeSourceProgramTargetMismatch expected actual) -> require (expected == "BoundedPing" && actual == "OtherArchitecture") "wrong target diagnostic"
          other -> ioError (userError ("wrong target did not reject: " <> show other))
    , test "P09" "valid changed source cannot reuse the old exact summary" $ do
        root <- fresh source scratch "changed-old-summary"
        alter root supplementPath changedLiterals
        refreshDigest root supplementPath
        old <- bundleAt source
        new <- bundleAt root
        require (sourceDigest old /= sourceDigest new) "source change lost revision identity"
        accepted <- entry root "audit.changed.old-summary"
        require (not accepted) "actual gate accepted obsolete exact summary"
    , test "P10" "consistently repackaged literals reach source-aware runtime values" $ do
        root <- fresh source scratch "changed-new-summary"
        alter root supplementPath changedLiterals
        refreshDigest root supplementPath
        regenerateReference root
        entry root "audit.changed.new-summary" >>= flip require "consistent package failed reconstruction"
        (spec,_) <- materialize root
        runMaterialized spec 1 43 "pong-2"
    , test "P11" "materialized shipped values preserve zero and positive count consumers" $ do
        (spec,_) <- materialize source
        forM_ [0,3] $ \count -> runMaterialized spec count 42 "pong"
    , test "P12" "positive-round semantic checker rejects addition in place of decrement" $ do
        root <- fresh source scratch "structural-not-runtime"
        alter root supplementPath (Text.replace "remaining - 1" "remaining + 1")
        refreshDigest root supplementPath
        (spec,_) <- materialize root
        sourceText <- roundText spec
        parsed <- must $ parseGrammarV1StructuralSource "audit.changed-round" sourceText
        (client,server) <- case grammarV1TopLevelDecls parsed of
          [Located _ c,Located _ s] -> (,) <$> must (F.declarationAsComponent "ClientRound" c) <*> must (F.declarationAsComponent "ServerRound" s)
          _ -> ioError (userError "changed supplemental did not parse as two components")
        case grammarV1CheckedBoundedPingSourceValues F.clientRoundKey client F.serverRoundKey server of
          Just (Left (GrammarV1BoundedPingSourceValuesClientShape detail)) -> require (detail == "expected remaining - 1") "wrong semantic rejection"
          other -> ioError (userError ("unsupported round not rejected by semantic checker: " <> show other))
        -- This observation is contract separation, not incorrect acceptance:
        -- the reconstruction gate never claims to run this numeric body.
        regenerateReference root
        b <- bundleAt root
        emptyAssurance b
        accepted <- entry root "audit.structural-only"
        require accepted "structural package contract changed; reassess observation"
        putStrLn "OBS O01 structural_reconstruction=True specialized_round_admission=False executable_numeric_credit=0"
    ]
  putStrLn "COMPLETE stage3_package_groups=12 observations=1"
  unless (and results) exitFailure
  where
    changedLiterals = Text.replace "send 42 on selected" "send 43 on selected"
      . Text.replace "send \"pong\" on replyEndpoint" "send \"pong-2\" on replyEndpoint"

test :: String -> String -> IO () -> IO Bool
test key label action = do
  outcome <- try action :: IO (Either IOException ())
  case outcome of
    Right () -> putStrLn ("AUDIT_PASS " <> key <> " " <> label) >> pure True
    Left problem -> putStrLn ("AUDIT_FAIL " <> key <> " " <> label <> " -- " <> show problem) >> pure False
