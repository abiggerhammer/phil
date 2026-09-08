{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, unless, when)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment
  , checkSurfaceComponent
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0
  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0ExpectationFor
  )
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)
import System.Timeout (timeout)

data NegativeCase = NegativeCase
  { negativeCaseId :: Text
  , negativeCasePath :: FilePath
  , negativeCaseExpectedClass :: RejectionClass
  , negativeCaseLayer :: Text
  , negativeCaseEnvironmentProfile :: Text
  , negativeCaseAuthority :: Text
  }
  deriving (Eq, Show)

manifestPath :: FilePath
manifestPath = "test/fixtures/phase1-negative/manifest.tsv"

main :: IO ()
main = do
  manifest <- TextIO.readFile manifestPath
  cases <- case parseManifest manifest of
    Left detail -> putStrLn ("FAIL: manifest -- " <> detail) >> exitFailure
    Right value -> pure value
  integrityOk <- checkIntegrity cases
  results <- forM cases replayCase
  unless (integrityOk && and results) exitFailure
  putStrLn ("PASS: INT-004 portable frozen negative manifest (" <> show (length cases) <> " fixtures)")

parseManifest :: Text -> Either String [NegativeCase]
parseManifest input = case Text.lines input of
  [] -> Left "empty manifest"
  header : rows
    | header /= expectedHeader -> Left ("unexpected header: " <> Text.unpack header)
    | otherwise -> traverse parseRow (filter (not . Text.null) rows)
  where
    expectedHeader = Text.intercalate "\t"
      [ "fixture_id"
      , "path"
      , "expect"
      , "competent_layer"
      , "environment_profile"
      , "governing_authority"
      ]

parseRow :: Text -> Either String NegativeCase
parseRow row = case Text.splitOn "\t" row of
  [fixtureId, path, expected, layer, environmentProfile, authority] -> do
    rejectionClass <- parseRejectionClass expected
    if any Text.null [fixtureId, path, layer, environmentProfile, authority]
      then Left ("empty required field: " <> Text.unpack row)
      else Right NegativeCase
        { negativeCaseId = fixtureId
        , negativeCasePath = Text.unpack path
        , negativeCaseExpectedClass = rejectionClass
        , negativeCaseLayer = layer
        , negativeCaseEnvironmentProfile = environmentProfile
        , negativeCaseAuthority = authority
        }
  _ -> Left ("invalid TSV row: " <> Text.unpack row)

parseRejectionClass :: Text -> Either String RejectionClass
parseRejectionClass value = case value of
  "structural-use" -> Right StructuralUse
  "linear-completion" -> Right LinearCompletion
  "session-action" -> Right SessionAction
  "branch-exhaustiveness" -> Right BranchExhaustiveness
  "illegal-projection" -> Right IllegalProjection
  "missing-evidence" -> Right MissingEvidence
  "explicit-transport" -> Right ExplicitTransport
  "incompatible-branch-residue" -> Right IncompatibleBranchResidue
  "control-after-terminal" -> Right ControlAfterTerminal
  "recognition-provenance" -> Right RecognitionProvenance
  "borrow-escape" -> Right BorrowEscape
  "opaque-proof" -> Right OpaqueProof
  "unchecked-arithmetic" -> Right UncheckedArithmetic
  _ -> Left ("unknown portable rejection class: " <> Text.unpack value)

-- Transitional INT-004 compatibility boundary. The portable manifest selects
-- a stable environment profile; this adapter alone maps that profile onto the
-- frozen Phase-0 environment table. The fixture path never selects the checker
-- environment. A later INT-004 slice will replace this adapter with genuinely
-- portable environment material.
phase0ProfileEnvironment :: Text -> Either Text SurfaceEnvironment
phase0ProfileEnvironment profile =
  case profile of
    "phase0.simple-receive" -> legacy "01-reuse-consumed-endpoint.phil"
    "phase0.wrong-order" -> legacy "03-wrong-protocol-order.phil"
    "phase0.nonexhaustive-offer" -> legacy "04-nonexhaustive-offer.phil"
    "phase0.legacy-raw" -> legacy "05-raw-field-access.phil"
    "phase0.parsed-validation-bypass" -> legacy "06-parsed-used-as-validated.phil"
    "phase0.unrelated-length" -> legacy "07-unrelated-payload-length.phil"
    "phase0.incompatible-join" -> legacy "08-incompatible-branch-join.phil"
    "phase0.failure-reuse" -> legacy "09-continue-after-fatal-recognition-failure.phil"
    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"
    "phase0.common" -> legacy "11-copy-authority-capability.phil"
    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"
    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"
    "phase0.stale-policy" -> legacy "17-use-evidence-wrong-context.phil"
    "phase0.opaque-proof" -> legacy "18-prove-opaque-digest.phil"
    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"
    _ -> Left ("unknown Phase-0 environment profile: " <> profile)
  where
    legacy name = phase0EnvironmentFor ("examples/rejected/" <> Text.unpack name)

checkIntegrity :: [NegativeCase] -> IO Bool
checkIntegrity cases = do
  let ids = map negativeCaseId cases
      paths = map negativeCasePath cases
      uniqueIds = Set.size (Set.fromList ids) == length ids
      uniquePaths = Set.size (Set.fromList paths) == length paths
      exactFrozenCount = length cases == 20
      layersExact = all ((== "surface-check") . negativeCaseLayer) cases
      authoritiesPresent = all ((== "INT-004") . negativeCaseAuthority) cases
      profilesNamed = all (Text.isPrefixOf "phase0." . negativeCaseEnvironmentProfile) cases
      profilesResolve = all
        (either (const False) (const True) . phase0ProfileEnvironment . negativeCaseEnvironmentProfile)
        cases
  filesPresent <- and <$> mapM doesFileExist paths
  report "20 frozen negative fixtures are manifest-owned" exactFrozenCount
  report "stable fixture IDs are unique" uniqueIds
  report "portable fixture paths are unique" uniquePaths
  report "every fixture names surface-check as competent layer" layersExact
  report "every fixture names its governing INT-004 matrix authority" authoritiesPresent
  report "every fixture names an explicit environment profile" profilesNamed
  report "every named environment profile resolves independently of fixture path" profilesResolve
  report "every portable fixture path exists" filesPresent
  pure (and
    [ exactFrozenCount
    , uniqueIds
    , uniquePaths
    , layersExact
    , authoritiesPresent
    , profilesNamed
    , profilesResolve
    , filesPresent
    ])

replayCase :: NegativeCase -> IO Bool
replayCase negativeCase = do
  source <- TextIO.readFile (negativeCasePath negativeCase)
  let path = negativeCasePath negativeCase
      expected = negativeCaseExpectedClass negativeCase
  parityOk <- case phase0ExpectationFor path of
    Just (FixtureReject legacyClass) -> do
      let ok = legacyClass == expected
      when (not ok) $ putStrLn
        ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
          <> " -- portable manifest disagrees with frozen legacy classification")
      pure ok
    _ -> putStrLn
      ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
        <> " -- frozen legacy fixture missing during migration") >> pure False
  case phase0ProfileEnvironment (negativeCaseEnvironmentProfile negativeCase) of
    Left detail -> failCase ("environment profile failed: " <> Text.unpack detail)
    Right environment -> case parseSurfaceFile (Text.pack path) source of
      Left diagnostic -> failCase
        ("rejected before recorded competent layer: syntax -- " <> show diagnostic)
      Right (SurfaceFile [component]) -> do
        checked <- timeout 2000000 $ evaluate (checkSurfaceComponent environment component)
        case checked of
          Nothing -> failCase "checker did not terminate"
          Just (Right _) -> failCase
            ("expected portable rejection class " <> show expected <> ", checker accepted")
          Just (Left errorValue)
            | surfaceErrorClass errorValue == expected -> do
                putStrLn ("PASS: " <> Text.unpack (negativeCaseId negativeCase)
                  <> " " <> path <> " @ surface-check")
                pure parityOk
            | otherwise -> failCase
                ("expected " <> show expected <> ", got "
                  <> show (surfaceErrorClass errorValue) <> ": "
                  <> Text.unpack (surfaceErrorDetail errorValue))
      Right (SurfaceFile components) -> failCase
        ("unexpected component count before competent layer: " <> show (length components))
  where
    failCase detail = putStrLn
      ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
        <> " " <> negativeCasePath negativeCase <> " -- " <> detail) >> pure False

report :: String -> Bool -> IO ()
report label ok = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
