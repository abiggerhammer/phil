{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Exception (IOException, try)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.NominalDataMode (NominalModeError (..))
import Phil.Core.Static (DeclarationKey (..), DefinitionRevision (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), RefTerm (..), Ty (..))
import qualified Phil.Surface.Parser as Legacy
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..), GrammarV1RecordDecl, GrammarV1DataDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.RecordFields
  ( GrammarV1CheckedRecordMode (..), GrammarV1CheckedRecordModeError (..)
  , grammarV1CheckedClosedRecordMode, grammarV1RecordModeFromCheckedFields )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..), GrammarV1CheckedDataModeError (..)
  , GrammarV1CheckedVariantMode (..), GrammarV1CheckedVariantModePayload (..)
  , grammarV1CheckedClosedDataMode )
import Phil.Surface.Syntax (Located (..))
import Phil.Verification (AssurancePolicyRevision (..), VerificationObligationGraph (..))
import Phil.Verification.Bundle (VerificationBundle (..))
import Phil.Verification.GrammarV1WholeSource
  ( GrammarV1WholeSourceVerificationSpec (..), GrammarV1WholeSourceVerificationError (..)
  , grammarV1WholeSourceVerificationBundle )
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)

data AuditFailure = HarnessFailure String | PropertyFailure String deriving Show
type Fixtures = Map.Map String Text
type Case = (String, Fixtures -> Either AuditFailure ())

fixtureNames :: [String]
fixtureNames =
  [ "record-valid.phil", "record-weak.phil", "record-unknown-proof.phil"
  , "record-tuple.phil", "record-generic.phil", "record-required.phil"
  , "record-renamed.phil", "record-duplicate.phil", "data-valid.phil"
  , "data-weak.phil", "data-nested.phil", "roots.phil"
  , "supplemental-invalid-syntax.phil" ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--fixtures", directory] -> run directory False
    ["--fixtures", directory, "--observe"] -> run directory True
    _ -> putStrLn "usage: schema-audit --fixtures DIRECTORY [--observe]" >> exitWith (ExitFailure 2)

run :: FilePath -> Bool -> IO ()
run directory withObservations = do
  loaded <- try (mapM (\name -> do
    text <- TextIO.readFile (directory <> "/" <> name)
    pure (name, text)) fixtureNames) :: IO (Either IOException [(String, Text)])
  case loaded of
    Left err -> putStrLn ("HARNESS\tfixture-read\t" <> show err) >> exitWith (ExitFailure 2)
    Right pairs -> do
      let fixtures = Map.fromList pairs
          observationsToRun = if withObservations then observations else []
      checkCodes <- mapM (emit "CHECK" "PASS" "FAIL" fixtures) checks
      observationCodes <- mapM (emit "OBSERVE" "MATCH" "DRIFT" fixtures) observationsToRun
      putStrLn ("SUMMARY\tchecks=" <> show (length checks)
        <> "\tobservations=" <> show (length observationsToRun))
      let codes = checkCodes <> observationCodes
          status | 2 `elem` codes = 2
                 | 1 `elem` checkCodes = 1
                 | 1 `elem` observationCodes = 3
                 | otherwise = 0
      exitWith (if status == 0 then ExitSuccess else ExitFailure status)

emit :: String -> String -> String -> Fixtures -> Case -> IO Int
emit category good bad fixtures (identifier, action) = case action fixtures of
  Right () -> putStrLn (category <> "\t" <> identifier <> "\t" <> good) >> pure 0
  Left (HarnessFailure detail) -> putStrLn
    (category <> "\t" <> identifier <> "\tHARNESS\t" <> show detail) >> pure 2
  Left (PropertyFailure detail) -> putStrLn
    (category <> "\t" <> identifier <> "\t" <> bad <> "\t" <> show detail) >> pure 1

source :: Fixtures -> String -> Either AuditFailure Text
source fixtures name = maybe (Left (HarnessFailure ("missing fixture " <> name))) Right (Map.lookup name fixtures)

oneDeclaration :: Text -> Either AuditFailure GrammarV1Declaration
oneDeclaration text = do
  parsed <- either (Left . HarnessFailure . show) Right
    (parseGrammarV1StructuralSource "schema-audit" text)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> Right (locatedValue (grammarV1Declaration top))
    _ -> Left (HarnessFailure "fixture did not contain exactly one declaration")

recordFrom :: Fixtures -> String -> Either AuditFailure GrammarV1RecordDecl
recordFrom fixtures name = do
  declaration <- source fixtures name >>= oneDeclaration
  case declaration of
    GrammarV1RecordDeclaration value -> Right value
    _ -> Left (HarnessFailure "expected record declaration")

dataFrom :: Fixtures -> String -> Either AuditFailure GrammarV1DataDecl
dataFrom fixtures name = do
  declaration <- source fixtures name >>= oneDeclaration
  case declaration of
    GrammarV1DataDeclaration value -> Right value
    _ -> Left (HarnessFailure "expected data declaration")

require :: Bool -> String -> Either AuditFailure ()
require True _ = Right ()
require False detail = Left (PropertyFailure detail)

recordCheck :: GrammarV1RecordDecl -> Maybe (Either GrammarV1CheckedRecordModeError GrammarV1CheckedRecordMode)
recordCheck = grammarV1CheckedClosedRecordMode emptyStaticContext Nothing

dataCheck :: GrammarV1DataDecl -> Maybe (Either GrammarV1CheckedDataModeError GrammarV1CheckedDataMode)
dataCheck = grammarV1CheckedClosedDataMode emptyStaticContext Nothing

spec :: Text -> [(Text, Text)] -> GrammarV1WholeSourceVerificationSpec
spec primary supplemental = GrammarV1WholeSourceVerificationSpec
  { wholeSourcePrimaryLabel = "schema-audit-primary"
  , wholeSourcePrimaryText = primary
  , wholeSourceSupplementalUnits = supplemental
  , wholeSourceArchitectureKey = DeclarationKey "audit.root"
  , wholeSourceArchitectureRevision = DefinitionRevision "audit.root.definition"
  , wholeSourceProgramKey = DeclarationKey "audit.program"
  , wholeSourcePolicyRevision = AssurancePolicyRevision "audit.policy"
  }

emptyGraphResult :: Either GrammarV1WholeSourceVerificationError VerificationBundle -> Either AuditFailure ()
emptyGraphResult result = case result of
  Left err -> Left (PropertyFailure ("bundle rejected: " <> show err))
  Right bundle -> do
    let graph = verificationBundleObligationGraph bundle
    require (Map.null (verificationGraphNodes graph)
      && Set.null (verificationGraphDependencies graph)
      && Set.null (verificationGraphCertificationScope graph)
      && Map.null (verificationBundleAcceptedEvidence bundle))
      "expected scoped identity bundle with empty graph/evidence; not a declaration-validity result"

checks :: [Case]
checks =
  [ ("C01-record-exact-types-modes", \f -> do
      r <- recordFrom f "record-valid.phil"
      require (recordCheck r == Just (Right (GrammarV1CheckedRecordMode
        [("flag", CheckedTypeMode TyBool Unrestricted, [])
        ,("payload", CheckedTypeMode (TyBytes (RefNat 7)) Linear, [])] Linear)))
        "record result changed exact field types/modes/order")
  , ("C02-record-weakening", \f -> do
      r <- recordFrom f "record-weak.phil"
      require (recordCheck r == Just (Left (GrammarV1RecordModeNominalError
        (DeclaredModeWeakensDerived Linear Unrestricted)))) "wrong weakening disposition")
  , ("C03-record-unknown-claim", \f -> do
      r <- recordFrom f "record-unknown-proof.phil"
      require (recordCheck r == Just (Left (GrammarV1RecordModeFocusingError
        (UnknownClaim "Missing")))) "wrong focusing disposition")
  , ("C04-record-tuple-noncompetence", \f -> do
      r <- recordFrom f "record-tuple.phil"
      require (recordCheck r == Nothing) "unsupported nested type acquired a mode")
  , ("C05-record-generic-noncompetence", \f -> do
      r <- recordFrom f "record-generic.phil"
      require (recordCheck r == Nothing) "generic entered closed checker")
  , ("C06-record-requirement-noncompetence", \f -> do
      r <- recordFrom f "record-required.phil"
      require (recordCheck r == Nothing) "requirement-bearing record entered closed checker")
  , ("C07-data-payload-shapes", \f -> do
      d <- dataFrom f "data-valid.phil"
      require (dataCheck d == Just (Right (GrammarV1CheckedDataMode
        [GrammarV1CheckedVariantMode "None" Nothing
        ,GrammarV1CheckedVariantMode "EmptyTuple" (Just (GrammarV1CheckedVariantModeTuple []))
        ,GrammarV1CheckedVariantMode "EmptyRecord" (Just (GrammarV1CheckedVariantModeRecord []))
        ,GrammarV1CheckedVariantMode "Payload" (Just (GrammarV1CheckedVariantModeTuple
          [(CheckedTypeMode (TyBytes (RefNat 7)) Linear, [])]))] Linear)))
        "nullary, empty tuple/record, or owned payload changed")
  , ("C08-data-weakening", \f -> do
      d <- dataFrom f "data-weak.phil"
      require (dataCheck d == Just (Left (GrammarV1DataModeNominalError
        (DeclaredModeWeakensDerived Linear Unrestricted)))) "wrong data weakening disposition")
  , ("C09-data-nested-noncompetence", \f -> do
      d <- dataFrom f "data-nested.phil"
      require (dataCheck d == Nothing) "nested tuple entered closed data checker")
  , ("C10-record-mode-order", \f -> do
      r <- recordFrom f "record-valid.phil"
      require (grammarV1RecordModeFromCheckedFields
        [("payload", Linear), ("flag", Unrestricted)] Nothing r == Nothing)
        "reordered external field-mode view accepted")
  , ("C11-whole-source-invalid-supplemental-syntax", \f -> do
      roots <- source f "roots.phil"
      invalid <- source f "supplemental-invalid-syntax.phil"
      case grammarV1WholeSourceVerificationBundle (spec roots [("bad", invalid)]) of
        Left (WholeSourceSupplementalParseError "bad" _) -> Right ()
        other -> Left (PropertyFailure ("wrong syntax-gate result: " <> show other)))
  , ("C12-legacy-parser-excludes-record-declarations", \f -> do
      text <- source f "record-valid.phil"
      case Legacy.parseSurfaceFile "audit-legacy-boundary" text of
        Left _ -> Right ()
        Right _ -> Left (PropertyFailure "legacy component parser admitted a record declaration"))
  ]

-- These are predicted boundary observations, NOT desired safety regressions.
-- A MATCH is never counted as a correctness PASS. A repaired/extended route may drift.
observations :: [Case]
observations =
  [ ("O01-record-view-not-declaration-identity", \f -> do
      a <- recordFrom f "record-valid.phil"
      b <- recordFrom f "record-renamed.phil"
      case (recordCheck a, recordCheck b) of
        (Just (Right left), Just (Right right)) -> require (left == right)
          "named declarations have different projected views"
        other -> Left (PropertyFailure ("name-only projection pair did not both accept: " <> show other)))
  , ("O02-duplicate-field-view-preserved", \f -> do
      r <- recordFrom f "record-duplicate.phil"
      case recordCheck r of
        Just (Right checked) -> require
          (map (\(n, _, _) -> n) (checkedRecordModeFields checked) == ["item", "item"]
            && checkedRecordStructuralMode checked == Linear)
          "duplicate spelling or exact aggregate mode changed"
        other -> Left (PropertyFailure ("duplicate projection changed: " <> show other)))
  , ("O03-rejected-record-in-primary-bundle", \f -> do
      r <- recordFrom f "record-weak.phil"
      require (recordCheck r == Just (Left (GrammarV1RecordModeNominalError
        (DeclaredModeWeakensDerived Linear Unrestricted)))) "direct checker did not reject"
      roots <- source f "roots.phil"
      bad <- source f "record-weak.phil"
      emptyGraphResult (grammarV1WholeSourceVerificationBundle (spec (roots <> bad) [])))
  , ("O04-rejected-record-in-supplemental-bundle", \f -> do
      roots <- source f "roots.phil"
      bad <- source f "record-weak.phil"
      emptyGraphResult (grammarV1WholeSourceVerificationBundle (spec roots [("record-unit", bad)])))
  , ("O05-noncompetent-record-in-primary-bundle", \f -> do
      r <- recordFrom f "record-tuple.phil"
      require (recordCheck r == Nothing) "direct checker unexpectedly competent"
      roots <- source f "roots.phil"
      unsupported <- source f "record-tuple.phil"
      emptyGraphResult (grammarV1WholeSourceVerificationBundle (spec (roots <> unsupported) [])))
  , ("O06-rejected-data-in-primary-bundle", \f -> do
      d <- dataFrom f "data-weak.phil"
      require (dataCheck d == Just (Left (GrammarV1DataModeNominalError
        (DeclaredModeWeakensDerived Linear Unrestricted)))) "direct data checker did not reject"
      roots <- source f "roots.phil"
      bad <- source f "data-weak.phil"
      emptyGraphResult (grammarV1WholeSourceVerificationBundle (spec (roots <> bad) [])))
  ]
