{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Authority
  ( AuthorityContractKey (..)
  , AuthorityOperationKey (..)
  )
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Proposition (..)
  )
import Phil.Surface.GrammarV1.CapabilityContract
  ( GrammarV1CheckedCapabilityContract (..)
  , grammarV1CheckedClosedCapabilityContract
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1StructuralMode)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-008 record linear mode routes exactly"
        (expectFixtureMode "accepted/11-record-explicit-linear-mode.phil" (Just Linear))
    , testIO "SURF-008 data affine mode routes exactly"
        (expectFixtureMode "accepted/12-sum-explicit-affine-mode.phil" (Just Affine))
    , testIO "SURF-008 capability unrestricted mode routes exactly"
        (expectFixtureMode "accepted/13-capability-unrestricted-mode.phil" (Just Unrestricted))
    , test "SURF-008 omitted record mode remains omitted before semantic derivation"
        omittedRecordModeRemainsAbsent
    , test "SURF-008 closed capability contracts preserve stable identity, mode, operations, requirements, and laws"
        closedCapabilityContract
    , test "SURF-008 capability proposition Core failures remain distinct from source non-competence"
        capabilityContractCoreFailure
    , test "SURF-008 generic, specialized, and unresolved capability forms remain fail-closed"
        capabilityContractCompetenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectFixtureMode :: FilePath -> Maybe Mode -> IO (Either String ())
expectFixtureMode relativePath expected = do
  source <- TextIO.readFile ("test/fixtures/phase1-surface/" <> relativePath)
  pure $ do
    parsed <- mapLeft show $ parseGrammarV1StructuralSource (Text.pack relativePath) source
    actual <- exactlyOneMode parsed
    assert (actual == expected)
      ("expected semantic mode " <> show expected <> ", got " <> show actual)

omittedRecordModeRemainsAbsent :: Either String ()
omittedRecordModeRemainsAbsent = do
  parsed <- mapLeft show $ parseGrammarV1StructuralSource "omitted-mode"
    "record Plain { value : U32 }"
  actual <- exactlyOneMode parsed
  assert (actual == Nothing)
    ("omitted record mode was defaulted during source elaboration: " <> show actual)

closedCapabilityContract :: Either String ()
closedCapabilityContract = do
  source <- onlyCapability $ Text.unlines
    [ "capability Access mode affine {"
    , "  permits storage.Read;"
    , "  requires true;"
    , "  permits Audit;"
    , "  law Safe : false;"
    , "}"
    ]
  renamed <- onlyCapability $ Text.unlines
    [ "capability RenamedPresentation mode affine {"
    , "  permits storage.Read;"
    , "  requires true;"
    , "  permits Audit;"
    , "  law Safe : false;"
    , "}"
    ]
  let contractKey = AuthorityContractKey "capability.stable.access"
      expected = GrammarV1CheckedCapabilityContract
        { checkedCapabilityContractKey = contractKey
        , checkedCapabilityContractMode = Affine
        , checkedCapabilityContractOperations =
            [ AuthorityOperationKey "storage.Read"
            , AuthorityOperationKey "Audit"
            ]
        , checkedCapabilityContractRequirements = [(Truth, [])]
        , checkedCapabilityContractLaws = [("Safe", Falsehood, [])]
        }
  assert
    ( grammarV1CheckedClosedCapabilityContract
        emptyStaticContext contractKey source
        == Just (Right expected)
    )
    "closed capability contract did not preserve exact semantic categories"
  assert
    ( grammarV1CheckedClosedCapabilityContract
        emptyStaticContext contractKey renamed
        == Just (Right expected)
    )
    "capability source display-name change leaked into stable contract identity"

capabilityContractCoreFailure :: Either String ()
capabilityContractCoreFailure = do
  source <- onlyCapability $ Text.unlines
    [ "capability BadClaim mode unrestricted {"
    , "  permits Audit;"
    , "  requires Missing();"
    , "}"
    ]
  let contractKey = AuthorityContractKey "capability.stable.bad-claim"
  assert
    ( grammarV1CheckedClosedCapabilityContract
        emptyStaticContext contractKey source
        == Just (Left (UnknownClaim "Missing"))
    )
    "capability proposition Core UnknownClaim collapsed into source non-competence"

capabilityContractCompetenceBoundaries :: Either String ()
capabilityContractCompetenceBoundaries = do
  specialized <- onlyCapability $ Text.unlines
    [ "capability Specialized mode unrestricted {"
    , "  permits storage.Read[U8];"
    , "}"
    ]
  generic <- onlyCapability $ Text.unlines
    [ "capability Generic[T : Type] mode unrestricted {"
    , "  permits Audit;"
    , "}"
    ]
  unresolved <- onlyCapability $ Text.unlines
    [ "capability Unresolved mode unrestricted {"
    , "  permits Audit;"
    , "  requires n == 0;"
    , "}"
    ]
  let contractKey = AuthorityContractKey "capability.stable.boundary"
  assert
    ( grammarV1CheckedClosedCapabilityContract
        emptyStaticContext contractKey specialized
        == Nothing
    )
    "specialized capability operation reference was flattened into a bare authority key"
  assert
    ( grammarV1CheckedClosedCapabilityContract
        emptyStaticContext contractKey generic
        == Nothing
    )
    "generic capability escaped the closed capability-contract competence wall"
  assert
    ( grammarV1CheckedClosedCapabilityContract
        emptyStaticContext contractKey unresolved
        == Nothing
    )
    "unresolved free capability proposition acquired an invented top-level binding"

onlyCapability :: Text.Text -> Either String GrammarV1CapabilityDecl
onlyCapability source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-capability-contract" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CapabilityDeclaration capability -> Right capability
      other -> Left ("expected capability declaration, got " <> show other)
    declarations -> Left
      ("expected one capability declaration, got " <> show (length declarations))

exactlyOneMode :: GrammarV1SourceFile -> Either String (Maybe Mode)
exactlyOneMode sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1RecordDeclaration declaration ->
          Right (grammarV1StructuralMode <$> grammarV1RecordMode declaration)
        GrammarV1DataDeclaration declaration ->
          Right (grammarV1StructuralMode <$> grammarV1DataMode declaration)
        GrammarV1CapabilityDeclaration declaration ->
          Right (Just (grammarV1StructuralMode (grammarV1CapabilityMode declaration)))
        other -> Left ("expected mode-bearing declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
