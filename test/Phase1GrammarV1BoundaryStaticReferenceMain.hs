{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 specialized static references survive boundary items"
        expectSpecializedBoundaryFixture
    , testIO "SURF-003 unclosed static argument still rejects"
        (expectFixtureReject "rejected/21-static-argument-unclosed.phil")
    , test "SURF-002 remaining boundary item forms preserve exact payloads"
        allBoundaryItemsPreserved
    , test "SURF-003 boundary item missing semicolon rejects"
        boundaryMissingSemicolonRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectSpecializedBoundaryFixture :: IO (Either String ())
expectSpecializedBoundaryFixture = do
  parsed <- parseFixture "accepted/26-specialized-static-reference.phil"
  pure $ do
    boundary <- singleBoundary =<< mapLeft show parsed
    assert (locatedValue (grammarV1BoundaryName boundary) == "Wire")
      "boundary name was not Wire"
    case grammarV1BoundaryGenericParams boundary of
      [Located _ param] -> do
        assert (locatedValue (grammarV1GenericParamName param) == "T")
          "generic parameter name was not T"
        assert (locatedValue (grammarV1GenericParamKind param) == GrammarV1TypeKind)
          "generic parameter kind was not Type"
      params -> Left ("expected one generic parameter, got " <> show params)
    assertNamedType "T" (grammarV1BoundaryType boundary)
    case grammarV1BoundaryItems boundary of
      [ Located _ (GrammarV1BoundaryReceive decoder)
        , Located _ (GrammarV1BoundarySend encoder)
        , Located _ (GrammarV1BoundaryCorrespondence proposition)
        ] -> do
          assertSpecializedReference "Decoder" "T" decoder
          assertSpecializedReference "Encoder" "T" encoder
          assertSpecializedClaim "Good" "T" proposition
      items -> Left ("unexpected boundary items " <> show items)

allBoundaryItemsPreserved :: Either String ()
allBoundaryItemsPreserved = do
  boundary <- singleBoundary =<< mapLeft show
    (parseGrammarV1StructuralSource "boundary-items" source)
  case grammarV1BoundaryItems boundary of
    [ Located _ GrammarV1BoundaryCanonical
      , Located _ (GrammarV1BoundaryFailure failureType)
      , Located _ (GrammarV1BoundaryLaw lawName proposition)
      ] -> do
        assert (locatedValue failureType == GrammarV1UnsignedType "U8")
          "failure type was not U8"
        assert (locatedValue lawName == "Identity") "law name was not Identity"
        assert (locatedValue proposition == GrammarV1TrueProposition)
          "law proposition was not true"
    items -> Left ("unexpected boundary item forms " <> show items)
  where
    source = Text.unlines
      [ "boundary B : U8 {"
      , "  canonical;"
      , "  failure U8;"
      , "  law Identity : true;"
      , "}"
      ]

boundaryMissingSemicolonRejects :: Either String ()
boundaryMissingSemicolonRejects =
  expectReject "boundary B : U8 { receive using Decoder[U8] }"

singleBoundary :: GrammarV1SourceFile -> Either String GrammarV1BoundaryDecl
singleBoundary sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [_, Located _ topLevel] -> extractBoundary topLevel
    [Located _ topLevel] -> extractBoundary topLevel
    declarations -> Left ("expected boundary declaration, got " <> show (length declarations) <> " top-level declarations")
  where
    extractBoundary topLevel = case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1BoundaryDeclaration boundary -> Right boundary
      other -> Left ("expected boundary declaration, got " <> show other)

assertNamedType :: Text.Text -> Located GrammarV1Type -> Either String ()
assertNamedType expected (Located _ ty) = case ty of
  GrammarV1NamedType reference ->
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
  other -> Left ("expected named type, got " <> show other)

assertSpecializedReference
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1StaticReference
  -> Either String ()
assertSpecializedReference expectedName expectedArgument (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName])
    ("unexpected static reference name " <> show (grammarV1StaticReferenceName reference))
  case grammarV1StaticReferenceArguments reference of
    [GrammarV1StaticReferenceArgument argument] ->
      assert
        (grammarV1QualifiedNameParts (grammarV1StaticReferenceName argument) == [expectedArgument])
        ("unexpected static reference argument " <> show argument)
    arguments -> Left ("expected one static reference argument, got " <> show arguments)

assertSpecializedClaim
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1Proposition
  -> Either String ()
assertSpecializedClaim expectedName expectedStaticArgument (Located _ proposition) =
  case proposition of
    GrammarV1ClaimApplicationProposition reference [Located _ (GrammarV1IntegerExpression "1")] -> do
      assert
        (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName])
        "claim application name was not Good"
      case grammarV1StaticReferenceArguments reference of
        [GrammarV1StaticReferenceArgument argument] ->
          assert
            (grammarV1QualifiedNameParts (grammarV1StaticReferenceName argument) == [expectedStaticArgument])
            "claim static argument was not T"
        arguments -> Left ("unexpected claim static arguments " <> show arguments)
    other -> Left ("expected specialized claim application, got " <> show other)

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "boundary-negative" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
