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
    [ testIO "SURF-002 outcome residues preserve kinds state and callee"
        expectOutcomeResidues
    , testIO "SURF-002 exact replace callee preserves replacement and state"
        expectExactReplaceCallee
    , testIO "SURF-002 outcome refinement preserves refined state slot"
        expectOutcomeRefinement
    , testIO "SURF-002 outcome kinds and obligations preserve all four kinds"
        expectOutcomeKindsAndObligations
    , testIO "SURF-003 outcome state missing semicolon rejects at syntax"
        (expectFixtureReject "rejected/06-outcome-state-missing-semicolon.phil")
    , testIO "SURF-003 replace callee missing with rejects at syntax"
        (expectFixtureReject "rejected/07-replace-callee-missing-with.phil")
    , testIO "SURF-003 outcome missing block rejects at syntax"
        (expectFixtureReject "rejected/09-outcome-missing-block.phil")
    , testIO "SURF-003 unclassified outcome set rejects at syntax"
        (expectFixtureReject "rejected/14-outcome-unclassified.phil")
    , testIO "SURF-003 outcome residue missing kind rejects at syntax"
        (expectFixtureReject "rejected/15-outcome-residue-missing-kind.phil")
    , test "SURF-002 named call followed by relation stays a relation"
        callRelationDisambiguation
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectOutcomeResidues :: IO (Either String ())
expectOutcomeResidues = do
  parsed <- parseFixture "accepted/06-outcome-residues.phil"
  pure $ do
    callable <- onlyCallable parsed
    case grammarV1CallableClauses callable of
      [ Located _ (GrammarV1CallableOutcomes specs)
        , Located _ (GrammarV1CallableOutcomeResidue successResidue)
        , Located _ (GrammarV1CallableOutcomeResidue negativeResidue)
        , Located _ (GrammarV1CallableCallee topCallee)
        ] -> do
          assertOutcomeKinds [GrammarV1SuccessOutcome, GrammarV1NegativeOutcome] specs
          assert (locatedValue (grammarV1OutcomeResidueKind (locatedValue successResidue)) == GrammarV1SuccessOutcome)
            "success residue kind was not preserved"
          assertNamedType "ReadOk" (locatedValue (grammarV1OutcomeResidueType (locatedValue successResidue)))
          case grammarV1OutcomeResidueClauses (locatedValue successResidue) of
            [Located _ (GrammarV1OutcomeState [Located _ slot]), Located _ (GrammarV1OutcomeEnsures proposition)] -> do
              assert (locatedValue (grammarV1StateSlotName slot) == "blob_next")
                "success state slot name was not blob_next"
              assertNamedType "Blob" (locatedValue (grammarV1StateSlotType slot))
              assertTrue proposition
            other -> Left ("unexpected success residue clauses " <> show other)
          assert (locatedValue (grammarV1OutcomeResidueKind (locatedValue negativeResidue)) == GrammarV1NegativeOutcome)
            "negative residue kind was not preserved"
          case grammarV1OutcomeResidueClauses (locatedValue negativeResidue) of
            [Located _ (GrammarV1OutcomeState []), Located _ (GrammarV1OutcomeEnsures proposition)] ->
              assertTrue proposition
            other -> Left ("unexpected negative residue clauses " <> show other)
          assertCalleePreserve topCallee
      clauses -> Left ("unexpected outcome-residue callable clauses " <> show clauses)

expectExactReplaceCallee :: IO (Either String ())
expectExactReplaceCallee = do
  parsed <- parseFixture "accepted/07-exact-replace-callee.phil"
  pure $ do
    callable <- onlyCallable parsed
    case grammarV1CallableClauses callable of
      [Located _ (GrammarV1CallableCallee transition)] ->
        case locatedValue transition of
          GrammarV1CalleeReplace replacement (Just successorState) -> do
            assertStaticReferenceName "NextCallable" replacement
            assertSimpleName "next_state" successorState
          other -> Left ("expected replace-with-state callee transition, got " <> show other)
      clauses -> Left ("expected one callee clause, got " <> show clauses)

expectOutcomeRefinement :: IO (Either String ())
expectOutcomeRefinement = do
  parsed <- parseFixture "accepted/10-outcome-refinement-composition.phil"
  pure $ do
    callable <- onlyCallable parsed
    case [residue | Located _ (GrammarV1CallableOutcomeResidue residue) <- grammarV1CallableClauses callable] of
      successResidue : _ ->
        case grammarV1OutcomeResidueClauses (locatedValue successResidue) of
          Located _ (GrammarV1OutcomeState [Located _ slot]) : _ ->
            case locatedValue (grammarV1StateSlotType slot) of
              GrammarV1RefinementType binder baseType predicate -> do
                assert (locatedValue binder == "b") "outcome refinement binder was not b"
                case locatedValue baseType of
                  GrammarV1BytesType lengthExpression -> assertSimpleName "n" lengthExpression
                  other -> Left ("expected Bytes refinement base, got " <> show other)
                assertNameIntegerRelation GrammarV1GreaterRelation "n" "0" predicate
              other -> Left ("expected refined state slot, got " <> show other)
          other -> Left ("expected first residue state clause, got " <> show other)
      [] -> Left "expected at least one outcome residue"

expectOutcomeKindsAndObligations :: IO (Either String ())
expectOutcomeKindsAndObligations = do
  parsed <- parseFixture "accepted/21-outcome-kinds-obligations.phil"
  pure $ do
    callable <- onlyCallable parsed
    case grammarV1CallableClauses callable of
      Located _ (GrammarV1CallableOutcomes specs)
        : Located _ (GrammarV1CallableObligation obligation)
        : residueClauses -> do
          assertOutcomeKinds
            [ GrammarV1SuccessOutcome
            , GrammarV1NegativeOutcome
            , GrammarV1TerminalOutcome
            , GrammarV1FatalOutcome
            ]
            specs
          assertClaimApplication "Ready" ["x"] obligation
          let residues = [residue | Located _ (GrammarV1CallableOutcomeResidue residue) <- residueClauses]
          assert (length residues == 4) "expected four outcome residues"
          case residues of
            [successResidue, negativeResidue, terminalResidue, fatalResidue] -> do
              assertResidueKind GrammarV1SuccessOutcome successResidue
              assertResidueKind GrammarV1NegativeOutcome negativeResidue
              assertResidueKind GrammarV1TerminalOutcome terminalResidue
              assertResidueKind GrammarV1FatalOutcome fatalResidue
              assertResidueCallee GrammarV1CalleePreserve successResidue
              assertResidueCallee GrammarV1CalleePreserve negativeResidue
              assertResidueCallee GrammarV1CalleeConsume terminalResidue
              assertResidueCallee GrammarV1CalleeConsume fatalResidue
              case grammarV1OutcomeResidueClauses (locatedValue successResidue) of
                [ Located _ (GrammarV1OutcomeState [Located _ slot])
                  , Located _ (GrammarV1OutcomeObligation preserved)
                  , Located _ (GrammarV1OutcomeCallee _)
                  ] -> do
                    assert (locatedValue (grammarV1StateSlotName slot) == "x_next")
                      "success state slot was not x_next"
                    assertClaimApplication "Preserved" ["x_next"] preserved
                other -> Left ("unexpected success obligation residue " <> show other)
            _ -> Left "internal four-residue assertion mismatch"
      clauses -> Left ("unexpected outcome-kinds callable clauses " <> show clauses)

assertOutcomeKinds
  :: [GrammarV1OutcomeKind]
  -> [Located GrammarV1OutcomeSpec]
  -> Either String ()
assertOutcomeKinds expected specs =
  assert
    (map (locatedValue . grammarV1OutcomeSpecKind . locatedValue) specs == expected)
    ("unexpected outcome kinds " <> show (map (locatedValue . grammarV1OutcomeSpecKind . locatedValue) specs))

assertResidueKind
  :: GrammarV1OutcomeKind
  -> Located GrammarV1OutcomeResidue
  -> Either String ()
assertResidueKind expected residue =
  assert
    (locatedValue (grammarV1OutcomeResidueKind (locatedValue residue)) == expected)
    ("unexpected residue kind " <> show (locatedValue (grammarV1OutcomeResidueKind (locatedValue residue))))

assertResidueCallee
  :: GrammarV1CalleeTransition
  -> Located GrammarV1OutcomeResidue
  -> Either String ()
assertResidueCallee expected residue =
  case [transition | Located _ (GrammarV1OutcomeCallee transition) <- grammarV1OutcomeResidueClauses (locatedValue residue)] of
    [transition] ->
      assert (locatedValue transition == expected)
        ("unexpected residue callee " <> show (locatedValue transition))
    transitions -> Left ("expected exactly one residue callee, got " <> show transitions)

assertCalleePreserve :: Located GrammarV1CalleeTransition -> Either String ()
assertCalleePreserve transition =
  assert (locatedValue transition == GrammarV1CalleePreserve)
    ("expected preserve callee, got " <> show (locatedValue transition))

assertStaticReferenceName
  :: Text.Text
  -> Located GrammarV1StaticReference
  -> Either String ()
assertStaticReferenceName expected reference = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName (locatedValue reference)) == [expected])
    ("expected static reference " <> Text.unpack expected)
  assert (null (grammarV1StaticReferenceArguments (locatedValue reference)))
    "unexpected static arguments on replacement reference"

assertNamedType :: Text.Text -> GrammarV1Type -> Either String ()
assertNamedType expected ty = case ty of
  GrammarV1NamedType reference -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "unexpected static arguments on named type"
  other -> Left ("expected named type, got " <> show other)

assertTrue :: Located GrammarV1Proposition -> Either String ()
assertTrue proposition =
  assert (locatedValue proposition == GrammarV1TrueProposition)
    ("expected true proposition, got " <> show (locatedValue proposition))

assertClaimApplication
  :: Text.Text
  -> [Text.Text]
  -> Located GrammarV1Proposition
  -> Either String ()
assertClaimApplication expectedClaim expectedArguments (Located _ proposition) =
  case proposition of
    GrammarV1ClaimApplicationProposition reference arguments -> do
      assert
        (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedClaim])
        ("unexpected claim application " <> show reference)
      assert (length arguments == length expectedArguments)
        "unexpected claim application arity"
      sequence_ (zipWith assertSimpleName expectedArguments arguments)
    other -> Left ("expected claim application proposition, got " <> show other)

assertNameIntegerRelation
  :: GrammarV1RelationOperator
  -> Text.Text
  -> Text.Text
  -> Located GrammarV1Proposition
  -> Either String ()
assertNameIntegerRelation expectedOperator expectedName expectedInteger (Located _ proposition) =
  case proposition of
    GrammarV1RelationProposition left operator right -> do
      assert (locatedValue operator == expectedOperator)
        ("unexpected relation operator " <> show (locatedValue operator))
      assertSimpleName expectedName left
      case locatedValue right of
        GrammarV1IntegerExpression value ->
          assert (value == expectedInteger)
            ("expected integer " <> Text.unpack expectedInteger <> ", got " <> Text.unpack value)
        other -> Left ("expected integer expression, got " <> show other)
    other -> Left ("expected relation proposition, got " <> show other)

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "unexpected static arguments on simple name"
    assert (null arguments) "unexpected term arguments on simple name"
  other -> Left ("expected simple name expression, got " <> show other)

onlyCallable
  :: Either GrammarV1ParseDiagnostic GrammarV1SourceFile
  -> Either String GrammarV1CallableContractDecl
onlyCallable parsed = do
  sourceFile <- mapLeft show parsed
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableContractDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

callRelationDisambiguation :: Either String ()
callRelationDisambiguation = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "call-relation" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ClaimDeclaration claimDecl -> case grammarV1ClaimProposition claimDecl of
        Just (Located _ (GrammarV1RelationProposition left operator right)) -> do
          assert (locatedValue operator == GrammarV1EqualRelation)
            "call relation operator was not equality"
          case locatedValue left of
            GrammarV1NameExpression reference [argument] -> do
              assert
                (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == ["P"])
                "relation left call was not P"
              assertSimpleName "x" argument
            other -> Left ("expected P(x) as relation left expression, got " <> show other)
          assertSimpleName "x" right
        other -> Left ("expected relation proposition, got " <> show other)
      other -> Left ("expected claim declaration, got " <> show other)
    declarations -> Left ("expected one claim declaration, got " <> show (length declarations))
  where
    source = "claim R(x : U32) = P(x) == x;"

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
