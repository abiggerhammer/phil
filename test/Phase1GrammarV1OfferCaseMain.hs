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
    [ testIO "SURF-002 term offer fixture preserves case patterns and arm blocks"
        expectTermOffer
    , testIO "SURF-002 offer plus transport composition parses end-to-end"
        expectOfferTransport
    , testIO "SURF-003 offer missing arm braces rejects at syntax"
        (expectFixtureReject "rejected/05-offer-missing-body-braces.phil")
    , test "SURF-002 record case binders and statement arm are preserved"
        recordCaseAndStatementArmPreserved
    , test "SURF-003 offer requires a nonempty arm set"
        emptyOfferRejects
    , test "SURF-003 case tuple binders reject trailing comma"
        tupleBinderTrailingCommaRejects
    , test "SURF-002 construct and borrow primaries preserve payloads"
        constructBorrowPreserved
    , test "SURF-002 match decide and break primaries preserve control structure"
        matchDecideBreakPreserved
    , test "SURF-003 control primaries reject malformed syntax"
        controlPrimariesRejectMalformed
    , test "SURF-002 protocol I/O primaries preserve exact operands"
        protocolIOPrimariesPreserved
    , test "SURF-002 protocol I/O optional clauses remain optional"
        protocolIOOptionalClausesPreserved
    , test "SURF-003 protocol I/O primaries reject malformed syntax"
        protocolIOPrimariesRejectMalformed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectTermOffer :: IO (Either String ())
expectTermOffer = do
  parsed <- parseFixture "accepted/05-term-offer.phil"
  pure $ do
    offer <- singleComponentOffer =<< mapLeft show parsed
    case offer of
      GrammarV1OfferExpression scrutinee [leftArm, rightArm] -> do
        assertSimpleName "endpoint" scrutinee
        assertArmName "Left" leftArm
        assertNoCaseBinders leftArm
        assertBlockReturnUnit leftArm
        assertArmName "Right" rightArm
        assertTupleBinders ["value"] rightArm
        assertBlockReturnName "value" rightArm
      other -> Left ("expected two-arm offer expression, got " <> show other)

expectOfferTransport :: IO (Either String ())
expectOfferTransport = do
  parsed <- parseFixture "accepted/09-offer-transport-composition.phil"
  pure $ do
    offer <- singleComponentOffer =<< mapLeft show parsed
    case offer of
      GrammarV1OfferExpression scrutinee [keepArm, convertArm] -> do
        assertSimpleName "endpoint" scrutinee
        assertArmName "Keep" keepArm
        assertBlockReturnName "value" keepArm
        assertArmName "Convert" convertArm
        case armBlockStatements convertArm of
          Right [Located _ (GrammarV1ReturnStatement returned)] ->
            case locatedValue returned of
              GrammarV1TransportExpression value target evidence -> do
                assertSimpleName "value" value
                assertBytesLengthName "m" (locatedValue target)
                assertSimpleName "equality" evidence
              other -> Left ("expected transport return in Convert arm, got " <> show other)
          Right statements -> Left ("expected one Convert-arm statement, got " <> show statements)
          Left detail -> Left detail
      other -> Left ("expected two-arm offer/transport expression, got " <> show other)

singleComponentOffer :: GrammarV1SourceFile -> Either String GrammarV1Expression
singleComponentOffer sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one component expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))

assertArmName :: Text.Text -> Located GrammarV1MatchArm -> Either String ()
assertArmName expected (Located _ arm) =
  let pattern' = locatedValue (grammarV1MatchArmPattern arm)
      actual = grammarV1QualifiedNameParts (locatedValue (grammarV1CasePatternName pattern'))
  in assert (actual == [expected])
      ("expected case pattern " <> Text.unpack expected <> ", got " <> show actual)

assertNoCaseBinders :: Located GrammarV1MatchArm -> Either String ()
assertNoCaseBinders (Located _ arm) =
  let pattern' = locatedValue (grammarV1MatchArmPattern arm)
  in assert (grammarV1CasePatternBinders pattern' == Nothing)
      "expected case pattern without binders"

assertTupleBinders :: [Text.Text] -> Located GrammarV1MatchArm -> Either String ()
assertTupleBinders expected (Located _ arm) =
  let pattern' = locatedValue (grammarV1MatchArmPattern arm)
  in case grammarV1CasePatternBinders pattern' of
      Just (GrammarV1TupleCaseBinders binders) ->
        assert (map locatedValue binders == expected)
          ("unexpected tuple binders " <> show (map locatedValue binders))
      other -> Left ("expected tuple case binders, got " <> show other)

assertBlockReturnUnit :: Located GrammarV1MatchArm -> Either String ()
assertBlockReturnUnit arm = do
  statements <- armBlockStatements arm
  case statements of
    [Located _ (GrammarV1ReturnStatement expression)] ->
      assert (locatedValue expression == GrammarV1UnitExpression)
        "arm did not return unit"
    other -> Left ("expected one return-unit statement, got " <> show other)

assertBlockReturnName :: Text.Text -> Located GrammarV1MatchArm -> Either String ()
assertBlockReturnName expected arm = do
  statements <- armBlockStatements arm
  case statements of
    [Located _ (GrammarV1ReturnStatement expression)] -> assertSimpleName expected expression
    other -> Left ("expected one return-name statement, got " <> show other)

armBlockStatements :: Located GrammarV1MatchArm -> Either String [Located GrammarV1Statement]
armBlockStatements (Located _ arm) = case grammarV1MatchArmBody arm of
  GrammarV1MatchArmBlock block -> Right (grammarV1BlockStatements (locatedValue block))
  other -> Left ("expected block arm body, got " <> show other)

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected simple name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "simple name unexpectedly had static arguments"
    assert (null arguments) "simple name unexpectedly had term arguments"
  other -> Left ("expected simple name expression, got " <> show other)

assertBytesLengthName :: Text.Text -> GrammarV1Type -> Either String ()
assertBytesLengthName expected ty = case ty of
  GrammarV1BytesType expression -> assertSimpleName expected expression
  other -> Left ("expected Bytes type, got " <> show other)

recordCaseAndStatementArmPreserved :: Either String ()
recordCaseAndStatementArmPreserved = do
  offer <- singleComponentOffer =<< mapLeft show
    (parseGrammarV1StructuralSource "record-case" source)
  case offer of
    GrammarV1OfferExpression _ [Located _ arm] -> do
      let pattern' = locatedValue (grammarV1MatchArmPattern arm)
      assert
        (grammarV1QualifiedNameParts (locatedValue (grammarV1CasePatternName pattern')) == ["Packet"])
        "record case pattern name was not Packet"
      case grammarV1CasePatternBinders pattern' of
        Just (GrammarV1RecordCaseBinders [Located _ first, Located _ second]) -> do
          assert (locatedValue (grammarV1FieldBinderField first) == "payload")
            "first field binder was not payload"
          assert ((locatedValue <$> grammarV1FieldBinderAlias first) == Just "p")
            "payload alias was not p"
          assert (locatedValue (grammarV1FieldBinderField second) == "tag")
            "second field binder was not tag"
          assert (grammarV1FieldBinderAlias second == Nothing)
            "tag unexpectedly had an alias"
        other -> Left ("expected two record field binders, got " <> show other)
      case grammarV1MatchArmBody arm of
        GrammarV1MatchArmStatement (Located _ (GrammarV1ReturnStatement expression)) ->
          assertSimpleName "p" expression
        other -> Left ("expected statement arm body returning p, got " <> show other)
    other -> Left ("expected one-arm offer expression, got " <> show other)
  where
    source = Text.unlines
      [ "component C(x : Packet) {"
      , "  offer x {"
      , "    Packet{payload as p, tag,} => return p"
      , "  }"
      , "}"
      ]

constructBorrowPreserved :: Either String ()
constructBorrowPreserved = do
  statements <- singleComponentStatements =<< mapLeft show
    (parseGrammarV1StructuralSource "construct-borrow" source)
  case statements of
    [ Located _ (GrammarV1LetStatement _ constructed)
      , Located _ (GrammarV1LetStatement _ borrowed)
      , Located _ (GrammarV1ReturnStatement returned)
      ] -> do
        case locatedValue constructed of
          GrammarV1ConstructExpression target [(leftName, leftValue), (rightName, rightValue)] -> do
            assert
              (grammarV1QualifiedNameParts
                (grammarV1StaticReferenceName (locatedValue target)) == ["Pair"])
              "construct target was not Pair"
            assert (null (grammarV1StaticReferenceArguments (locatedValue target)))
              "construct target unexpectedly had static arguments"
            assert (locatedValue leftName == "left") "first construct field was not left"
            assertSimpleName "x" leftValue
            assert (locatedValue rightName == "right") "second construct field was not right"
            assertSimpleName "y" rightValue
          other -> Left ("expected two-field construct expression, got " <> show other)
        case locatedValue borrowed of
          GrammarV1BorrowExpression value binder body -> do
            assertSimpleName "made" value
            assert (locatedValue binder == "view") "borrow binder was not view"
            case grammarV1BlockStatements (locatedValue body) of
              [Located _ (GrammarV1ReturnStatement result)] -> assertSimpleName "view" result
              other -> Left ("expected borrow body to return view, got " <> show other)
          other -> Left ("expected borrow expression, got " <> show other)
        assertSimpleName "borrowed" returned
    other -> Left ("expected construct, borrow, return statements, got " <> show other)
  where
    source = Text.unlines
      [ "component C(x : U32, y : U32) {"
      , "  let made = construct Pair { left = x, right = y, }"
      , "  let borrowed = borrow made as view { return view }"
      , "  return borrowed"
      , "}"
      ]

matchDecideBreakPreserved :: Either String ()
matchDecideBreakPreserved = do
  statements <- singleComponentStatements =<< mapLeft show
    (parseGrammarV1StructuralSource "match-decide-break" source)
  case statements of
    [ Located _ (GrammarV1LetStatement _ matched)
      , Located _ (GrammarV1LetStatement _ decided)
      , Located _ (GrammarV1ExpressionStatement broken)
      ] -> do
        case locatedValue matched of
          GrammarV1MatchExpression scrutinee (Just joinClause) [leftArm, rightArm] -> do
            assertSimpleName "tagged" scrutinee
            let joinValue = locatedValue joinClause
            case grammarV1JoinState joinValue of
              [Located _ slot] -> do
                assert (locatedValue (grammarV1StateSlotName slot) == "saved")
                  "match join slot was not saved"
                assert (locatedValue (grammarV1StateSlotType slot) == GrammarV1UnsignedType "U32")
                  "match join slot type was not U32"
              other -> Left ("expected one match join state slot, got " <> show other)
            assert
              ((locatedValue <$> grammarV1JoinInvariant joinValue) == Just GrammarV1TrueProposition)
              "match join invariant was not true"
            assertArmName "Left" leftArm
            assertTupleBinders ["value"] leftArm
            assertBlockReturnName "value" leftArm
            assertArmName "Right" rightArm
          other -> Left ("expected joined match expression, got " <> show other)
        case locatedValue decided of
          GrammarV1DecideExpression
            (Located _ (GrammarV1BinaryExpression left (Located _ GrammarV1Add) right))
            [yesArm, noArm] -> do
              assertSimpleName "x" left
              assertSimpleName "y" right
              assertArmName "Yes" yesArm
              assertArmName "No" noArm
          other -> Left ("expected additive decide expression, got " <> show other)
        case locatedValue broken of
          GrammarV1BreakExpression [first, second] -> do
            assertSimpleName "x" first
            assertSimpleName "y" second
          other -> Left ("expected two-argument break expression, got " <> show other)
    other -> Left ("expected match, decide, break statements, got " <> show other)
  where
    source = Text.unlines
      [ "component C(tagged : Choice, x : U32, y : U32) {"
      , "  let matched = match tagged join state (saved : U32) invariant true {"
      , "    Left(value) => { return value }"
      , "    Right => return x"
      , "  }"
      , "  let decided = decide x + y {"
      , "    Yes => return x"
      , "    No => return y"
      , "  }"
      , "  break(x, y)"
      , "}"
      ]

controlPrimariesRejectMalformed :: Either String ()
controlPrimariesRejectMalformed = do
  expectReject "component C(x : U32) { construct Pair { field x } }"
  expectReject "component C(x : U32) { borrow x view { return view } }"
  expectReject "component C(x : T) { match x {} }"
  expectReject "component C(x : U32) { decide x {} }"
  expectReject "component C(x : U32) { break(x,) }"

protocolIOPrimariesPreserved :: Either String ()
protocolIOPrimariesPreserved = do
  statements <- singleComponentStatements =<< mapLeft show
    (parseGrammarV1StructuralSource "protocol-io-primaries" source)
  case statements of
    [ Located _ (GrammarV1LetStatement _ framed)
      , Located _ (GrammarV1LetStatement _ exact)
      , Located _ (GrammarV1LetStatement _ received)
      , Located _ (GrammarV1LetStatement _ recognized)
      , Located _ (GrammarV1LetStatement _ validated)
      , Located _ (GrammarV1ExpressionStatement sentExact)
      , Located _ (GrammarV1ExpressionStatement sent)
      , Located _ (GrammarV1ExpressionStatement selected)
      , Located _ (GrammarV1ExpressionStatement committed)
      ] -> do
        case locatedValue framed of
          GrammarV1ReceiveFrameExpression endpoint -> assertSimpleName "endpoint" endpoint
          other -> Left ("expected receive_frame expression, got " <> show other)
        case locatedValue exact of
          GrammarV1ReceiveExactExpression amount endpoint (Just evidence) -> do
            assertAddNames "n" "one" amount
            assertSimpleName "endpoint" endpoint
            assertSimpleName "proof" evidence
          other -> Left ("expected receive_exact expression with using, got " <> show other)
        case locatedValue received of
          GrammarV1ReceiveExpression resultType endpoint -> do
            assert (locatedValue resultType == GrammarV1UnsignedType "U32")
              "receive result type was not U32"
            assertSimpleName "endpoint" endpoint
          other -> Left ("expected receive expression, got " <> show other)
        case locatedValue recognized of
          GrammarV1RecognizeExpression recognizer input -> do
            assertStaticReferenceName "Packet" recognizer
            assertSimpleName "plain" input
          other -> Left ("expected recognize expression, got " <> show other)
        case locatedValue validated of
          GrammarV1ValidateExpression validator (Just position) endpoint -> do
            assertStaticReferenceName "Check" validator
            assertSimpleName "plain" position
            assertSimpleName "endpoint" endpoint
          other -> Left ("expected validate expression with at, got " <> show other)
        case locatedValue sentExact of
          GrammarV1SendExactExpression value endpoint -> do
            assertSimpleName "n" value
            assertSimpleName "endpoint" endpoint
          other -> Left ("expected send_exact expression, got " <> show other)
        case locatedValue sent of
          GrammarV1SendExpression value endpoint -> do
            assertAddNames "n" "one" value
            assertSimpleName "endpoint" endpoint
          other -> Left ("expected send expression, got " <> show other)
        case locatedValue selected of
          GrammarV1SelectExpression branch endpoint (Just evidence) -> do
            let branchValue = locatedValue branch
            assert
              (grammarV1QualifiedNameParts (locatedValue (grammarV1BranchValueName branchValue)) == ["Ready"])
              "select branch name was not Ready"
            case grammarV1BranchValueArguments branchValue of
              [argument] -> assertSimpleName "n" argument
              other -> Left ("expected one select branch argument, got " <> show other)
            assertSimpleName "endpoint" endpoint
            assertSimpleName "proof" evidence
          other -> Left ("expected select expression with branch payload and using, got " <> show other)
        case locatedValue committed of
          GrammarV1CommitReceiveExpression input evidence -> do
            assertSimpleName "endpoint" input
            assertSimpleName "validated" evidence
          other -> Left ("expected commit_receive expression, got " <> show other)
    other -> Left ("expected nine protocol I/O statements, got " <> show other)
  where
    source = Text.unlines
      [ "component C(endpoint : Channel, n : U32, one : U32, proof : Proof[true]) {"
      , "  let framed = receive_frame(endpoint)"
      , "  let exact = receive_exact n + one on endpoint using proof"
      , "  let plain = receive U32 on endpoint"
      , "  let recognized = recognize Packet from plain"
      , "  let validated = validate Check at plain on endpoint"
      , "  send_exact n on endpoint"
      , "  send n + one on endpoint"
      , "  select Ready(n) on endpoint using proof"
      , "  commit_receive endpoint using validated"
      , "}"
      ]

protocolIOOptionalClausesPreserved :: Either String ()
protocolIOOptionalClausesPreserved = do
  statements <- singleComponentStatements =<< mapLeft show
    (parseGrammarV1StructuralSource "protocol-io-optionals" source)
  case statements of
    [ Located _ (GrammarV1ExpressionStatement exact)
      , Located _ (GrammarV1ExpressionStatement validated)
      , Located _ (GrammarV1ExpressionStatement selected)
      ] -> do
        case locatedValue exact of
          GrammarV1ReceiveExactExpression _ _ Nothing -> Right ()
          other -> Left ("expected receive_exact without using, got " <> show other)
        case locatedValue validated of
          GrammarV1ValidateExpression _ Nothing _ -> Right ()
          other -> Left ("expected validate without at, got " <> show other)
        case locatedValue selected of
          GrammarV1SelectExpression branch _ Nothing -> do
            let branchValue = locatedValue branch
            assert (null (grammarV1BranchValueArguments branchValue))
              "payload-free select unexpectedly had branch arguments"
          other -> Left ("expected select without using, got " <> show other)
    other -> Left ("expected three optional-clause statements, got " <> show other)
  where
    source = Text.unlines
      [ "component C(endpoint : Channel, n : U32) {"
      , "  receive_exact n on endpoint"
      , "  validate Check on endpoint"
      , "  select Ready on endpoint"
      , "}"
      ]

protocolIOPrimariesRejectMalformed :: Either String ()
protocolIOPrimariesRejectMalformed = do
  expectReject "component C(endpoint : Channel) { receive_frame endpoint }"
  expectReject "component C(endpoint : Channel, n : U32) { receive_exact n endpoint }"
  expectReject "component C(endpoint : Channel) { receive U32 endpoint }"
  expectReject "component C(x : U32) { recognize Packet x }"
  expectReject "component C(endpoint : Channel, x : U32) { validate Check x on endpoint }"
  expectReject "component C(endpoint : Channel, x : U32) { send_exact x endpoint }"
  expectReject "component C(endpoint : Channel, x : U32) { send x endpoint }"
  expectReject "component C(endpoint : Channel) { select Ready endpoint }"
  expectReject "component C(endpoint : Channel, x : U32) { commit_receive endpoint x }"

assertAddNames
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1Expression
  -> Either String ()
assertAddNames leftName rightName (Located _ expression) = case expression of
  GrammarV1BinaryExpression left (Located _ GrammarV1Add) right -> do
    assertSimpleName leftName left
    assertSimpleName rightName right
  other -> Left ("expected additive expression, got " <> show other)

assertStaticReferenceName
  :: Text.Text
  -> Located GrammarV1StaticReference
  -> Either String ()
assertStaticReferenceName expected (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
    ("unexpected static reference " <> show reference)
  assert (null (grammarV1StaticReferenceArguments reference))
    "static reference unexpectedly had static arguments"

singleComponentStatements
  :: GrammarV1SourceFile
  -> Either String [Located GrammarV1Statement]
singleComponentStatements sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        Right (grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)))
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))

emptyOfferRejects :: Either String ()
emptyOfferRejects = expectReject "component C(x : T) { offer x {} }"

tupleBinderTrailingCommaRejects :: Either String ()
tupleBinderTrailingCommaRejects =
  expectReject "component C(x : T) { offer x { Right(value,) => { return value } } }"

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "offer-negative" source of
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
