{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-005 declaration prefixes have one preserved concrete family" declarationFamiliesPreserved
    , test "SURF-005 brace-led static actuals have one preserved concrete category" braceActualsPreserved
    , test "SURF-005 grouping and tuple syntax remain structurally distinct" groupingTuplePreserved
    , test "SURF-005 session keyword forms remain distinct from static session references" sessionFormsPreserved
    , test "SURF-005 local suffixes attach before returning to enclosing statements" localSuffixAttachmentPreserved
    , test "SURF-005 nested using clauses attach to the innermost eligible expression" nestedUsingAttachmentPreserved
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

declarationFamiliesPreserved :: Either String ()
declarationFamiliesPreserved = do
  sourceFile <- parse "determinacy-declarations" $ Text.unlines
    [ "record Plain { value : U8 }"
    , "record Linear mode linear { value : U8 }"
    , "data Choice mode affine = Left | Right;"
    , "capability Copyable mode unrestricted {}"
    , "provider Store {}"
    , "provider implementation MemoryStore satisfies Store {}"
    , "opaque provider implementation RemoteStore satisfies Store;"
    ]
  case map (locatedValue . grammarV1Declaration . locatedValue) (grammarV1TopLevelDecls sourceFile) of
    [ GrammarV1RecordDeclaration plain
      , GrammarV1RecordDeclaration linear
      , GrammarV1DataDeclaration choice
      , GrammarV1CapabilityDeclaration capability
      , GrammarV1ProviderContractDeclaration _
      , GrammarV1ProviderImplementationDeclaration _
      , GrammarV1OpaqueProviderImplementationDeclaration _
      ] -> do
        assert (grammarV1RecordMode plain == Nothing) "plain record acquired a mode clause"
        assert (grammarV1RecordMode linear == Just GrammarV1Linear) "linear record lost its exact mode"
        assert (grammarV1DataMode choice == Just GrammarV1Affine) "data declaration lost affine mode"
        assert (grammarV1CapabilityMode capability == GrammarV1Unrestricted) "capability mode was not unrestricted"
    other -> Left ("unexpected declaration-family parse " <> show other)

braceActualsPreserved :: Either String ()
braceActualsPreserved = do
  sourceFile <- parse "determinacy-braces" $ Text.unlines
    [ "type EffectActual = Box[{IO, Audit(x)}];"
    , "type Refined = Box[{v : U8 | v > 0}];"
    ]
  aliases <- traverse onlyAlias (grammarV1TopLevelDecls sourceFile)
  case aliases of
    [effectsAlias, refinedAlias] -> do
      effects <- aliasArguments effectsAlias
      refined <- aliasArguments refinedAlias
      case effects of
        [GrammarV1StaticEffectSetArgument (Located _ (GrammarV1EffectSetLiteral values))] ->
          assert (length values == 2) "effect-set actual did not preserve two effects"
        other -> Left ("brace-led effect actual was reinterpreted as " <> show other)
      case refined of
        [GrammarV1StaticTypeArgument (GrammarV1RefinementType binder baseType proposition)] -> do
          assert (locatedValue binder == "v") "refinement binder was not v"
          assert (locatedValue baseType == GrammarV1UnsignedType "U8") "refinement base type was not U8"
          case locatedValue proposition of
            GrammarV1RelationProposition _ operator _ ->
              assert (locatedValue operator == GrammarV1GreaterRelation) "refinement relation was not >"
            other -> Left ("refinement proposition was reinterpreted as " <> show other)
        other -> Left ("brace-led refinement actual was reinterpreted as " <> show other)
    other -> Left ("expected two aliases, got " <> show (length other))

groupingTuplePreserved :: Either String ()
groupingTuplePreserved = do
  sourceFile <- parse "determinacy-parentheses" $ Text.unlines
    [ "type Grouped = Box[(1 + 2)];"
    , "type Tupled = Box[(U8, Bool)];"
    ]
  aliases <- traverse onlyAlias (grammarV1TopLevelDecls sourceFile)
  case aliases of
    [groupedAlias, tupleAlias] -> do
      grouped <- aliasArguments groupedAlias
      tupled <- aliasArguments tupleAlias
      case grouped of
        [GrammarV1StaticValueArgument (Located _ (GrammarV1StaticValueParenthesized _))] -> Right ()
        other -> Left ("grouped static value was reinterpreted as " <> show other)
      case tupled of
        [GrammarV1StaticTypeArgument (GrammarV1TupleType [Located _ left, Located _ right])] -> do
          assert (left == GrammarV1UnsignedType "U8") "tuple left type was not U8"
          assert (right == GrammarV1BoolType) "tuple right type was not Bool"
        other -> Left ("tuple type was reinterpreted as " <> show other)
    other -> Left ("expected two aliases, got " <> show (length other))

sessionFormsPreserved :: Either String ()
sessionFormsPreserved = do
  sourceFile <- parse "determinacy-sessions" $ Text.unlines
    [ "protocol P {"
    , "  role client = Next;"
    , "  role server = send (x : U8) then Next;"
    , "}"
    ]
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1ProtocolDeclaration protocol ->
        case grammarV1ProtocolRoles protocol of
          [Located _ client, Located _ server] -> do
            case locatedValue (grammarV1RoleSessionExpression client) of
              GrammarV1SessionReference reference ->
                assert
                  (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == ["Next"])
                  "static session reference was not Next"
              other -> Left ("static session reference was reinterpreted as " <> show other)
            case locatedValue (grammarV1RoleSessionExpression server) of
              GrammarV1SessionSend _ _ _ continuation -> case locatedValue continuation of
                GrammarV1SessionReference reference ->
                  assert
                    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == ["Next"])
                    "send continuation was not Next"
                other -> Left ("send continuation was not a session reference: " <> show other)
              other -> Left ("send session was reinterpreted as " <> show other)
          roles -> Left ("expected two protocol roles, got " <> show roles)
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one protocol declaration, got " <> show declarations)

localSuffixAttachmentPreserved :: Either String ()
localSuffixAttachmentPreserved = do
  functionDecl <- parseOnlyFunction "determinacy-local-suffix" $ Text.unlines
    [ "fn attach(x : U8) -> U8 satisfies Attach {"
    , "  let called = f(x);"
    , "  let qualified = pkg.value;"
    , "  let projected = (x).field;"
    , "  let closed = close x + 1 * 2;"
    , "  return x or fail Problem(x);"
    , "}"
    ]
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
    [ Located _ (GrammarV1LetStatement _ called)
      , Located _ (GrammarV1LetStatement _ qualified)
      , Located _ (GrammarV1LetStatement _ projected)
      , Located _ (GrammarV1LetStatement _ closed)
      , Located _ (GrammarV1ReturnStatement failed)
      ] -> do
        case locatedValue called of
          GrammarV1NameExpression reference arguments -> do
            assertNameParts ["f"] reference
            assert (length arguments == 1) "f(x) did not attach its term arguments"
          other -> Left ("f(x) was not one name-call expression: " <> show other)
        case locatedValue qualified of
          GrammarV1NameExpression reference arguments -> do
            assertNameParts ["pkg", "value"] reference
            assert (null arguments) "qualified name unexpectedly acquired term arguments"
          other -> Left ("pkg.value was not one maximal qualified name: " <> show other)
        case locatedValue projected of
          GrammarV1ProjectionExpression receiver field -> do
            assert (locatedValue field == "field") "explicit projection field was not field"
            case locatedValue receiver of
              GrammarV1ParenthesizedExpression inner -> assertSimpleName "x" inner
              other -> Left ("projection receiver was not parenthesized x: " <> show other)
          other -> Left ("(x).field was not an explicit projection: " <> show other)
        case locatedValue closed of
          GrammarV1CloseExpression operand -> case locatedValue operand of
            GrammarV1BinaryExpression left addOp right -> do
              assertSimpleName "x" left
              assert (locatedValue addOp == GrammarV1Add) "close operand did not retain +"
              case locatedValue right of
                GrammarV1BinaryExpression one mulOp two -> do
                  assertInteger "1" one
                  assert (locatedValue mulOp == GrammarV1Multiply) "close operand did not retain *"
                  assertInteger "2" two
                other -> Left ("close additive RHS did not retain multiplication: " <> show other)
            other -> Left ("close did not consume its full additive operand: " <> show other)
          other -> Left ("close expression was reinterpreted as an outer binary expression: " <> show other)
        case locatedValue failed of
          GrammarV1FallbackExpression base (Located _ (GrammarV1FailFallback target)) -> do
            assertSimpleName "x" base
            assert (length (grammarV1FailureTargetArguments (locatedValue target)) == 1)
              "failure-target term arguments did not attach locally"
          other -> Left ("fail fallback did not retain its target arguments: " <> show other)
    statements -> Left ("unexpected local-suffix statement sequence " <> show statements)

nestedUsingAttachmentPreserved :: Either String ()
nestedUsingAttachmentPreserved = do
  functionDecl <- parseOnlyFunction "determinacy-nested-using" $ Text.unlines
    [ "fn nested() satisfies Nested {"
    , "  let exactInner = receive_exact 1 on receive_exact 2 using proof on endpoint;"
    , "  let exactOuter = receive_exact 1 using proof on (receive_exact 2 on endpoint);"
    , "  let selectInner = select A on select B using proof on endpoint;"
    , "  let selectOuter = select A using proof on (select B on endpoint);"
    , "}"
    ]
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
    [ Located _ (GrammarV1LetStatement _ exactInner)
      , Located _ (GrammarV1LetStatement _ exactOuter)
      , Located _ (GrammarV1LetStatement _ selectInner)
      , Located _ (GrammarV1LetStatement _ selectOuter)
      ] -> do
        case locatedValue exactInner of
          GrammarV1ReceiveExactExpression _ endpoint Nothing ->
            assertInnerReceiveUsing endpoint True
          other -> Left ("unparenthesized receive_exact did not bind using inward: " <> show other)
        case locatedValue exactOuter of
          GrammarV1ReceiveExactExpression _ endpoint (Just evidence) -> do
            assertSimpleName "proof" evidence
            assertInnerReceiveUsing endpoint False
          other -> Left ("parenthesized receive_exact did not expose using to outer expression: " <> show other)
        case locatedValue selectInner of
          GrammarV1SelectExpression _ endpoint Nothing ->
            assertInnerSelectUsing endpoint True
          other -> Left ("unparenthesized select did not bind using inward: " <> show other)
        case locatedValue selectOuter of
          GrammarV1SelectExpression _ endpoint (Just evidence) -> do
            assertSimpleName "proof" evidence
            assertInnerSelectUsing endpoint False
          other -> Left ("parenthesized select did not expose using to outer expression: " <> show other)
    statements -> Left ("unexpected nested-using statement sequence " <> show statements)

assertInnerReceiveUsing :: Located GrammarV1Expression -> Bool -> Either String ()
assertInnerReceiveUsing expression expectedUsing = do
  inner <- unwrapParenthesized expression
  case locatedValue inner of
    GrammarV1ReceiveExactExpression _ endpoint evidence -> do
      assertSimpleName "endpoint" endpoint
      assert (isJustEvidence evidence == expectedUsing)
        ("inner receive_exact using presence was " <> show (isJustEvidence evidence))
    other -> Left ("expected inner receive_exact, got " <> show other)

assertInnerSelectUsing :: Located GrammarV1Expression -> Bool -> Either String ()
assertInnerSelectUsing expression expectedUsing = do
  inner <- unwrapParenthesized expression
  case locatedValue inner of
    GrammarV1SelectExpression _ endpoint evidence -> do
      assertSimpleName "endpoint" endpoint
      assert (isJustEvidence evidence == expectedUsing)
        ("inner select using presence was " <> show (isJustEvidence evidence))
    other -> Left ("expected inner select, got " <> show other)

unwrapParenthesized :: Located GrammarV1Expression -> Either String (Located GrammarV1Expression)
unwrapParenthesized expression = case locatedValue expression of
  GrammarV1ParenthesizedExpression inner -> Right inner
  _ -> Right expression

isJustEvidence :: Maybe a -> Bool
isJustEvidence (Just _) = True
isJustEvidence Nothing = False

parse :: Text.Text -> Text.Text -> Either String GrammarV1SourceFile
parse label source = either (Left . show) Right (parseGrammarV1StructuralSource label source)

parseOnlyFunction :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
parseOnlyFunction label source = do
  sourceFile <- parse label source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left ("expected one function declaration, got " <> show declarations)

onlyAlias :: Located GrammarV1TopLevelDecl -> Either String GrammarV1TypeAliasDecl
onlyAlias (Located _ top) = case locatedValue (grammarV1Declaration top) of
  GrammarV1TypeAliasDeclaration alias -> Right alias
  other -> Left ("expected type alias, got " <> show other)

aliasArguments :: GrammarV1TypeAliasDecl -> Either String [GrammarV1StaticArgument]
aliasArguments alias = case locatedValue (grammarV1TypeAliasTarget alias) of
  GrammarV1NamedType reference -> Right (grammarV1StaticReferenceArguments reference)
  other -> Left ("expected named alias target, got " <> show other)

assertNameParts :: [Text.Text] -> GrammarV1StaticReference -> Either String ()
assertNameParts expected reference =
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == expected)
    ("unexpected static-reference name " <> show (grammarV1StaticReferenceName reference))

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assertNameParts [expected] reference
    assert (null (grammarV1StaticReferenceArguments reference)) "unexpected static arguments"
    assert (null arguments) "unexpected term arguments"
  other -> Left ("expected simple name " <> Text.unpack expected <> ", got " <> show other)

assertInteger :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertInteger expected (Located _ expression) = case expression of
  GrammarV1IntegerExpression actual ->
    assert (actual == expected) ("expected integer " <> Text.unpack expected)
  other -> Left ("expected integer expression, got " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
