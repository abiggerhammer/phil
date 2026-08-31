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
    [ "type Effects = Box[{IO, Audit(x)}];"
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

parse :: Text.Text -> Text.Text -> Either String GrammarV1SourceFile
parse label source = either (Left . show) Right (parseGrammarV1StructuralSource label source)

onlyAlias :: Located GrammarV1TopLevelDecl -> Either String GrammarV1TypeAliasDecl
onlyAlias (Located _ top) = case locatedValue (grammarV1Declaration top) of
  GrammarV1TypeAliasDeclaration alias -> Right alias
  other -> Left ("expected type alias, got " <> show other)

aliasArguments :: GrammarV1TypeAliasDecl -> Either String [GrammarV1StaticArgument]
aliasArguments alias = case locatedValue (grammarV1TypeAliasTarget alias) of
  GrammarV1NamedType reference -> Right (grammarV1StaticReferenceArguments reference)
  other -> Left ("expected named alias target, got " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
