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
    [ testIO "SURF-002 record declaration fixture parses with exact linear mode"
        (expectFixtureMode "accepted/11-record-explicit-linear-mode.phil" GrammarV1Linear)
    , testIO "SURF-002 data declaration fixture parses with exact affine mode"
        (expectFixtureMode "accepted/12-sum-explicit-affine-mode.phil" GrammarV1Affine)
    , testIO "SURF-002 unrestricted capability fixture parses"
        (expectFixtureMode "accepted/13-capability-unrestricted-mode.phil" GrammarV1Unrestricted)
    , testIO "SURF-002 affine capability fixture parses"
        (expectFixtureMode "accepted/14-capability-affine-mode.phil" GrammarV1Affine)
    , testIO "SURF-002 linear capability fixture parses"
        (expectFixtureMode "accepted/15-capability-linear-mode.phil" GrammarV1Linear)
    , testIO "SURF-002 ordinary binding fixture preserves term parameter and let-return block"
        expectOrdinaryBinding
    , testIO "SURF-002 static type actual fixture preserves generic kind and argument"
        expectStaticTypeActual
    , testIO "SURF-002 static session parameter fixture preserves Session kind"
        expectStaticSessionParameter
    , testIO "SURF-002 generic requirement fixture preserves requirement categories"
        expectRequirementCategories
    , testIO "SURF-002 membership claim preserves relation proposition"
        (expectRelationClaim "accepted/03-membership.phil" "Contains" GrammarV1InRelation)
    , testIO "SURF-002 disjointness claim preserves relation proposition"
        (expectRelationClaim "accepted/04-disjointness.phil" "Separate" GrammarV1DisjointRelation)
    , testIO "SURF-003 membership relation missing RHS rejects at syntax"
        (expectFixtureReject "rejected/03-membership-missing-rhs.phil")
    , testIO "SURF-003 disjointness relation missing RHS rejects at syntax"
        (expectFixtureReject "rejected/04-disjointness-missing-rhs.phil")
    , testIO "SURF-003 malformed record mode rejects at syntax"
        (expectFixtureReject "rejected/10-record-mode-missing-literal.phil")
    , testIO "SURF-003 unknown capability mode rejects at syntax"
        (expectFixtureReject "rejected/11-capability-mode-unknown-literal.phil")
    , testIO "SURF-003 binding-local structural mode rejects at pattern syntax"
        (expectFixtureReject "rejected/12-binding-local-mode.phil")
    , testIO "SURF-003 type alias cannot acquire declaration mode"
        (expectFixtureReject "rejected/13-type-alias-mode.phil")
    , testIO "SURF-003 unclosed static argument list rejects at syntax"
        (expectFixtureReject "rejected/21-static-argument-unclosed.phil")
    , testIO "SURF-003 generic requirement missing semicolon rejects at syntax"
        (expectFixtureReject "rejected/22-generic-requirement-missing-semicolon.phil")
    , test "SURF-002 proposition precedence is not > and > or"
        propositionPrecedencePreserved
    , test "SURF-002 name-shaped static actual has one static-reference parse"
        nameShapedStaticActualPreserved
    , test "SURF-002 source envelope preserves module imports attributes and fields"
        sourceEnvelopePreserved
    , test "SURF-003 nontrivia trailing token cannot be ignored"
        trailingTokenRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectFixtureMode :: FilePath -> GrammarV1StructuralMode -> IO (Either String ())
expectFixtureMode relativePath expectedMode = do
  parsed <- parseFixture relativePath
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ topLevel] ->
        let actualMode = declarationMode (locatedValue (grammarV1Declaration topLevel))
        in assert (actualMode == Just expectedMode) $
            "expected mode " <> show expectedMode <> ", got " <> show actualMode
      declarations -> Left ("expected exactly one declaration, got " <> show (length declarations))

expectOrdinaryBinding :: IO (Either String ())
expectOrdinaryBinding = do
  parsed <- parseFixture "accepted/16-ordinary-binding-inherits-mode.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1ComponentDeclaration componentDecl -> do
          case grammarV1ComponentTermParams componentDecl of
            Just [Located _ param] -> do
              assert (locatedValue (grammarV1TermParamName param) == "x")
                "component parameter name was not x"
              assert (locatedValue (grammarV1TermParamType param) == GrammarV1UnsignedType "U32")
                "component parameter type was not U32"
            other -> Left ("expected exactly one component parameter, got " <> show other)
          case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
            [Located _ letStatement, Located _ returnStatement] -> do
              case letStatement of
                GrammarV1LetStatement pattern' initializer -> do
                  assert (identifierPatternNamed "y" pattern')
                    "let pattern did not bind y"
                  assert (nameExpressionNamed "x" initializer)
                    "let initializer was not the name expression x"
                other -> Left ("expected let statement first, got " <> show other)
              case returnStatement of
                GrammarV1ReturnStatement expression ->
                  assert (nameExpressionNamed "y" expression)
                    "return expression was not the name expression y"
                other -> Left ("expected return statement second, got " <> show other)
            statements -> Left ("expected exactly two component statements, got " <> show (length statements))
        other -> Left ("expected component declaration, got " <> show other)
      declarations -> Left ("expected one component declaration, got " <> show (length declarations))

identifierPatternNamed :: Text.Text -> Located GrammarV1Pattern -> Bool
identifierPatternNamed expected (Located _ pattern') = case pattern' of
  GrammarV1IdentifierPattern name -> locatedValue name == expected

nameExpressionNamed :: Text.Text -> Located GrammarV1Expression -> Bool
nameExpressionNamed expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments ->
    grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected]
      && null (grammarV1StaticReferenceArguments reference)
      && null arguments
  _ -> False

expectStaticTypeActual :: IO (Either String ())
expectStaticTypeActual = do
  parsed <- parseFixture "accepted/17-static-type-actual.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ firstTop, Located _ secondTop] -> do
        case locatedValue (grammarV1Declaration firstTop) of
          GrammarV1TypeAliasDeclaration aliasDecl ->
            assertGenericKind GrammarV1TypeKind (grammarV1TypeAliasGenericParams aliasDecl)
          other -> Left ("expected generic type alias first, got " <> show other)
        case locatedValue (grammarV1Declaration secondTop) of
          GrammarV1TypeAliasDeclaration aliasDecl ->
            case locatedValue (grammarV1TypeAliasTarget aliasDecl) of
              GrammarV1NamedType reference -> do
                assert
                  (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == ["Boxed"])
                  "static type application target was not Boxed"
                assert
                  (grammarV1StaticReferenceArguments reference ==
                    [GrammarV1StaticTypeArgument (GrammarV1UnsignedType "U32")])
                  "U32 was not preserved as the exact static type actual"
              other -> Left ("expected applied named type, got " <> show other)
          other -> Left ("expected applied type alias second, got " <> show other)
      declarations -> Left ("expected two type aliases, got " <> show (length declarations))

expectStaticSessionParameter :: IO (Either String ())
expectStaticSessionParameter = do
  parsed <- parseFixture "accepted/18-static-session-actual.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1ProtocolDeclaration protocolDecl -> do
          assertGenericKind GrammarV1SessionKind (grammarV1ProtocolGenericParams protocolDecl)
          assert (length (grammarV1ProtocolRoles protocolDecl) == 2)
            "protocol did not preserve its two role declarations"
          assert (all roleReferencesS (grammarV1ProtocolRoles protocolDecl))
            "protocol role session references were not preserved as S"
        other -> Left ("expected protocol declaration, got " <> show other)
      declarations -> Left ("expected one protocol declaration, got " <> show (length declarations))

expectRequirementCategories :: IO (Either String ())
expectRequirementCategories = do
  parsed <- parseFixture "accepted/19-generic-requirement-kinds.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1RecordDeclaration recordDecl -> do
          assertGenericKind GrammarV1TypeKind (grammarV1RecordGenericParams recordDecl)
          assert
            (map (requirementTag . locatedValue) (grammarV1RecordRequirements recordDecl) ==
              [ "authority"
              , "boundary-representation"
              , "representation"
              , "placement"
              , "cost"
              , "environment"
              ])
            "generic requirement categories were not preserved in source order"
        other -> Left ("expected constrained record declaration, got " <> show other)
      declarations -> Left ("expected one constrained record, got " <> show (length declarations))

expectRelationClaim
  :: FilePath
  -> Text.Text
  -> GrammarV1RelationOperator
  -> IO (Either String ())
expectRelationClaim relativePath expectedName expectedOperator = do
  parsed <- parseFixture relativePath
  pure $ do
    sourceFile <- mapLeft show parsed
    case reverse (grammarV1TopLevelDecls sourceFile) of
      Located _ topLevel : _ -> case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1ClaimDeclaration claimDecl -> do
          assert (locatedValue (grammarV1ClaimName claimDecl) == expectedName)
            "claim name was not preserved"
          case grammarV1ClaimProposition claimDecl of
            Just (Located _ (GrammarV1RelationProposition left operator right)) -> do
              assert (locatedValue operator == expectedOperator)
                "claim relation operator was not preserved"
              assert (isSimpleNameExpression left)
                "relation left operand was not a simple name expression"
              assert (isSimpleNameExpression right)
                "relation right operand was not a simple name expression"
            other -> Left ("expected relation proposition, got " <> show other)
        other -> Left ("expected claim declaration, got " <> show other)
      [] -> Left "expected at least one top-level declaration"

isSimpleNameExpression :: Located GrammarV1Expression -> Bool
isSimpleNameExpression (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments ->
    null (grammarV1StaticReferenceArguments reference) && null arguments
  _ -> False

propositionPrecedencePreserved :: Either String ()
propositionPrecedencePreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "proposition-precedence" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ClaimDeclaration claimDecl ->
        case grammarV1ClaimProposition claimDecl of
          Just (Located _ (GrammarV1OrProposition left right)) -> do
            case locatedValue left of
              GrammarV1NotProposition inner ->
                assert (isRelationProposition inner) "not did not bind to the relation"
              other -> Left ("expected not proposition on left of or, got " <> show other)
            case locatedValue right of
              GrammarV1AndProposition relation truth -> do
                assert (isRelationProposition relation) "and left side was not a relation"
                assert (locatedValue truth == GrammarV1TrueProposition)
                  "and right side was not true"
              other -> Left ("expected and proposition on right of or, got " <> show other)
          other -> Left ("expected top-level or proposition, got " <> show other)
      other -> Left ("expected claim declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))
  where
    source = "claim Logic(a : U32, b : U32, c : U32) = not (a == b) or a == c and true;"

isRelationProposition :: Located GrammarV1Proposition -> Bool
isRelationProposition (Located _ proposition) = case proposition of
  GrammarV1RelationProposition _ _ _ -> True
  _ -> False

assertGenericKind
  :: GrammarV1GenericKind
  -> [Located GrammarV1GenericParam]
  -> Either String ()
assertGenericKind expected params = case params of
  [Located _ param] ->
    assert (locatedValue (grammarV1GenericParamKind param) == expected) $
      "expected generic kind " <> show expected
        <> ", got " <> show (locatedValue (grammarV1GenericParamKind param))
  values -> Left ("expected exactly one generic parameter, got " <> show (length values))

roleReferencesS :: Located GrammarV1RoleSessionDecl -> Bool
roleReferencesS (Located _ roleDecl) =
  case locatedValue (grammarV1RoleSessionExpression roleDecl) of
    GrammarV1SessionReference reference ->
      grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == ["S"]
        && null (grammarV1StaticReferenceArguments reference)
    _ -> False

requirementTag :: GrammarV1GenericRequirement -> String
requirementTag requirement = case requirement of
  GrammarV1StructuralRequirement _ _ -> "structural"
  GrammarV1PropositionRequirement _ -> "proposition"
  GrammarV1ProviderRequirement _ _ -> "provider"
  GrammarV1CallableRequirement _ _ -> "callable"
  GrammarV1BoundaryRequirement _ _ -> "boundary"
  GrammarV1ArchitectureRequirement _ _ -> "architecture"
  GrammarV1EffectsRequirement _ _ -> "effects"
  GrammarV1AuthorityRequirement _ -> "authority"
  GrammarV1BoundaryRepresentationRequirement _ -> "boundary-representation"
  GrammarV1RepresentationRequirement _ -> "representation"
  GrammarV1PlacementRequirement _ -> "placement"
  GrammarV1CostRequirement _ -> "cost"
  GrammarV1EnvironmentRequirement _ -> "environment"

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

declarationMode :: GrammarV1Declaration -> Maybe GrammarV1StructuralMode
declarationMode declaration = case declaration of
  GrammarV1RecordDeclaration value -> grammarV1RecordMode value
  GrammarV1DataDeclaration value -> grammarV1DataMode value
  GrammarV1TypeAliasDeclaration _ -> Nothing
  GrammarV1ClaimDeclaration _ -> Nothing
  GrammarV1CallableContractDeclaration _ -> Nothing
  GrammarV1FunctionDeclaration _ -> Nothing
  GrammarV1ProviderContractDeclaration _ -> Nothing
  GrammarV1ProviderImplementationDeclaration _ -> Nothing
  GrammarV1OpaqueProviderImplementationDeclaration _ -> Nothing
  GrammarV1CapabilityDeclaration value -> Just (grammarV1CapabilityMode value)
  GrammarV1BoundaryDeclaration _ -> Nothing
  GrammarV1ProtocolDeclaration _ -> Nothing
  GrammarV1ComponentDeclaration _ -> Nothing
  GrammarV1ArchitectureDeclaration _ -> Nothing
  GrammarV1ProgramDeclaration _ -> Nothing

nameShapedStaticActualPreserved :: Either String ()
nameShapedStaticActualPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "name-shaped-static" source
  case grammarV1TopLevelDecls sourceFile of
    [_, Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1TypeAliasDeclaration aliasDecl ->
        case locatedValue (grammarV1TypeAliasTarget aliasDecl) of
          GrammarV1NamedType reference ->
            assert
              (grammarV1StaticReferenceArguments reference ==
                [ GrammarV1StaticReferenceArgument
                    (GrammarV1StaticReference
                      { grammarV1StaticReferenceName = GrammarV1QualifiedName ["T"]
                      , grammarV1StaticReferenceArguments = []
                      })
                ])
              "name-shaped static actual was reinterpreted as a type alternative"
          other -> Left ("expected named type application, got " <> show other)
      other -> Left ("expected second type alias, got " <> show other)
    declarations -> Left ("expected two declarations, got " <> show (length declarations))
  where
    source = Text.unlines
      [ "type Ref[T : Type] = T;"
      , "type Use = Ref[T];"
      ]

sourceEnvelopePreserved :: Either String ()
sourceEnvelopePreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "envelope" source
  assert (hasModule sourceFile) "module declaration was not preserved"
  assert (length (grammarV1ImportDecls sourceFile) == 2) "expected two import declarations"
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> do
      assert (length (grammarV1Attributes topLevel) == 1) "expected one declaration attribute"
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1RecordDeclaration recordDecl -> do
          assert (grammarV1RecordMode recordDecl == Just GrammarV1Unrestricted)
            "record mode was not preserved"
          assert (length (grammarV1RecordFields recordDecl) == 2)
            "record fields were not preserved"
        other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))
  where
    source = Text.unlines
      [ "module demo.root;"
      , "import dep.alpha;"
      , "import dep.beta { x, y };"
      , "@key(\"decl.demo\")"
      , "record R mode unrestricted {"
      , "  x : U32,"
      , "  y : dep.T,"
      , "}"
      ]

hasModule :: GrammarV1SourceFile -> Bool
hasModule sourceFile = case grammarV1ModuleDecl sourceFile of
  Just _ -> True
  Nothing -> False

trailingTokenRejects :: Either String ()
trailingTokenRejects = case parseGrammarV1StructuralSource "trailing" source of
  Left _ -> Right ()
  Right value -> Left ("expected complete-input rejection, got " <> show value)
  where
    source = "module demo; record R {} stray"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
