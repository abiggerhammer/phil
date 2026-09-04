{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.CallableRefinement (CallableAuthorityRequirement (..))
import Phil.Surface.GrammarV1.CallableAuthority
  ( grammarV1CallableAuthorityBounds
  )
import Phil.Surface.GrammarV1.CallableEffects
  ( grammarV1CallableEffectBounds
  )
import Phil.Surface.GrammarV1.CallableResources
  ( GrammarV1CallableResourceClause (..)
  , GrammarV1CallableResourceDisposition (..)
  , grammarV1CallableResourceClauses
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-002 callable/effects slice preserves all callable clauses" callableClausesPreserved
    , test "SURF-002 effect-set references remain distinct from literals" effectSetReferencePreserved
    , test "SURF-008 simple callable effect literals preserve exact Core identities"
        simpleEffectSemantics
    , test "SURF-008 simple callable authority types preserve exact Core identities"
        simpleAuthoritySemantics
    , test "SURF-008 callable consumes and borrows preserve exact unresolved resource intent"
        callableResourceSemantics
    , test "SURF-002 effect-set trailing comma rejects at syntax" $
        expectReject "callable C() -> Unit { effects {IO,}; }"
    , test "SURF-002 name-set trailing comma rejects at syntax" $
        expectReject "callable C() -> Unit { consumes {x,}; }"
    , test "SURF-002 effects requirement requires within" $
        expectReject "callable C[E : Effects] requires { effects E {IO}; } () -> Unit {}"
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

callableClausesPreserved :: Either String ()
callableClausesPreserved = do
  callable <- onlyCallable fullCallableSource
  case grammarV1CallableRequirements callable of
    [Located _ (GrammarV1EffectsRequirement effectParam effectBound)] -> do
      assert (locatedValue effectParam == "E") "effects requirement parameter was not E"
      assertEffectLiteral ["IO", "Audit"] effectBound
    requirements -> Left ("expected one effects requirement, got " <> show requirements)
  case grammarV1CallableClauses callable of
    [ Located _ (GrammarV1CallableRequires requires)
      , Located _ (GrammarV1CallableConsumes consumes)
      , Located _ (GrammarV1CallableBorrows borrows)
      , Located _ (GrammarV1CallableAuthority authority)
      , Located _ (GrammarV1CallableEffects effects)
      , Located _ (GrammarV1CallableOutcomes outcomes)
      , Located _ (GrammarV1CallableOutcomeResidue residue)
      , Located _ (GrammarV1CallableEnsures ensures)
      , Located _ (GrammarV1CallableObligation obligation)
      , Located _ (GrammarV1CallableAssumes assumes)
      , Located _ (GrammarV1CallableCost cost)
      , Located _ (GrammarV1CallableCallee callee)
      ] -> do
        assertTrue requires
        assertQualifiedNames ["x", "store.slot"] consumes
        assertQualifiedNames ["loan"] borrows
        assertTypes ["Cap", "OtherCap"] authority
        assertEffectLiteralWithArguments effects
        assert (length outcomes == 1) "expected one callable outcome"
        case outcomes of
          [Located _ spec] -> do
            assert (locatedValue (grammarV1OutcomeSpecKind spec) == GrammarV1SuccessOutcome)
              "callable outcome kind was not success"
            assertNamedType "Unit" (grammarV1OutcomeSpecType spec)
          _ -> Left "internal one-outcome assertion mismatch"
        assert (locatedValue (grammarV1OutcomeResidueKind (locatedValue residue)) == GrammarV1SuccessOutcome)
          "outcome residue kind was not success"
        assertNamedType "Unit" (grammarV1OutcomeResidueType (locatedValue residue))
        assert (null (grammarV1OutcomeResidueClauses (locatedValue residue)))
          "empty outcome residue acquired clauses"
        assertTrue ensures
        assertTrue obligation
        assertTrue assumes
        assertInteger "7" cost
        assert (locatedValue callee == GrammarV1CalleePreserve)
          "callee transition was not preserve"
    clauses -> Left ("unexpected callable clauses " <> show clauses)

fullCallableSource :: Text.Text
fullCallableSource = Text.unlines
  [ "callable C[E : Effects] requires { effects E within {IO, Audit}; } (x : U32) -> Unit {"
  , "  requires true;"
  , "  consumes {x, store.slot};"
  , "  borrows {loan};"
  , "  authority {Cap, OtherCap};"
  , "  effects {IO, Audit(x)};"
  , "  outcomes {success Unit};"
  , "  outcome success Unit {}"
  , "  ensures true;"
  , "  obligation true;"
  , "  assumes true;"
  , "  cost 7;"
  , "  callee preserve;"
  , "}"
  ]

effectSetReferencePreserved :: Either String ()
effectSetReferencePreserved = do
  callable <- onlyCallable "callable C() -> Unit { effects E; }"
  case grammarV1CallableClauses callable of
    [Located _ (GrammarV1CallableEffects (Located _ effectSet))] ->
      case effectSet of
        GrammarV1EffectSetReference reference ->
          assertStaticReference "E" reference
        other -> Left ("expected effect-set reference, got " <> show other)
    clauses -> Left ("expected one effects clause, got " <> show clauses)

simpleEffectSemantics :: Either String ()
simpleEffectSemantics = do
  literal <- onlyCallable $ Text.unlines
    [ "callable EffectCarrier() -> Unit {"
    , "  effects {IO, pkg.Audit, IO};"
    , "  effects {};"
    , "}"
    ]
  assert
    (grammarV1CallableEffectBounds literal ==
      Just
        [ Set.fromList [SemanticEffect "IO", SemanticEffect "pkg.Audit"]
        , Set.empty
        ])
    "simple callable effect routing changed exact identity, clause order, or Set normalization"

  argumentBearing <- onlyCallable
    "callable ArgumentEffect(x : U8) -> Unit { effects {Audit(x)}; }"
  assert
    (grammarV1CallableEffectBounds argumentBearing == Nothing)
    "argument-bearing effect was flattened into a SemanticEffect identity"

  referenced <- onlyCallable
    "callable ReferencedEffects() -> Unit { effects E; }"
  assert
    (grammarV1CallableEffectBounds referenced == Nothing)
    "effect-set reference was treated as a concrete Core effect set"

simpleAuthoritySemantics :: Either String ()
simpleAuthoritySemantics = do
  literal <- onlyCallable $ Text.unlines
    [ "callable AuthorityCarrier() -> Unit {"
    , "  authority {Cap, pkg.ReadCap, Cap};"
    , "  authority {};"
    , "}"
    ]
  assert
    (grammarV1CallableAuthorityBounds literal ==
      Just
        [ Set.fromList
            [ CallableAuthorityRequirement "Cap"
            , CallableAuthorityRequirement "pkg.ReadCap"
            ]
        , Set.empty
        ])
    "simple callable authority routing changed exact identity, clause order, or Set normalization"

  specialized <- onlyCallable
    "callable SpecializedAuthority() -> Unit { authority {Cap[U8]}; }"
  assert
    (grammarV1CallableAuthorityBounds specialized == Nothing)
    "specialized authority type was flattened into a textual authority identity"

  structured <- onlyCallable
    "callable StructuredAuthority() -> Unit { authority {(U8, Bool)}; }"
  assert
    (grammarV1CallableAuthorityBounds structured == Nothing)
    "structured authority type was flattened into a textual authority identity"

callableResourceSemantics :: Either String ()
callableResourceSemantics = do
  callable <- onlyCallable $ Text.unlines
    [ "callable ResourceCarrier() -> Unit {"
    , "  consumes {owner, store.slot, owner};"
    , "  borrows {loan};"
    , "  consumes {};"
    , "  borrows {pkg.shared, loan};"
    , "}"
    ]
  case grammarV1CallableResourceClauses callable of
    [ GrammarV1CallableResourceClause
        GrammarV1CallableConsumesResource firstConsumes
      , GrammarV1CallableResourceClause
        GrammarV1CallableBorrowsResource firstBorrows
      , GrammarV1CallableResourceClause
        GrammarV1CallableConsumesResource emptyConsumes
      , GrammarV1CallableResourceClause
        GrammarV1CallableBorrowsResource secondBorrows
      ] -> do
        assertQualifiedNames ["owner", "store.slot", "owner"] firstConsumes
        assertQualifiedNames ["loan"] firstBorrows
        assert (null emptyConsumes) "explicit empty consumes clause was not preserved"
        assertQualifiedNames ["pkg.shared", "loan"] secondBorrows
    clauses -> Left
      ("callable resource clauses lost category, grouping, or source order: "
        <> show clauses)

  empty <- onlyCallable "callable NoResources() -> Unit {}"
  assert
    (null (grammarV1CallableResourceClauses empty))
    "callable without resource clauses acquired implicit resource behavior"

  generic <- onlyCallable
    "callable GenericResource[T : Type](x : T) -> Unit { consumes {x}; }"
  case grammarV1CallableResourceClauses generic of
    [GrammarV1CallableResourceClause GrammarV1CallableConsumesResource names] ->
      assertQualifiedNames ["x"] names
    clauses -> Left
      ("generic callable resource intent was reinterpreted before binder resolution: "
        <> show clauses)

assertEffectLiteral :: [Text.Text] -> Located GrammarV1EffectSetExpression -> Either String ()
assertEffectLiteral expected (Located _ effectSet) = case effectSet of
  GrammarV1EffectSetLiteral effects -> do
    assert (length effects == length expected) "unexpected effect-set literal arity"
    sequence_ (zipWith assertEffectName expected effects)
  other -> Left ("expected effect-set literal, got " <> show other)

assertEffectLiteralWithArguments :: Located GrammarV1EffectSetExpression -> Either String ()
assertEffectLiteralWithArguments (Located _ effectSet) = case effectSet of
  GrammarV1EffectSetLiteral
    [ Located _ firstEffect
      , Located _ secondEffect
      ] -> do
        assertStaticReference "IO" (grammarV1EffectReference firstEffect)
        assert (null (grammarV1EffectArguments firstEffect)) "IO effect unexpectedly had arguments"
        assertStaticReference "Audit" (grammarV1EffectReference secondEffect)
        case grammarV1EffectArguments secondEffect of
          [argument] -> assertSimpleName "x" argument
          arguments -> Left ("expected Audit(x), got " <> show arguments)
  other -> Left ("expected two-effect literal, got " <> show other)

assertEffectName :: Text.Text -> Located GrammarV1EffectExpression -> Either String ()
assertEffectName expected (Located _ effect) =
  assertStaticReference expected (grammarV1EffectReference effect)

assertQualifiedNames :: [Text.Text] -> [Located GrammarV1QualifiedName] -> Either String ()
assertQualifiedNames expected actual =
  assert
    (map (Text.intercalate "." . grammarV1QualifiedNameParts . locatedValue) actual == expected)
    ("unexpected qualified-name set " <> show actual)

assertTypes :: [Text.Text] -> [Located GrammarV1Type] -> Either String ()
assertTypes expected actual = do
  assert (length expected == length actual) "unexpected authority type-set arity"
  sequence_ (zipWith assertNamedType expected actual)

assertNamedType :: Text.Text -> Located GrammarV1Type -> Either String ()
assertNamedType expected (Located _ ty) = case ty of
  GrammarV1UnitType ->
    assert (expected == "Unit") ("expected named type " <> Text.unpack expected <> ", got Unit")
  GrammarV1NamedType reference -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "named type unexpectedly had static arguments"
  other -> Left ("expected type " <> Text.unpack expected <> ", got " <> show other)

assertStaticReference :: Text.Text -> Located GrammarV1StaticReference -> Either String ()
assertStaticReference expected (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
    ("expected static reference " <> Text.unpack expected)
  assert (null (grammarV1StaticReferenceArguments reference))
    "static reference unexpectedly had arguments"

assertTrue :: Located GrammarV1Proposition -> Either String ()
assertTrue proposition =
  assert (locatedValue proposition == GrammarV1TrueProposition)
    ("expected true proposition, got " <> show (locatedValue proposition))

assertInteger :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertInteger expected (Located _ expression) = case expression of
  GrammarV1IntegerExpression actual ->
    assert (actual == expected) ("expected integer " <> Text.unpack expected <> ", got " <> Text.unpack actual)
  other -> Left ("expected integer expression, got " <> show other)

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "simple name unexpectedly had static arguments"
    assert (null arguments) "simple name unexpectedly had term arguments"
  other -> Left ("expected simple name expression, got " <> show other)

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "callable-effects" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableContractDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "callable-effects-reject" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
