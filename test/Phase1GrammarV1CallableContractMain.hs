{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( declareOpaqueClaim
  , declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CallablePropositions
  ( grammarV1CallableAssumptions
  , grammarV1CallableEnsures
  , grammarV1CallableObligations
  , grammarV1CallableRequires
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1CheckedCallableSignature
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 refinement callable fixture preserves contract shell and ensures"
        expectRefinementCallable
    , testIO "SURF-003 callable refinement missing bar rejects at syntax"
        (expectFixtureReject "rejected/01-refinement-missing-bar.phil")
    , test "SURF-008 primitive callable parameters establish exact checked result scope"
        checkedCallableSignaturesPreserveScope
    , test "SURF-008 callable proposition clauses preserve category, order, scope, and Core authority"
        checkedCallablePropositionsPreserveCategories
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectRefinementCallable :: IO (Either String ())
expectRefinementCallable = do
  parsed <- parseFixture "accepted/01-refinement-type.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ claimTop, Located _ callableTop] -> do
        case locatedValue (grammarV1Declaration claimTop) of
          GrammarV1ClaimDeclaration claimDecl -> do
            assert (locatedValue (grammarV1ClaimName claimDecl) == "Positive")
              "claim name was not Positive"
            case grammarV1ClaimProposition claimDecl of
              Just proposition -> assertNameIntegerRelation GrammarV1GreaterRelation "x" "0" proposition
              Nothing -> Left "Positive claim had no proposition"
          other -> Left ("expected claim first, got " <> show other)
        case locatedValue (grammarV1Declaration callableTop) of
          GrammarV1CallableContractDeclaration callableDecl -> do
            assert (locatedValue (grammarV1CallableName callableDecl) == "KeepPositive")
              "callable name was not KeepPositive"
            assert (null (grammarV1CallableGenericParams callableDecl))
              "unexpected callable generic parameters"
            assert (null (grammarV1CallableRequirements callableDecl))
              "unexpected callable generic requirements"
            case grammarV1CallableTermParams callableDecl of
              [Located _ param] -> do
                assert (locatedValue (grammarV1TermParamName param) == "x")
                  "callable parameter name was not x"
                assertRefinementParameter (locatedValue (grammarV1TermParamType param))
              params -> Left ("expected one callable parameter, got " <> show (length params))
            assert (locatedValue (grammarV1CallableResultType callableDecl) == GrammarV1UnsignedType "U32")
              "callable result type was not U32"
            case grammarV1CallableClauses callableDecl of
              [Located _ (GrammarV1CallableEnsures proposition)] ->
                assertNameIntegerRelation GrammarV1GreaterRelation "x" "0" proposition
              clauses -> Left ("expected one ensures clause, got " <> show clauses)
          other -> Left ("expected callable contract second, got " <> show other)
      declarations -> Left ("expected claim and callable declarations, got " <> show (length declarations))

checkedCallableSignaturesPreserveScope :: Either String ()
checkedCallableSignaturesPreserveScope = do
  context <- mapLeft show $
    declareOpaqueClaim
      "NeedsNat"
      [(Name "n", SortNat)]
      emptyStaticContext
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-callable-signatures" signatureSource
  declarations <- mapM callableDeclaration (grammarV1TopLevelDecls sourceFile)
  let x = RefVar (Name "x")
      actual = map
        (grammarV1CheckedCallableSignature context emptySurfaceState)
        declarations
      expected =
        [ Just
            (Right
              ( ( "DependentBytes"
                , [ (Name "x", TyUInt 8)
                  , (Name "ok", TyBool)
                  ]
                , TyBytes (RefToNat x)
                )
              , []
              ))
        , Just
            (Right
              ( ( "CheckedProof"
                , [(Name "x", TyUInt 8)]
                , TyProof (Atom "NeedsNat" [RefToNat x])
                )
              , [InsertedUIntToNat x]
              ))
        , Just (Left (UnknownClaim "Missing"))
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "checked callable signature routing changed name/parameter/result meaning or collapsed competence boundaries: "
      <> show actual

checkedCallablePropositionsPreserveCategories :: Either String ()
checkedCallablePropositionsPreserveCategories = do
  context1 <- mapLeft show $
    declareOpaqueClaim
      "NeedsNat"
      [(Name "n", SortNat)]
      emptyStaticContext
  context2 <- mapLeft show $
    declareOpaqueClaim
      "Flagged"
      [(Name "flag", SortBool)]
      context1
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      context2
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-callable-propositions" propositionSource
  declarations <- mapM callableDeclaration (grammarV1TopLevelDecls sourceFile)
  case declarations of
    [clauses, unknown, specialized, unresolved, duplicate, generic, empty] -> do
      let x = RefVar (Name "x")
          ok = RefVar (Name "ok")
      assert
        (grammarV1CallableRequires context emptySurfaceState clauses
          == Just
              (Right
                [ (Atom "Flagged" [ok], [])
                , (Atom "NeedsNat" [RefToNat x], [InsertedUIntToNat x])
                ]))
        "callable requires lost source order, category, or Core focusing trace"
      assert
        (grammarV1CallableEnsures context emptySurfaceState clauses
          == Just
              (Right
                [ ( LessThan (RefNat 0) (RefToNat x)
                  , [ExpandedTransparentClaim "Positive"]
                  )
                ]))
        "callable ensures did not preserve transparent Core claim semantics"
      assert
        (grammarV1CallableObligations context emptySurfaceState clauses
          == Just
              (Right
                [ (Atom "NeedsNat" [RefToNat x], [InsertedUIntToNat x])
                ]))
        "callable residual obligation was dropped or reclassified"
      assert
        (grammarV1CallableAssumptions context emptySurfaceState clauses
          == Just (Right [(Atom "Flagged" [ok], [])]))
        "callable assumption was dropped or reclassified"
      assert
        (grammarV1CallableEnsures context emptySurfaceState unknown
          == Just (Left (UnknownClaim "Missing")))
        "callable Core rejection collapsed into source non-competence"
      assert
        (grammarV1CallableRequires context emptySurfaceState specialized == Nothing)
        "specialized callable claim reached Core despite structural non-competence"
      assert
        (grammarV1CallableEnsures context emptySurfaceState unresolved == Nothing)
        "unresolved callable proposition argument reached Core"
      assert
        (grammarV1CallableEnsures context emptySurfaceState duplicate == Nothing)
        "duplicate callable parameter scope was silently accepted"
      assert
        (grammarV1CallableRequires context emptySurfaceState generic == Nothing)
        "generic callable entered primitive proposition-clause scope"
      assert
        (grammarV1CallableRequires context emptySurfaceState empty == Just (Right []))
        "absent callable requires did not preserve exact empty category"
      assert
        (grammarV1CallableEnsures context emptySurfaceState empty == Just (Right []))
        "absent callable ensures did not preserve exact empty category"
      assert
        (grammarV1CallableObligations context emptySurfaceState empty == Just (Right []))
        "absent callable obligations did not preserve exact empty category"
      assert
        (grammarV1CallableAssumptions context emptySurfaceState empty == Just (Right []))
        "absent callable assumptions did not preserve exact empty category"
    other -> Left
      ("expected seven callable proposition fixtures, got " <> show (length other))

callableDeclaration
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1CallableContractDecl
callableDeclaration (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1CallableContractDeclaration declaration -> Right declaration
    other -> Left ("expected callable declaration, got " <> show other)

signatureSource :: Text.Text
signatureSource = Text.unlines
  [ "callable DependentBytes(x : U8, ok : Bool) -> Bytes[toNat(x)] {}"
  , "callable CheckedProof(x : U8) -> Proof[NeedsNat(x)] {}"
  , "callable UnknownClaim(x : U8) -> Proof[Missing(x)] {}"
  , "callable Duplicate(x : U8, x : Bool) -> Bool {}"
  , "callable Generic[T : Type](x : U8) -> U8 {}"
  , "callable RefinedParam(x : {v : U8 | v > 0}) -> U8 {}"
  , "callable TupleResult(x : U8) -> (U8, Bool) {}"
  ]

propositionSource :: Text.Text
propositionSource = Text.unlines
  [ "callable Clauses(x : U8, ok : Bool) -> U8 { requires Flagged(ok); requires NeedsNat(x); ensures Positive(x); obligation NeedsNat(x); assumes Flagged(ok); }"
  , "callable Unknown(x : U8) -> U8 { ensures Missing(x); }"
  , "callable Specialized(x : U8, ok : Bool) -> U8 { requires Flagged[U8](ok); }"
  , "callable Unresolved(x : U8) -> U8 { ensures Positive(missing); }"
  , "callable Duplicate(x : U8, x : Bool) -> U8 { ensures true; }"
  , "callable Generic[T : Type](x : U8) -> U8 { requires true; }"
  , "callable Empty(x : U8) -> U8 {}"
  ]

assertRefinementParameter :: GrammarV1Type -> Either String ()
assertRefinementParameter ty = case ty of
  GrammarV1RefinementType binder baseType predicate -> do
    assert (locatedValue binder == "v") "refinement binder was not v"
    assert (locatedValue baseType == GrammarV1UnsignedType "U32")
      "refinement base type was not U32"
    assertNameIntegerRelation GrammarV1GreaterRelation "v" "0" predicate
  other -> Left ("expected refinement parameter type, got " <> show other)

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
