{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , declareOpaqueClaim
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
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.CallablePropositions
  ( grammarV1CallableAssumptions
  , grammarV1CallableEnsures
  , grammarV1CallableObligations
  , grammarV1CallableRequires
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1CheckedCallableSignature
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticCallableOutcomePropositions
  ( grammarV1CheckedSemanticCallableOutcomeEnsuresAfterResult
  )
import Phil.Surface.GrammarV1.SemanticCallableOutcomeState
  ( GrammarV1SemanticCallableOutcomeResidueScope (..)
  , GrammarV1SemanticCallableOutcomeStateScope (..)
  , grammarV1SemanticCallableOutcomeScopesAfterResult
  )
import Phil.Surface.GrammarV1.SemanticCallablePropositions
  ( GrammarV1CheckedSemanticCallableProposition (..)
  )
import Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1CheckedSemanticCallableSignature (..)
  , GrammarV1SemanticCallableSignatureError (..)
  , grammarV1CheckedSemanticCallableSignature
  )
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
    , test "SURF-009 semantic callable signatures use generated parameter state"
        semanticCallableUsesGeneratedNames
    , test "SURF-009 semantic callable signatures are alpha-stable for dependent results"
        semanticCallableAlphaStable
    , test "SURF-009 callable result refinements compose before outcome-state binders"
        semanticCallableResultRefinementComposesWithOutcomes
    , test "SURF-009 semantic callable signatures preserve duplicate-binder diagnostics"
        semanticCallableDuplicatePreserved
    , test "SURF-009 semantic callable signatures preserve Core focusing errors"
        semanticCallableFocusingPreserved
    , test "SURF-009 semantic callable signatures remain bounded to primitive parameters"
        semanticCallableCompetenceBoundary
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

semanticCallableUsesGeneratedNames :: Either String ()
semanticCallableUsesGeneratedNames = do
  source <- onlyCallable "semantic-callable" $ Text.unlines
    [ "callable Dependent(n : U8, ok : Bool) -> Bytes[toNat(n)] {}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticCallable"
  checked <- checkedSemanticCallable declarationKey source
  case checkedSemanticCallableParameters checked of
    [(nBinder, TyUInt 8), (okBinder, TyBool)] -> do
      let nName@(Name nText) = grammarV1ResolvedBinderCoreName nBinder
          okName@(Name okText) = grammarV1ResolvedBinderCoreName okBinder
          state = checkedSemanticCallableState checked
          context = resourceContext (stateCore state)
      assert
        ( grammarV1ResolvedBinderKind nBinder == GrammarV1CallableParameterBinder
          && grammarV1ResolvedBinderKind okBinder == GrammarV1CallableParameterBinder )
        "callable parameters did not retain their distinct binder family"
      assert (nText /= "n" && okText /= "ok")
        "semantic callable parameter names collapsed to source spelling"
      assert
        (Map.member nText (stateBindings state) && Map.member okText (stateBindings state))
        "semantic callable SurfaceState omitted generated parameter names"
      assert
        (not (Map.member "n" (stateBindings state)) && not (Map.member "ok" (stateBindings state)))
        "source callable parameter spelling leaked into semantic SurfaceState"
      assert
        (Map.member nName (unrestrictedBindings context) && Map.member okName (unrestrictedBindings context))
        "Core resource context omitted generated callable parameter names"
      assert
        (checkedSemanticCallableResultType checked
          == TyBytes (RefToNat (RefVar nName)))
        "dependent callable result did not retain generated n identity"
      reference <- exactlyOne
        "semantic callable result reference"
        (checkedSemanticCallableResultReferences checked)
      assert
        ( grammarV1ResolvedBinderKey
            (grammarV1CheckedLexicalReferenceBinder reference)
          == grammarV1ResolvedBinderKey nBinder )
        "dependent callable result reference lost exact binder evidence"
    other -> Left ("unexpected semantic callable parameter shape: " <> show other)

semanticCallableAlphaStable :: Either String ()
semanticCallableAlphaStable = do
  original <- onlyCallable "semantic-callable-alpha-original"
    "callable Dependent(n : U8, ok : Bool) -> Bytes[toNat(n)] {}"
  renamed <- onlyCallable "semantic-callable-alpha-renamed"
    "callable Dependent(count : U8, ready : Bool) -> Bytes[toNat(count)] {}"
  let declarationKey = DeclarationKey "decl.SemanticCallableAlpha"
  originalChecked <- checkedSemanticCallable declarationKey original
  renamedChecked <- checkedSemanticCallable declarationKey renamed
  let originalBinders = map fst (checkedSemanticCallableParameters originalChecked)
      renamedBinders = map fst (checkedSemanticCallableParameters renamedChecked)
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming changed semantic callable binder keys"
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming changed semantic callable Core names"
  assert
    (checkedSemanticCallableResultType originalChecked
      == checkedSemanticCallableResultType renamedChecked)
    "alpha-renaming changed dependent semantic callable result type"
  assert
    (map grammarV1ResolvedBinderDisplayName originalBinders == ["n", "ok"])
    "original callable display spellings changed"
  assert
    (map grammarV1ResolvedBinderDisplayName renamedBinders == ["count", "ready"])
    "renamed callable display spellings changed"

semanticCallableResultRefinementComposesWithOutcomes :: Either String ()
semanticCallableResultRefinementComposesWithOutcomes = do
  source <- onlyCallable "semantic-callable-composition" $ Text.unlines
    [ "callable RefinedOutcome(x : U8) -> {v : U8 | v <= x} {"
    , "  outcome success Done {"
    , "    state (s : U8);"
    , "    ensures PairOk(x, s);"
    , "  }"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticCallableComposition"
  signature <- checkedSemanticCallable declarationKey source
  xBinder <- exactlyOne
    "semantic callable composition parameter"
    (map fst (checkedSemanticCallableParameters signature))
  vBinder <- maybe
    (Left "callable result refinement lost semantic binder evidence")
    Right
    (checkedSemanticCallableResultRefinementBinder signature)
  let xName = grammarV1ResolvedBinderCoreName xBinder
      vName = grammarV1ResolvedBinderCoreName vBinder
  assert
    ( grammarV1BinderOrdinal (grammarV1ResolvedBinderKey xBinder) == 0
      && grammarV1BinderOrdinal (grammarV1ResolvedBinderKey vBinder) == 1 )
    "callable parameter/result-refinement ordinal order changed"
  assert
    ( checkedSemanticCallableResultType signature
        == TyRefined
          vName
          (TyUInt 8)
          (LessEqual (RefVar vName) (RefVar xName)) )
    "callable result refinement lost exact semantic parameter/binder identity"
  residueScopes <- case grammarV1SemanticCallableOutcomeScopesAfterResult
      emptyStaticContext declarationKey source of
    Just (Right scopes) -> Right scopes
    other -> Left ("expected composed callable outcome scopes, got " <> show other)
  residue <- exactlyOne "composed callable outcome residue" residueScopes
  stateScope <- exactlyOne
    "composed callable outcome state scope"
    (semanticCallableOutcomeResidueStateScopes residue)
  (sBinder, TyUInt 8) <- exactlyOne
    "composed callable outcome state binding"
    (semanticCallableOutcomeStateBindings stateScope)
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey sBinder) == 2)
    "callable outcome state reused the closed result-refinement ordinal"
  context <- mapLeft show $
    declareOpaqueClaim
      "PairOk"
      [(Name "x", SortUInt 8), (Name "s", SortUInt 8)]
      emptyStaticContext
  ensured <- case grammarV1CheckedSemanticCallableOutcomeEnsuresAfterResult
      context declarationKey source of
    Just (Right checked) -> Right checked
    other -> Left ("expected composed callable outcome ensures, got " <> show other)
  checked <- case ensured of
    [(GrammarV1SuccessOutcome, [value])] -> Right value
    other -> Left ("unexpected composed callable ensures shape: " <> show other)
  let sName = grammarV1ResolvedBinderCoreName sBinder
  assert
    (checkedSemanticCallablePropositionCore checked
      == Atom "PairOk" [RefVar xName, RefVar sName])
    "composed callable outcome proposition lost semantic parameter/state names"
  assert
    ( map
        (grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder)
        (checkedSemanticCallablePropositionReferences checked)
        == [grammarV1ResolvedBinderKey xBinder, grammarV1ResolvedBinderKey sBinder] )
    "composed callable outcome proposition lost exact binder reference evidence"

semanticCallableDuplicatePreserved :: Either String ()
semanticCallableDuplicatePreserved = do
  source <- onlyCallable "semantic-callable-duplicate"
    "callable Duplicate(x : U8, x : Bool) -> U8 {}"
  case grammarV1CheckedSemanticCallableSignature
      emptyStaticContext
      (DeclarationKey "decl.SemanticCallableDuplicate")
      source of
    Just (Left (GrammarV1SemanticCallableBinderScopeError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "x")
          "semantic callable duplicate diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "x")
          "semantic callable duplicate diagnostic lost previous binder"
    other -> Left
      ("expected semantic callable duplicate-binder rejection, got " <> show other)

semanticCallableFocusingPreserved :: Either String ()
semanticCallableFocusingPreserved = do
  source <- onlyCallable "semantic-callable-focusing"
    "callable Bad(x : U8) -> Proof[Missing(x)] {}"
  let actual = grammarV1CheckedSemanticCallableSignature
        emptyStaticContext
        (DeclarationKey "decl.SemanticCallableFocusing")
        source
  assert
    (actual == Just
      (Left
        (GrammarV1SemanticCallableResultFocusingError
          (UnknownClaim "Missing"))))
    ("semantic callable changed Core UnknownClaim rejection: " <> show actual)

semanticCallableCompetenceBoundary :: Either String ()
semanticCallableCompetenceBoundary = do
  named <- onlyCallable "semantic-callable-named"
    "callable Named(x : Other) -> U8 {}"
  generic <- onlyCallable "semantic-callable-generic"
    "callable Generic[T : Type](x : U8) -> U8 {}"
  let check source = grammarV1CheckedSemanticCallableSignature
        emptyStaticContext
        (DeclarationKey "decl.SemanticCallableBoundary")
        source
  assert (check named == Nothing)
    "nonprimitive callable parameter escaped semantic-signature competence"
  assert (check generic == Nothing)
    "generic callable escaped semantic-signature competence"

checkedSemanticCallable
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String GrammarV1CheckedSemanticCallableSignature
checkedSemanticCallable declarationKey source =
  case grammarV1CheckedSemanticCallableSignature
      emptyStaticContext declarationKey source of
    Just (Right (checked, [])) -> Right checked
    other -> Left ("expected checked semantic callable signature, got " <> show other)

callableDeclaration
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1CallableContractDecl
callableDeclaration (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1CallableContractDeclaration declaration -> Right declaration
    other -> Left ("expected callable declaration, got " <> show other)

onlyCallable
  :: Text.Text
  -> Text.Text
  -> Either String GrammarV1CallableContractDecl
onlyCallable label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [declaration] -> callableDeclaration declaration
    declarations -> Left
      ("expected one callable declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left
  ("expected exactly one " <> label <> ", got " <> show (length values))

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
