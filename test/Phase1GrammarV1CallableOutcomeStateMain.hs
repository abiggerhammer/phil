{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , StaticContext
  , declareOpaqueClaim
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
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.CallableOutcomePropositions
  ( grammarV1CallableOutcomeEnsures
  , grammarV1CallableOutcomeObligations
  )
import Phil.Surface.GrammarV1.CallableOutcomeState
  ( grammarV1CallableOutcomeStateTelescopes
  )
import Phil.Surface.GrammarV1.GenericTermScope
  ( GrammarV1GenericTermScopeError (..)
  , grammarV1CheckedCallableGenericTermScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticCallableOutcomePropositions
  ( GrammarV1SemanticCallableOutcomePropositionError (..)
  , grammarV1CheckedSemanticCallableOutcomeEnsures
  , grammarV1CheckedSemanticCallableOutcomeObligations
  )
import Phil.Surface.GrammarV1.SemanticCallableOutcomeState
  ( GrammarV1SemanticCallableOutcomeResidueScope (..)
  , GrammarV1SemanticCallableOutcomeStateError (..)
  , GrammarV1SemanticCallableOutcomeStateScope (..)
  , grammarV1SemanticCallableOutcomeScopes
  )
import Phil.Surface.GrammarV1.SemanticCallablePropositions
  ( GrammarV1CheckedSemanticCallableProposition (..)
  )
import Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1SemanticCallableScope (..)
  , grammarV1SemanticCallableParameterScope
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 callable outcome state preserves branch and telescope structure"
        primitiveOutcomeStateTelescopes
    , test "SURF-008 repeated outcome state clauses remain distinct"
        repeatedStateClausesRemainDistinct
    , test "SURF-008 duplicate outcome state slots fail closed"
        duplicateStateSlotsReject
    , test "SURF-008 nonprimitive outcome state slots remain outside competence"
        nonprimitiveStateSlotsReject
    , test "SURF-008 generic callable outcome state remains outside primitive scope"
        genericCallableStateRejects
    , test "SURF-008 callable without outcome residues has exact empty projection"
        absentOutcomeResiduesAreEmpty
    , test "SURF-008 outcome propositions use exact parameter plus branch-state scope"
        checkedOutcomePropositionsUseBranchScope
    , test "SURF-008 outcome propositions reject unresolved branch-state names structurally"
        missingOutcomeStateBindingRejects
    , test "SURF-008 repeated outcome state is ambiguous for proposition scope"
        repeatedOutcomeStateScopeRejects
    , test "SURF-008 outcome proposition Core failures remain distinct"
        outcomePropositionCoreFailurePreserved
    , test "SURF-009 outcome state slots use generated sibling-unique identities"
        semanticOutcomeStateUsesGeneratedSiblingIdentities
    , test "SURF-009 outcome propositions use exact parameter and branch-state binders"
        semanticOutcomePropositionsUseExactBranchIdentity
    , test "SURF-009 outcome state and propositions are alpha-stable"
        semanticOutcomeAlphaStable
    , test "SURF-009 repeated outcome state ambiguity remains explicit"
        semanticRepeatedOutcomeStateAmbiguityExplicit
    , test "SURF-009 duplicate outcome state binders remain explicit"
        semanticDuplicateOutcomeStateBinderExplicit
    , test "SURF-009 outcome state competence remains bounded"
        semanticOutcomeStateCompetenceBoundary
    , test "SURF-009 outcome state slots cannot shadow callable generics"
        callableOutcomeStateCannotShadowGeneric
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

primitiveOutcomeStateTelescopes :: Either String ()
primitiveOutcomeStateTelescopes = do
  callable <- onlyCallable $ Text.unlines
    [ "callable Run(x : U32) -> Unit {"
    , "  outcomes { success Done, negative Retry, terminal Closed, fatal Crashed };"
    , "  outcome success Done { state (x_next : U32); }"
    , "  outcome negative Retry { state (retry : U8, flag : Bool); }"
    , "  outcome terminal Closed { state (); }"
    , "  outcome fatal Crashed {}"
    , "}"
    ]
  assert
    ( grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable ==
        Just
          [ (GrammarV1SuccessOutcome, [[(Name "x_next", TyUInt 32)]])
          , ( GrammarV1NegativeOutcome
            , [[(Name "retry", TyUInt 8), (Name "flag", TyBool)]]
            )
          , (GrammarV1TerminalOutcome, [[]])
          , (GrammarV1FatalOutcome, [])
          ]
    )
    "outcome kind, slot order/type, empty state, or absent-state distinction changed"

repeatedStateClausesRemainDistinct :: Either String ()
repeatedStateClausesRemainDistinct = do
  callable <- onlyCallable $ Text.unlines
    [ "callable RepeatedState() -> Unit {"
    , "  outcome success Done {"
    , "    state (a : U8);"
    , "    state (b : Bool);"
    , "  }"
    , "}"
    ]
  assert
    ( grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable ==
        Just
          [ ( GrammarV1SuccessOutcome
            , [[(Name "a", TyUInt 8)], [(Name "b", TyBool)]]
            )
          ]
    )
    "repeated state clauses were merged, reordered, or dropped"

duplicateStateSlotsReject :: Either String ()
duplicateStateSlotsReject = do
  callable <- onlyCallable
    "callable DuplicateState() -> Unit { outcome success Done { state (x : U8, x : Bool); } }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Nothing)
    "duplicate state-slot names escaped the ordinary binding authority"

nonprimitiveStateSlotsReject :: Either String ()
nonprimitiveStateSlotsReject = do
  callable <- onlyCallable
    "callable NamedState() -> Unit { outcome success Done { state (blob : Blob); } }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Nothing)
    "named state type acquired an invented unrestricted structural mode"

genericCallableStateRejects :: Either String ()
genericCallableStateRejects = do
  callable <- onlyCallable
    "callable GenericState[T : Type]() -> Unit { outcome success Done { state (x : U8); } }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Nothing)
    "generic callable bypassed the shared primitive parameter-scope competence wall"

absentOutcomeResiduesAreEmpty :: Either String ()
absentOutcomeResiduesAreEmpty = do
  callable <- onlyCallable
    "callable NoResidues() -> Unit { outcomes { success Done }; }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Just [])
    "callable without outcome residues did not preserve exact absence"
  context <- checkedContext
  assert
    (grammarV1CallableOutcomeEnsures context emptySurfaceState callable == Just (Right []))
    "outcome ensures projection did not preserve exact absence"
  assert
    (grammarV1CallableOutcomeObligations context emptySurfaceState callable == Just (Right []))
    "outcome obligation projection did not preserve exact absence"

checkedOutcomePropositionsUseBranchScope :: Either String ()
checkedOutcomePropositionsUseBranchScope = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable CheckedOutcome(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (s : U8);"
    , "    ensures PairOk(x, s);"
    , "    obligation PairOk(x, s);"
    , "    ensures ParamOk(x);"
    , "  }"
    , "  outcome negative Retry {"
    , "    ensures ParamOk(x);"
    , "  }"
    , "}"
    ]
  case
      ( grammarV1CallableOutcomeEnsures context emptySurfaceState callable
      , grammarV1CallableOutcomeObligations context emptySurfaceState callable
      ) of
    (Just (Right ensured), Just (Right obligations)) -> do
      let x = RefVar (Name "x")
          s = RefVar (Name "s")
          pair = Atom "PairOk" [x, s]
          parameterOnly = Atom "ParamOk" [x]
      assert
        (stripSteps ensured ==
          [ (GrammarV1SuccessOutcome, [pair, parameterOnly])
          , (GrammarV1NegativeOutcome, [parameterOnly])
          ])
        ("outcome ensures lost branch scope/category/order: " <> show ensured)
      assert
        (stripSteps obligations ==
          [ (GrammarV1SuccessOutcome, [pair])
          , (GrammarV1NegativeOutcome, [])
          ])
        ("outcome obligations were reclassified or lost branch scope: " <> show obligations)
    other -> Left
      ("checked outcome propositions did not preserve branch scope/categories: " <> show other)

missingOutcomeStateBindingRejects :: Either String ()
missingOutcomeStateBindingRejects = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable MissingState(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    ensures PairOk(x, s);"
    , "  }"
    , "}"
    ]
  assert
    (grammarV1CallableOutcomeEnsures context emptySurfaceState callable == Nothing)
    "unbound branch-state name reached Core focusing or acquired an ambient meaning"

repeatedOutcomeStateScopeRejects :: Either String ()
repeatedOutcomeStateScopeRejects = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable AmbiguousState(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (a : U8);"
    , "    state (b : U8);"
    , "    ensures ParamOk(x);"
    , "  }"
    , "}"
    ]
  assert
    (grammarV1CallableOutcomeEnsures context emptySurfaceState callable == Nothing)
    "checked proposition routing arbitrarily selected one of several state scopes"

outcomePropositionCoreFailurePreserved :: Either String ()
outcomePropositionCoreFailurePreserved = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable CoreReject(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (s : U8);"
    , "    ensures Missing(x);"
    , "  }"
    , "}"
    ]
  case grammarV1CallableOutcomeEnsures context emptySurfaceState callable of
    Just (Left (UnknownClaim "Missing")) -> Right ()
    other -> Left ("Core UnknownClaim was collapsed or changed: " <> show other)

semanticOutcomeStateUsesGeneratedSiblingIdentities :: Either String ()
semanticOutcomeStateUsesGeneratedSiblingIdentities = do
  callable <- semanticSiblingCallable
  let declarationKey = DeclarationKey "decl.SemanticCallableOutcomes"
  residueScopes <- checkedSemanticOutcomeScopes declarationKey callable
  case residueScopes of
    [successResidue, retryResidue] -> do
      (successBinder, successState) <- singleOutcomeBinder "success" successResidue
      (retryBinder, retryState) <- singleOutcomeBinder "retry" retryResidue
      let successName@(Name successText) = grammarV1ResolvedBinderCoreName successBinder
          retryName@(Name retryText) = grammarV1ResolvedBinderCoreName retryBinder
      assert
        (grammarV1ResolvedBinderKind successBinder
          == GrammarV1CallableOutcomeStateBinder)
        "success outcome slot lost its binder family"
      assert
        (grammarV1ResolvedBinderKind retryBinder
          == GrammarV1CallableOutcomeStateBinder)
        "retry outcome slot lost its binder family"
      assert (successText /= "s" && retryText /= "s")
        "outcome state semantic identity collapsed to source spelling"
      assert (successName /= retryName)
        "sibling outcome state slots reused one generated Core name"
      assert
        (grammarV1ResolvedBinderKey successBinder
          /= grammarV1ResolvedBinderKey retryBinder)
        "sibling outcome state slots reused one BinderKey"
      assert
        (Map.member successText (stateBindings successState)
          && not (Map.member "s" (stateBindings successState)))
        "success outcome SurfaceState did not use generated slot identity"
      assert
        (Map.member retryText (stateBindings retryState)
          && not (Map.member "s" (stateBindings retryState)))
        "retry outcome SurfaceState did not use generated slot identity"
    other -> Left
      ("expected success/retry semantic outcome scopes, got " <> show (length other))

semanticOutcomePropositionsUseExactBranchIdentity :: Either String ()
semanticOutcomePropositionsUseExactBranchIdentity = do
  context <- checkedContext
  callable <- semanticSiblingCallable
  let declarationKey = DeclarationKey "decl.SemanticCallableOutcomeProps"
  callableScope <- checkedCallableScope declarationKey callable
  xBinder <- exactlyOne
    "semantic callable parameter"
    (map fst (semanticCallableScopeParameters callableScope))
  residueScopes <- checkedSemanticOutcomeScopes declarationKey callable
  case residueScopes of
    [successResidue, retryResidue] -> do
      (successBinder, _) <- singleOutcomeBinder "success" successResidue
      (retryBinder, _) <- singleOutcomeBinder "retry" retryResidue
      ensured <- checkedSemanticOutcomeEnsures context declarationKey callable
      obligations <- checkedSemanticOutcomeObligations context declarationKey callable
      let xName = grammarV1ResolvedBinderCoreName xBinder
          successName = grammarV1ResolvedBinderCoreName successBinder
          retryName = grammarV1ResolvedBinderCoreName retryBinder
          successPair = Atom "PairOk" [RefVar xName, RefVar successName]
          retryPair = Atom "PairOk" [RefVar xName, RefVar retryName]
      case ensured of
        [ (GrammarV1SuccessOutcome, [successChecked])
          , (GrammarV1NegativeOutcome, [retryChecked])
          ] -> do
            assert
              (checkedSemanticCallablePropositionCore successChecked == successPair)
              "success outcome proposition lost exact semantic slot identity"
            assert
              (checkedSemanticCallablePropositionCore retryChecked == retryPair)
              "retry outcome proposition lost exact semantic slot identity"
            assertReferenceKeys
              "success outcome references"
              [grammarV1ResolvedBinderKey xBinder, grammarV1ResolvedBinderKey successBinder]
              successChecked
            assertReferenceKeys
              "retry outcome references"
              [grammarV1ResolvedBinderKey xBinder, grammarV1ResolvedBinderKey retryBinder]
              retryChecked
        other -> Left ("unexpected semantic ensures shape: " <> show other)
      case obligations of
        [ (GrammarV1SuccessOutcome, [successChecked])
          , (GrammarV1NegativeOutcome, [])
          ] -> assert
            (checkedSemanticCallablePropositionCore successChecked == successPair)
            "semantic outcome obligation lost exact branch identity"
        other -> Left ("unexpected semantic obligation shape: " <> show other)
    other -> Left
      ("expected two semantic outcome residues, got " <> show (length other))

semanticOutcomeAlphaStable :: Either String ()
semanticOutcomeAlphaStable = do
  original <- onlyCallable $ Text.unlines
    [ "callable Alpha(x : U32) -> Unit {"
    , "  outcome success Done { state (s : U8); ensures PairOk(x, s); }"
    , "}"
    ]
  renamed <- onlyCallable $ Text.unlines
    [ "callable Alpha(count : U32) -> Unit {"
    , "  outcome success Done { state (slot : U8); ensures PairOk(count, slot); }"
    , "}"
    ]
  context <- checkedContext
  let declarationKey = DeclarationKey "decl.SemanticCallableOutcomeAlpha"
  originalScope <- checkedCallableScope declarationKey original
  renamedScope <- checkedCallableScope declarationKey renamed
  originalParam <- exactlyOne "original alpha parameter"
    (map fst (semanticCallableScopeParameters originalScope))
  renamedParam <- exactlyOne "renamed alpha parameter"
    (map fst (semanticCallableScopeParameters renamedScope))
  originalResidue <- exactlyOne "original alpha residue"
    =<< checkedSemanticOutcomeScopes declarationKey original
  renamedResidue <- exactlyOne "renamed alpha residue"
    =<< checkedSemanticOutcomeScopes declarationKey renamed
  (originalStateBinder, _) <- singleOutcomeBinder "original alpha" originalResidue
  (renamedStateBinder, _) <- singleOutcomeBinder "renamed alpha" renamedResidue
  originalEnsures <- checkedSemanticOutcomeEnsures context declarationKey original
  renamedEnsures <- checkedSemanticOutcomeEnsures context declarationKey renamed
  originalChecked <- exactlyOne "original alpha ensures"
    =<< exactlyOneCategory originalEnsures
  renamedChecked <- exactlyOne "renamed alpha ensures"
    =<< exactlyOneCategory renamedEnsures
  assert
    (grammarV1ResolvedBinderKey originalParam
      == grammarV1ResolvedBinderKey renamedParam)
    "alpha-renaming changed callable parameter identity"
  assert
    (grammarV1ResolvedBinderKey originalStateBinder
      == grammarV1ResolvedBinderKey renamedStateBinder)
    "alpha-renaming changed outcome-state BinderKey"
  assert
    (grammarV1ResolvedBinderCoreName originalStateBinder
      == grammarV1ResolvedBinderCoreName renamedStateBinder)
    "alpha-renaming changed outcome-state Core name"
  assert
    (checkedSemanticCallablePropositionCore originalChecked
      == checkedSemanticCallablePropositionCore renamedChecked)
    "alpha-renaming changed semantic outcome proposition Core meaning"

semanticRepeatedOutcomeStateAmbiguityExplicit :: Either String ()
semanticRepeatedOutcomeStateAmbiguityExplicit = do
  callable <- onlyCallable $ Text.unlines
    [ "callable Ambiguous(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (a : U8);"
    , "    state (b : U8);"
    , "    ensures ParamOk(x);"
    , "  }"
    , "}"
    ]
  let actual = grammarV1CheckedSemanticCallableOutcomeEnsures
        emptyStaticContext
        (DeclarationKey "decl.SemanticOutcomeAmbiguous")
        callable
  case actual of
    Just (Left (GrammarV1SemanticCallableOutcomeAmbiguousStateScope _)) -> Right ()
    other -> Left
      ("semantic outcome state ambiguity was collapsed or guessed: " <> show other)

semanticDuplicateOutcomeStateBinderExplicit :: Either String ()
semanticDuplicateOutcomeStateBinderExplicit = do
  callable <- onlyCallable
    "callable Duplicate() -> Unit { outcome success Done { state (s : U8, s : Bool); } }"
  let actual = grammarV1SemanticCallableOutcomeScopes
        (DeclarationKey "decl.SemanticOutcomeDuplicate")
        callable
  case actual of
    Just (Left (GrammarV1SemanticCallableOutcomeBinderScopeError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "s")
          "duplicate outcome-state diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "s")
          "duplicate outcome-state diagnostic lost previous binder"
    other -> Left
      ("expected explicit semantic outcome duplicate rejection, got " <> show other)

semanticOutcomeStateCompetenceBoundary :: Either String ()
semanticOutcomeStateCompetenceBoundary = do
  callable <- onlyCallable
    "callable Named() -> Unit { outcome success Done { state (blob : Blob); } }"
  assert
    ( grammarV1SemanticCallableOutcomeScopes
        (DeclarationKey "decl.SemanticOutcomeBoundary")
        callable
        == Nothing
    )
    "nonprimitive outcome state escaped semantic competence boundary"

callableOutcomeStateCannotShadowGeneric :: Either String ()
callableOutcomeStateCannotShadowGeneric = do
  callable <- onlyCallable
    "callable GenericCollision[s : Nat](x : U8) -> Unit { outcome success Done { state (s : U8); } }"
  case grammarV1CheckedCallableGenericTermScope
      (DeclarationKey "decl.SemanticOutcomeGenericShadow")
      callable of
    Left (GrammarV1GenericTermActiveStaticShadowing sourceName _) ->
      assert (locatedValue sourceName == "s")
        "generic/outcome-state shadow diagnostic lost slot spelling"
    other -> Left
      ("outcome state slot did not reject active generic shadowing: " <> show other)

semanticSiblingCallable :: Either String GrammarV1CallableContractDecl
semanticSiblingCallable = onlyCallable $ Text.unlines
  [ "callable Branches(x : U32) -> Unit {"
  , "  outcome success Done {"
  , "    state (s : U8);"
  , "    ensures PairOk(x, s);"
  , "    obligation PairOk(x, s);"
  , "  }"
  , "  outcome negative Retry {"
  , "    state (s : U8);"
  , "    ensures PairOk(x, s);"
  , "  }"
  , "}"
  ]

singleOutcomeBinder
  :: String
  -> GrammarV1SemanticCallableOutcomeResidueScope
  -> Either String (GrammarV1ResolvedBinder, SurfaceState)
singleOutcomeBinder label residue = do
  stateScope <- exactlyOne
    (label <> " state scope")
    (semanticCallableOutcomeResidueStateScopes residue)
  case semanticCallableOutcomeStateBindings stateScope of
    [(binder, TyUInt 8)] ->
      Right (binder, semanticCallableOutcomeStateSurfaceState stateScope)
    other -> Left
      ("unexpected " <> label <> " semantic state binding shape: " <> show other)

checkedCallableScope
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String GrammarV1SemanticCallableScope
checkedCallableScope declarationKey callable =
  case grammarV1SemanticCallableParameterScope declarationKey callable of
    Just (Right scope) -> Right scope
    other -> Left ("expected semantic callable parameter scope, got " <> show other)

checkedSemanticOutcomeScopes
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String [GrammarV1SemanticCallableOutcomeResidueScope]
checkedSemanticOutcomeScopes declarationKey callable =
  case grammarV1SemanticCallableOutcomeScopes declarationKey callable of
    Just (Right scopes) -> Right scopes
    other -> Left ("expected semantic callable outcome scopes, got " <> show other)

checkedSemanticOutcomeEnsures
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String
      [(GrammarV1OutcomeKind, [GrammarV1CheckedSemanticCallableProposition])]
checkedSemanticOutcomeEnsures context declarationKey callable =
  case grammarV1CheckedSemanticCallableOutcomeEnsures context declarationKey callable of
    Just (Right checked) -> Right checked
    other -> Left ("expected semantic callable outcome ensures, got " <> show other)

checkedSemanticOutcomeObligations
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String
      [(GrammarV1OutcomeKind, [GrammarV1CheckedSemanticCallableProposition])]
checkedSemanticOutcomeObligations context declarationKey callable =
  case grammarV1CheckedSemanticCallableOutcomeObligations context declarationKey callable of
    Just (Right checked) -> Right checked
    other -> Left ("expected semantic callable outcome obligations, got " <> show other)

exactlyOneCategory
  :: [(GrammarV1OutcomeKind, [a])]
  -> Either String [a]
exactlyOneCategory [(_, values)] = Right values
exactlyOneCategory other = Left
  ("expected exactly one semantic outcome category, got " <> show (length other))

assertReferenceKeys
  :: String
  -> [Phil.Surface.GrammarV1.BinderScope.GrammarV1BinderKey]
  -> GrammarV1CheckedSemanticCallableProposition
  -> Either String ()
assertReferenceKeys label expected checked =
  let actual = map
        ( grammarV1ResolvedBinderKey
        . grammarV1CheckedLexicalReferenceBinder
        )
        (checkedSemanticCallablePropositionReferences checked)
  in assert (actual == expected)
      (label <> " changed exact binder evidence: " <> show actual)

checkedContext :: Either String StaticContext
checkedContext = do
  context1 <- mapLeft show $
    declareOpaqueClaim
      "PairOk"
      [(Name "x", SortUInt 32), (Name "s", SortUInt 8)]
      emptyStaticContext
  mapLeft show $
    declareOpaqueClaim "ParamOk" [(Name "x", SortUInt 32)] context1

stripSteps
  :: [(GrammarV1OutcomeKind, [(Proposition, steps)])]
  -> [(GrammarV1OutcomeKind, [Proposition])]
stripSteps = map (\(kind, propositions) -> (kind, map fst propositions))

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "callable-outcome-state" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableContractDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left
  ("expected exactly one " <> label <> ", got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
