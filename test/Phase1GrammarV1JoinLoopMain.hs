{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.CaseArmScope
  ( GrammarV1CheckedCaseArm (..)
  , GrammarV1CheckedCaseExpression (..)
  )
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedIfBranch (..)
  , GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedJoinExpression (..)
  , GrammarV1CheckedJoinReference (..)
  , GrammarV1CheckedJoinSlot (..)
  , GrammarV1JoinStateScopeError (..)
  , grammarV1CheckedJoinExpressionInScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  , GrammarV1LexicalReferenceError (..)
  )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopBodyStep (..)
  , GrammarV1CheckedLoopSlot (..)
  , GrammarV1CheckedLoopState (..)
  , GrammarV1LoopStateScopeError (..)
  , grammarV1CheckedLoopExpressionInScope
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 join invariant fixture preserves typed join state and invariant"
        expectJoinInvariant
    , testIO "SURF-002 typed loop state fixture preserves initializer invariant and continue"
        expectTypedLoopState
    , testIO "SURF-003 join invariant missing proposition rejects at syntax"
        (expectFixtureReject "rejected/18-join-invariant-missing-proposition.phil")
    , testIO "SURF-003 typed loop state missing initializer rejects at syntax"
        (expectFixtureReject "rejected/19-loop-typed-state-missing-initializer.phil")
    , test "SURF-002 untyped loop state and zero-actual continue are preserved"
        untypedLoopAndZeroContinuePreserved
    , test "SURF-003 loop state bindings reject trailing comma"
        loopStateTrailingCommaRejects
    , test "SURF-009 match join binders are post-arm occurrences with fresh identity"
        matchJoinBindersArePostArm
    , test "SURF-009 join binders cannot shadow an active enclosing parameter"
        joinBinderCannotShadowParameter
    , test "SURF-009 later join slots and invariant resolve earlier post-state binders"
        dependentJoinSlotsResolveEarlierBinders
    , test "SURF-009 join state rejects forward references in the state telescope"
        joinStateForwardReferenceRejects
    , test "SURF-009 if predecessor locals are sibling-scoped before post-join binding"
        ifJoinPredecessorScopesAreDisjoint
    , test "SURF-009 omitted else contributes no invented lexical bindings"
        omittedElseAddsNoBindings
    , test "SURF-009 join-state names are not visible inside predecessor arms"
        joinBinderNotVisibleInArm
    , test "SURF-009 join-state alpha renaming preserves semantic identity"
        joinAlphaRenamingPreservesIdentity
    , test "SURF-009 loop initializers use entry scope and header state drives continue"
        loopInitializersUseEntryScope
    , test "SURF-009 later loop-state types may depend on earlier header binders"
        dependentLoopStateResolvesEarlierHeader
    , test "SURF-009 loop-state initializers cannot see future header binders"
        loopInitializerCannotSeeHeaderBinder
    , test "SURF-009 loop-state types reject forward header references"
        loopTypeForwardReferenceRejects
    , test "SURF-009 loop-state binders cannot shadow enclosing parameters"
        loopStateCannotShadowParameter
    , test "SURF-009 duplicate loop-state binders reject"
        duplicateLoopStateRejects
    , test "SURF-009 loop body lets and break actuals stay inside loop scope"
        loopBodyLetBreakScopeCloses
    , test "SURF-009 zero-actual continue never implicitly captures loop state"
        zeroActualContinueDoesNotCaptureState
    , test "SURF-009 loop-state alpha renaming preserves semantic identity"
        loopStateAlphaRenamingPreservesIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectJoinInvariant :: IO (Either String ())
expectJoinInvariant = do
  parsed <- parseFixture "accepted/23-join-invariant.phil"
  pure $ do
    expression <- singleComponentExpression =<< mapLeft show parsed
    case expression of
      GrammarV1IfExpression condition (Just joinClause) thenBlock (Just elseBlock) -> do
        assert (locatedValue condition == GrammarV1BoolExpression True)
          "if condition was not true"
        case grammarV1JoinState (locatedValue joinClause) of
          [Located _ slot] -> do
            assert (locatedValue (grammarV1StateSlotName slot) == "x_next")
              "join state slot name was not x_next"
            assert (locatedValue (grammarV1StateSlotType slot) == GrammarV1UnsignedType "U32")
              "join state slot type was not U32"
          slots -> Left ("expected one join state slot, got " <> show (length slots))
        case grammarV1JoinInvariant (locatedValue joinClause) of
          Just invariant -> assertNameIntegerRelation GrammarV1GreaterEqualRelation "x_next" "0" invariant
          Nothing -> Left "join invariant was missing"
        assertSingleExpressionName "x" thenBlock
        assertSingleExpressionName "x" elseBlock
      other -> Left ("expected if expression with join and else, got " <> show other)

expectTypedLoopState :: IO (Either String ())
expectTypedLoopState = do
  parsed <- parseFixture "accepted/24-typed-loop-state.phil"
  pure $ do
    expression <- singleComponentExpression =<< mapLeft show parsed
    case expression of
      GrammarV1LoopExpression [Located _ binding] (Just invariant) body -> do
        assert (locatedValue (grammarV1StateBindingName binding) == "i")
          "loop state binding name was not i"
        assert (fmap locatedValue (grammarV1StateBindingType binding) == Just (GrammarV1UnsignedType "U32"))
          "loop state binding type was not U32"
        assertSimpleName "n" (grammarV1StateBindingInitializer binding)
        assertNameIntegerRelation GrammarV1GreaterEqualRelation "i" "0" invariant
        case grammarV1BlockStatements (locatedValue body) of
          [Located _ (GrammarV1ExpressionStatement (Located _ (GrammarV1ContinueExpression [actual])))] ->
            assertSimpleName "i" actual
          statements -> Left ("expected continue(i) loop body, got " <> show statements)
      other -> Left ("expected typed loop expression, got " <> show other)

untypedLoopAndZeroContinuePreserved :: Either String ()
untypedLoopAndZeroContinuePreserved = do
  expression <- singleComponentExpression =<< mapLeft show
    (parseGrammarV1StructuralSource "untyped-loop" source)
  case expression of
    GrammarV1LoopExpression [Located _ binding] Nothing body -> do
      assert (grammarV1StateBindingType binding == Nothing)
        "untyped loop state unexpectedly acquired a type"
      assertSimpleName "n" (grammarV1StateBindingInitializer binding)
      case grammarV1BlockStatements (locatedValue body) of
        [Located _ (GrammarV1ExpressionStatement (Located _ (GrammarV1ContinueExpression [])))] -> Right ()
        statements -> Left ("expected zero-actual continue, got " <> show statements)
    other -> Left ("expected untyped loop expression, got " <> show other)
  where
    source = "component C(n : U32) { loop state (i = n) { continue; }; }"

loopStateTrailingCommaRejects :: Either String ()
loopStateTrailingCommaRejects =
  expectReject "component C(n : U32) { loop state (i = n,) { continue; }; }"

matchJoinBindersArePostArm :: Either String ()
matchJoinBindersArePostArm = do
  functionDecl <- onlyFunction "join-match-post-arm" $ Text.unlines
    [ "fn join_match(tagged : U8) -> U8 satisfies C {"
    , "  match tagged join state (selected : U8) {"
    , "    Left(selected) => selected;"
    , "    Right(selected) => selected;"
    , "  };"
    , "  return tagged;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.JoinMatch"
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedJoin initialScope expression
  case checked of
    GrammarV1CheckedMatchJoinExpression checkedCase checkedClause ->
      case grammarV1CheckedCaseArms checkedCase of
        [leftArm, rightArm] -> do
          leftBinder <- exactlyOne "left arm binder"
            (grammarV1CheckedCaseArmBinders leftArm)
          rightBinder <- exactlyOne "right arm binder"
            (grammarV1CheckedCaseArmBinders rightArm)
          joinSlot <- exactlyOne "join state slot" (grammarV1CheckedJoinSlots checkedClause)
          let joinBinder = grammarV1CheckedJoinSlotBinder joinSlot
          assert (grammarV1ResolvedBinderDisplayName leftBinder == "selected")
            "left arm binder spelling was not selected"
          assert (grammarV1ResolvedBinderDisplayName rightBinder == "selected")
            "right arm binder spelling was not selected"
          assert (grammarV1ResolvedBinderDisplayName joinBinder == "selected")
            "post-join binder spelling was not selected"
          assert
            (grammarV1ResolvedBinderKey leftBinder /= grammarV1ResolvedBinderKey rightBinder
              && grammarV1ResolvedBinderKey leftBinder /= grammarV1ResolvedBinderKey joinBinder
              && grammarV1ResolvedBinderKey rightBinder /= grammarV1ResolvedBinderKey joinBinder)
            "arm-local and post-join binders did not receive distinct semantic identities"
          assert
            (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey joinBinder) == 3)
            "post-join binder was not allocated after both sibling arm binders"
          resolved <- resolveLike joinBinder finalScope
          assert (grammarV1ResolvedBinderKey resolved == grammarV1ResolvedBinderKey joinBinder)
            "post-join binder was not visible in the successor scope"
        other -> Left ("expected two checked match arms, got " <> show other)
    other -> Left ("expected checked match join, got " <> show other)

joinBinderCannotShadowParameter :: Either String ()
joinBinderCannotShadowParameter = do
  functionDecl <- onlyFunction "join-shadow" $ Text.unlines
    [ "fn join_shadow(seed : U8) -> U8 satisfies C {"
    , "  match seed join state (seed : U8) {"
    , "    Left => seed;"
    , "    Right => seed;"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinShadow") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedJoinExpressionInScope initialScope expression of
    Just (Left (GrammarV1JoinStateBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "seed")
          "join shadowing diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "seed")
          "join shadowing diagnostic lost active enclosing binder"
    other -> Left ("expected active join-binder rejection, got " <> show other)

dependentJoinSlotsResolveEarlierBinders :: Either String ()
dependentJoinSlotsResolveEarlierBinders = do
  functionDecl <- onlyFunction "join-dependent" $ Text.unlines
    [ "fn join_dependent(tagged : U8) -> U8 satisfies C {"
    , "  match tagged join state (n : U8, payload : Bytes[n]) invariant n >= 0 {"
    , "    Left => tagged;"
    , "    Right => tagged;"
    , "  };"
    , "  return tagged;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinDependent") functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedJoin initialScope expression
  checkedClause <- matchJoinClause checked
  case grammarV1CheckedJoinSlots checkedClause of
    [nSlot, payloadSlot] -> do
      let nBinder = grammarV1CheckedJoinSlotBinder nSlot
          payloadBinder = grammarV1CheckedJoinSlotBinder payloadSlot
      dependency <- exactlyOne "payload type dependency"
        (grammarV1CheckedJoinSlotTypeReferences payloadSlot)
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedJoinReferenceBinder dependency)
          == grammarV1ResolvedBinderKey nBinder)
        "later join slot did not resolve earlier n binder"
      invariantReference <- exactlyOne "join invariant reference"
        (grammarV1CheckedJoinInvariantReferences checkedClause)
      assert
        (grammarV1ResolvedBinderKey
          (grammarV1CheckedJoinReferenceBinder invariantReference)
          == grammarV1ResolvedBinderKey nBinder)
        "join invariant was not checked after state-slot binding"
      resolvedPayload <- resolveLike payloadBinder finalScope
      assert
        (grammarV1ResolvedBinderKey resolvedPayload
          == grammarV1ResolvedBinderKey payloadBinder)
        "later post-join slot was not visible in successor scope"
    other -> Left ("expected n/payload join slots, got " <> show other)

joinStateForwardReferenceRejects :: Either String ()
joinStateForwardReferenceRejects = do
  functionDecl <- onlyFunction "join-forward" $ Text.unlines
    [ "fn join_forward(tagged : U8) -> U8 satisfies C {"
    , "  match tagged join state (payload : Bytes[n], n : U8) {"
    , "    Left => tagged;"
    , "    Right => tagged;"
    , "  };"
    , "  return tagged;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinForward") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedJoinExpressionInScope initialScope expression of
    Just (Left (GrammarV1JoinStateForwardReference missing)) ->
      assert (locatedValue missing == "n")
        "forward-reference diagnostic lost future slot spelling"
    other -> Left ("expected join-state forward-reference rejection, got " <> show other)

ifJoinPredecessorScopesAreDisjoint :: Either String ()
ifJoinPredecessorScopesAreDisjoint = do
  functionDecl <- onlyFunction "join-if-siblings" $ Text.unlines
    [ "fn join_if(cond : Bool, seed : U8) -> U8 satisfies C {"
    , "  if cond join state (result : U8) {"
    , "    let temp = seed;"
    , "    temp;"
    , "  } else {"
    , "    let temp = seed;"
    , "    temp;"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinIf") functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedJoin initialScope expression
  case checked of
    GrammarV1CheckedIfJoinExpression _ trueBranch (Just falseBranch) checkedClause -> do
      trueTemp <- branchLetBinder trueBranch
      falseTemp <- branchLetBinder falseBranch
      joinSlot <- exactlyOne "if join slot" (grammarV1CheckedJoinSlots checkedClause)
      let resultBinder = grammarV1CheckedJoinSlotBinder joinSlot
      assert
        (grammarV1ResolvedBinderKey trueTemp /= grammarV1ResolvedBinderKey falseTemp)
        "sibling if branches reused one temp semantic identity"
      assert
        (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey trueTemp) == 2
          && grammarV1BinderOrdinal (grammarV1ResolvedBinderKey falseTemp) == 3
          && grammarV1BinderOrdinal (grammarV1ResolvedBinderKey resultBinder) == 4)
        "if-branch/post-join binder ordinals were not threaded in control-flow order"
      case grammarV1ResolveLocal
          (Located (grammarV1ResolvedBinderSourceSpan trueTemp) "temp") finalScope of
        Left (GrammarV1BinderNotInScope _) -> Right ()
        other -> Left ("branch-local temp leaked into post-join scope: " <> show other)
      resolvedResult <- resolveLike resultBinder finalScope
      assert
        (grammarV1ResolvedBinderKey resolvedResult
          == grammarV1ResolvedBinderKey resultBinder)
        "post-if join result did not enter successor scope"
    other -> Left ("expected checked if join with two predecessors, got " <> show other)

omittedElseAddsNoBindings :: Either String ()
omittedElseAddsNoBindings = do
  functionDecl <- onlyFunction "join-if-omitted" $ Text.unlines
    [ "fn join_if_omitted(cond : Bool, seed : U8) -> U8 satisfies C {"
    , "  if cond join state (result : U8) {"
    , "    seed;"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinIfOmitted") functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, _) <- checkedJoin initialScope expression
  case checked of
    GrammarV1CheckedIfJoinExpression _ _ Nothing checkedClause -> do
      joinSlot <- exactlyOne "omitted-else join slot"
        (grammarV1CheckedJoinSlots checkedClause)
      assert
        (grammarV1BinderOrdinal
          (grammarV1ResolvedBinderKey (grammarV1CheckedJoinSlotBinder joinSlot)) == 2)
        "omitted else invented a lexical binder or advanced the ordinal"
    other -> Left ("expected omitted-else checked join, got " <> show other)

joinBinderNotVisibleInArm :: Either String ()
joinBinderNotVisibleInArm = do
  functionDecl <- onlyFunction "join-arm-future" $ Text.unlines
    [ "fn join_arm_future(tagged : U8) -> U8 satisfies C {"
    , "  match tagged join state (post : U8) {"
    , "    Left => post;"
    , "    Right => tagged;"
    , "  };"
    , "  return tagged;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinArmFuture") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedJoinExpressionInScope initialScope expression of
    Nothing -> Right ()
    other -> Left ("post-join binder became visible in predecessor arm: " <> show other)

joinAlphaRenamingPreservesIdentity :: Either String ()
joinAlphaRenamingPreservesIdentity = do
  original <- onlyFunction "join-alpha-original" $ Text.unlines
    [ "fn join_alpha(tagged : U8) -> U8 satisfies C {"
    , "  match tagged join state (n : U8, payload : Bytes[n]) invariant n >= 0 {"
    , "    Left => tagged;"
    , "    Right => tagged;"
    , "  };"
    , "  return tagged;"
    , "}"
    ]
  renamed <- onlyFunction "join-alpha-renamed" $ Text.unlines
    [ "fn join_alpha(tagged : U8) -> U8 satisfies C {"
    , "    match tagged join state (count : U8, bytes : Bytes[count]) invariant count >= 0 {"
    , "      Left => tagged;"
    , "      Right => tagged;"
    , "    };"
    , "    return tagged;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.JoinAlpha"
  (_, originalScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey original)
  (_, renamedScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey renamed)
  originalExpression <- firstExpressionStatement original
  renamedExpression <- firstExpressionStatement renamed
  (originalChecked, _) <- checkedJoin originalScope originalExpression
  (renamedChecked, _) <- checkedJoin renamedScope renamedExpression
  originalClause <- matchJoinClause originalChecked
  renamedClause <- matchJoinClause renamedChecked
  let originalBinders = map grammarV1CheckedJoinSlotBinder
        (grammarV1CheckedJoinSlots originalClause)
      renamedBinders = map grammarV1CheckedJoinSlotBinder
        (grammarV1CheckedJoinSlots renamedClause)
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming join slots changed semantic binder identity"
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming join slots changed generated Core names"
  assert (map grammarV1ResolvedBinderDisplayName originalBinders == ["n", "payload"])
    "original join display spellings were not retained diagnostically"
  assert (map grammarV1ResolvedBinderDisplayName renamedBinders == ["count", "bytes"])
    "renamed join display spellings were not retained diagnostically"

loopInitializersUseEntryScope :: Either String ()
loopInitializersUseEntryScope = do
  functionDecl <- onlyFunction "loop-entry-scope" $ Text.unlines
    [ "fn loop_entry_scope(seed : U8) -> U8 satisfies C {"
    , "  loop state (i : U8 = seed) invariant i >= 0 {"
    , "    continue(i);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.LoopEntryScope"
  (parameters, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey functionDecl)
  seedBinder <- exactlyOne "loop entry parameter" parameters
  expression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedLoop initialScope expression
  slot <- exactlyOne "loop state slot" (grammarV1CheckedLoopSlots checked)
  let iBinder = grammarV1CheckedLoopSlotBinder slot
  initializerReference <- exactlyOne "loop initializer reference"
    (grammarV1CheckedLoopSlotInitializerReferences slot)
  invariantReference <- exactlyOne "loop invariant reference"
    (grammarV1CheckedLoopInvariantReferences checked)
  assert
    (grammarV1ResolvedBinderKey
      (grammarV1CheckedLexicalReferenceBinder initializerReference)
      == grammarV1ResolvedBinderKey seedBinder)
    "loop initializer did not resolve in the pre-header entry scope"
  assert
    (grammarV1ResolvedBinderKey
      (grammarV1CheckedLexicalReferenceBinder invariantReference)
      == grammarV1ResolvedBinderKey iBinder)
    "loop invariant did not resolve the established header binder"
  case grammarV1CheckedLoopBodySteps checked of
    [GrammarV1CheckedLoopContinueStep _ actuals references] -> do
      assert (length actuals == 1)
        "continue(i) did not retain exactly one explicit successor actual"
      continued <- exactlyOne "continue lexical reference" references
      assert
        (grammarV1ResolvedBinderKey
          (grammarV1CheckedLexicalReferenceBinder continued)
          == grammarV1ResolvedBinderKey iBinder)
        "continue(i) did not resolve the current loop-header occurrence"
    other -> Left ("expected one continue step, got " <> show other)
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey iBinder) == 1)
    "loop header binder did not follow the function parameter ordinal"
  assertNotInScope iBinder finalScope

dependentLoopStateResolvesEarlierHeader :: Either String ()
dependentLoopStateResolvesEarlierHeader = do
  functionDecl <- onlyFunction "loop-dependent-state" $ Text.unlines
    [ "fn loop_dependent_state(seed : U8) -> U8 satisfies C {"
    , "  loop state (n : U8 = seed, payload : Bytes[n] = seed) invariant n >= 0 {"
    , "    continue(n, payload);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopDependentState") functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedLoop initialScope expression
  case grammarV1CheckedLoopSlots checked of
    [nSlot, payloadSlot] -> do
      let nBinder = grammarV1CheckedLoopSlotBinder nSlot
          payloadBinder = grammarV1CheckedLoopSlotBinder payloadSlot
      dependency <- exactlyOne "loop payload type dependency"
        (grammarV1CheckedLoopSlotTypeReferences payloadSlot)
      assert
        (grammarV1ResolvedBinderKey
          (grammarV1CheckedLexicalReferenceBinder dependency)
          == grammarV1ResolvedBinderKey nBinder)
        "later loop-state type did not resolve earlier header binder n"
      payloadInitializer <- exactlyOne "payload entry initializer reference"
        (grammarV1CheckedLoopSlotInitializerReferences payloadSlot)
      assert
        (grammarV1ResolvedBinderDisplayName
          (grammarV1CheckedLexicalReferenceBinder payloadInitializer) == "seed")
        "later loop initializer incorrectly resolved through header scope"
      case grammarV1CheckedLoopBodySteps checked of
        [GrammarV1CheckedLoopContinueStep _ actuals references] -> do
          assert (length actuals == 2)
            "continue(n, payload) did not preserve exact successor arity"
          assert
            (map (grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder)
                references
              == [grammarV1ResolvedBinderKey nBinder,
                  grammarV1ResolvedBinderKey payloadBinder])
            "continue actuals did not resolve the two current header binders"
        other -> Left ("expected dependent continue step, got " <> show other)
      assertNotInScope nBinder finalScope
      assertNotInScope payloadBinder finalScope
    other -> Left ("expected n/payload loop slots, got " <> show other)

loopInitializerCannotSeeHeaderBinder :: Either String ()
loopInitializerCannotSeeHeaderBinder = do
  functionDecl <- onlyFunction "loop-future-initializer" $ Text.unlines
    [ "fn loop_future_initializer(seed : U8) -> U8 satisfies C {"
    , "  loop state (i : U8 = i) {"
    , "    continue(i);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopFutureInitializer") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedLoopExpressionInScope initialScope expression of
    Just (Left (GrammarV1LoopStateReferenceError
      (GrammarV1LexicalReferenceForwardReference missing))) ->
        assert (locatedValue missing == "i")
          "loop initializer forward-reference diagnostic lost state spelling"
    other -> Left ("expected loop initializer forward-reference rejection, got " <> show other)

loopTypeForwardReferenceRejects :: Either String ()
loopTypeForwardReferenceRejects = do
  functionDecl <- onlyFunction "loop-forward-type" $ Text.unlines
    [ "fn loop_forward_type(seed : U8) -> U8 satisfies C {"
    , "  loop state (payload : Bytes[n] = seed, n : U8 = seed) {"
    , "    continue(payload, n);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopForwardType") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedLoopExpressionInScope initialScope expression of
    Just (Left (GrammarV1LoopStateReferenceError
      (GrammarV1LexicalReferenceForwardReference missing))) ->
        assert (locatedValue missing == "n")
          "loop-state type forward-reference diagnostic lost future spelling"
    other -> Left ("expected loop-state type forward-reference rejection, got " <> show other)

loopStateCannotShadowParameter :: Either String ()
loopStateCannotShadowParameter = do
  functionDecl <- onlyFunction "loop-shadow-parameter" $ Text.unlines
    [ "fn loop_shadow_parameter(i : U8) -> U8 satisfies C {"
    , "  loop state (i : U8 = i) {"
    , "    continue(i);"
    , "  };"
    , "  return i;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopShadowParameter") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedLoopExpressionInScope initialScope expression of
    Just (Left (GrammarV1LoopStateBinderError
      (GrammarV1ActiveShadowing shadowing previous))) -> do
        assert (locatedValue shadowing == "i")
          "loop-state shadowing diagnostic lost local spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "i")
          "loop-state shadowing diagnostic lost enclosing parameter"
    other -> Left ("expected loop-state active-shadowing rejection, got " <> show other)

duplicateLoopStateRejects :: Either String ()
duplicateLoopStateRejects = do
  functionDecl <- onlyFunction "loop-duplicate-state" $ Text.unlines
    [ "fn loop_duplicate_state(seed : U8) -> U8 satisfies C {"
    , "  loop state (item : U8 = seed, item : U8 = seed) {"
    , "    continue(item, item);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopDuplicateState") functionDecl)
  expression <- firstExpressionStatement functionDecl
  case grammarV1CheckedLoopExpressionInScope initialScope expression of
    Just (Left (GrammarV1LoopStateBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "item")
          "duplicate loop-state diagnostic lost second spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "item")
          "duplicate loop-state diagnostic lost first binder"
    other -> Left ("expected duplicate loop-state rejection, got " <> show other)

loopBodyLetBreakScopeCloses :: Either String ()
loopBodyLetBreakScopeCloses = do
  functionDecl <- onlyFunction "loop-body-break" $ Text.unlines
    [ "fn loop_body_break(seed : U8) -> U8 satisfies C {"
    , "  loop state (i : U8 = seed) {"
    , "    let temp = i;"
    , "    break(temp);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopBodyBreak") functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedLoop initialScope expression
  loopSlot <- exactlyOne "loop body state slot" (grammarV1CheckedLoopSlots checked)
  let iBinder = grammarV1CheckedLoopSlotBinder loopSlot
  case grammarV1CheckedLoopBodySteps checked of
    [ GrammarV1CheckedLoopBodyLetStep _ initializerReferences [tempBinder]
      , GrammarV1CheckedLoopBreakStep _ actuals breakReferences
      ] -> do
        initializerReference <- exactlyOne "loop body let initializer"
          initializerReferences
        assert
          (grammarV1ResolvedBinderKey
            (grammarV1CheckedLexicalReferenceBinder initializerReference)
            == grammarV1ResolvedBinderKey iBinder)
          "loop-body let initializer did not resolve header state"
        assert (grammarV1ResolvedBinderDisplayName tempBinder == "temp")
          "loop-body let binder spelling changed"
        assert (length actuals == 1)
          "break(temp) did not retain exactly one explicit exit actual"
        breakReference <- exactlyOne "break lexical reference" breakReferences
        assert
          (grammarV1ResolvedBinderKey
            (grammarV1CheckedLexicalReferenceBinder breakReference)
            == grammarV1ResolvedBinderKey tempBinder)
          "break(temp) did not resolve body-local temp"
        assert
          (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey tempBinder) == 2)
          "body-local temp did not receive fresh identity after loop state"
        assertNotInScope iBinder finalScope
        assertNotInScope tempBinder finalScope
    other -> Left ("expected loop let then break trace, got " <> show other)

zeroActualContinueDoesNotCaptureState :: Either String ()
zeroActualContinueDoesNotCaptureState = do
  functionDecl <- onlyFunction "loop-zero-continue" $ Text.unlines
    [ "fn loop_zero_continue(seed : U8) -> U8 satisfies C {"
    , "  loop state (i : U8 = seed) {"
    , "    continue;"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope
      (DeclarationKey "decl.LoopZeroContinue") functionDecl)
  expression <- firstExpressionStatement functionDecl
  (checked, _) <- checkedLoop initialScope expression
  case grammarV1CheckedLoopBodySteps checked of
    [GrammarV1CheckedLoopContinueStep _ actuals references] -> do
      assert (null actuals)
        "bare continue acquired an implicit successor actual"
      assert (null references)
        "bare continue implicitly captured the current loop-state binder"
    other -> Left ("expected one zero-actual continue step, got " <> show other)

loopStateAlphaRenamingPreservesIdentity :: Either String ()
loopStateAlphaRenamingPreservesIdentity = do
  original <- onlyFunction "loop-alpha-original" $ Text.unlines
    [ "fn loop_alpha(seed : U8) -> U8 satisfies C {"
    , "  loop state (i : U8 = seed) invariant i >= 0 {"
    , "    continue(i);"
    , "  };"
    , "  return seed;"
    , "}"
    ]
  renamed <- onlyFunction "loop-alpha-renamed" $ Text.unlines
    [ "fn loop_alpha(seed : U8) -> U8 satisfies C {"
    , "    loop state (cursor : U8 = seed) invariant cursor >= 0 {"
    , "      continue(cursor);"
    , "    };"
    , "    return seed;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.LoopAlpha"
  (_, originalScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey original)
  (_, renamedScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey renamed)
  originalExpression <- firstExpressionStatement original
  renamedExpression <- firstExpressionStatement renamed
  (originalChecked, _) <- checkedLoop originalScope originalExpression
  (renamedChecked, _) <- checkedLoop renamedScope renamedExpression
  originalSlot <- exactlyOne "original alpha loop slot"
    (grammarV1CheckedLoopSlots originalChecked)
  renamedSlot <- exactlyOne "renamed alpha loop slot"
    (grammarV1CheckedLoopSlots renamedChecked)
  let originalBinder = grammarV1CheckedLoopSlotBinder originalSlot
      renamedBinder = grammarV1CheckedLoopSlotBinder renamedSlot
  assert
    (grammarV1ResolvedBinderKey originalBinder
      == grammarV1ResolvedBinderKey renamedBinder)
    "alpha-renaming loop state changed semantic BinderKey"
  assert
    (grammarV1ResolvedBinderCoreName originalBinder
      == grammarV1ResolvedBinderCoreName renamedBinder)
    "alpha-renaming loop state changed generated Core name"
  assert (grammarV1ResolvedBinderDisplayName originalBinder == "i")
    "original loop-state spelling was not retained diagnostically"
  assert (grammarV1ResolvedBinderDisplayName renamedBinder == "cursor")
    "renamed loop-state spelling was not retained diagnostically"

checkedJoin
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either String (GrammarV1CheckedJoinExpression, GrammarV1LexicalScope)
checkedJoin scope expression =
  case grammarV1CheckedJoinExpressionInScope scope expression of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked join expression, got " <> show other)

checkedLoop
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either String (GrammarV1CheckedLoopState, GrammarV1LexicalScope)
checkedLoop scope expression =
  case grammarV1CheckedLoopExpressionInScope scope expression of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked loop scope, got " <> show other)

matchJoinClause
  :: GrammarV1CheckedJoinExpression
  -> Either String GrammarV1CheckedJoinClause
matchJoinClause checked = case checked of
  GrammarV1CheckedMatchJoinExpression _ clause -> Right clause
  other -> Left ("expected match join expression, got " <> show other)

branchLetBinder :: GrammarV1CheckedIfBranch -> Either String GrammarV1ResolvedBinder
branchLetBinder branch = case grammarV1CheckedIfBranchSteps branch of
  GrammarV1CheckedLetBindingStep _ _ [binder] : _ -> Right binder
  other -> Left ("expected leading single-binder let step, got " <> show other)

resolveLike
  :: GrammarV1ResolvedBinder
  -> GrammarV1LexicalScope
  -> Either String GrammarV1ResolvedBinder
resolveLike binder scope = mapLeft show $ grammarV1ResolveLocal
  (Located (grammarV1ResolvedBinderSourceSpan binder)
    (grammarV1ResolvedBinderDisplayName binder))
  scope

assertNotInScope
  :: GrammarV1ResolvedBinder
  -> GrammarV1LexicalScope
  -> Either String ()
assertNotInScope binder scope =
  case grammarV1ResolveLocal
      (Located (grammarV1ResolvedBinderSourceSpan binder)
        (grammarV1ResolvedBinderDisplayName binder))
      scope of
    Left (GrammarV1BinderNotInScope _) -> Right ()
    other -> Left
      ("closed lexical binder remained visible after scope exit: " <> show other)

firstExpressionStatement
  :: GrammarV1FunctionDecl
  -> Either String (Located GrammarV1Expression)
firstExpressionStatement functionDecl =
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
    Located _ (GrammarV1ExpressionStatement expression) : _ -> Right expression
    statements -> Left ("expected leading expression statement, got " <> show statements)

onlyFunction :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left
      ("expected one function declaration, got " <> show (length declarations))

singleComponentExpression :: GrammarV1SourceFile -> Either String GrammarV1Expression
singleComponentExpression sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ComponentDeclaration componentDecl ->
      case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
        [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
        statements -> Left ("expected one component expression statement, got " <> show statements)
    other -> Left ("expected component declaration, got " <> show other)
  declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))

assertSingleExpressionName :: Text.Text -> Located GrammarV1Block -> Either String ()
assertSingleExpressionName expected block =
  case grammarV1BlockStatements (locatedValue block) of
    [Located _ (GrammarV1ExpressionStatement expression)] -> assertSimpleName expected expression
    statements -> Left ("expected one expression statement, got " <> show statements)

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
      ("expected simple name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "simple name unexpectedly had static arguments"
    assert (null arguments) "simple name unexpectedly had term arguments"
  other -> Left ("expected simple name expression, got " <> show other)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "join-loop-negative" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

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
