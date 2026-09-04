{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
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
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 match join binders are post-arm occurrences with fresh identity"
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
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

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
    GrammarV1CheckedMatchJoinExpression checkedCase checkedClause -> do
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

checkedJoin
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either String (GrammarV1CheckedJoinExpression, GrammarV1LexicalScope)
checkedJoin scope expression =
  case grammarV1CheckedJoinExpressionInScope scope expression of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked join expression, got " <> show other)

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
