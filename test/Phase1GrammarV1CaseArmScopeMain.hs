{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.List as List
import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderKind (GrammarV1LetPatternBinder)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1BindLocal
  , grammarV1FunctionParameterScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.CaseArmScope
  ( GrammarV1CaseArmScopeError (..)
  , GrammarV1CaseExpressionKind (..)
  , GrammarV1CheckedCaseArm (..)
  , GrammarV1CheckedCaseExpression (..)
  , grammarV1CheckedCaseExpressionInScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 match arms use disjoint child scopes with fresh semantic identities"
        matchSiblingScopesAreDistinct
    , test "SURF-009 offer record aliases and arm-local lets compose with exact scope"
        offerRecordAliasesComposeWithLet
    , test "SURF-009 decide shares the exact case-arm binder authority"
        decideUsesCaseArmAuthority
    , test "SURF-009 duplicate case binders reject"
        duplicateCaseBindersReject
    , test "SURF-009 case binders cannot shadow active enclosing parameters"
        caseBinderCannotShadowParameter
    , test "SURF-009 scrutinees resolve before arm binders exist"
        scrutineeCannotSeeFutureArmBinder
    , test "SURF-009 match join-state remains for the join-state binder slice"
        matchJoinRemainsOutsideCompetence
    , test "SURF-009 alpha-renamed case binders preserve semantic identity"
        caseBinderAlphaRenamingPreservesIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

matchSiblingScopesAreDistinct :: Either String ()
matchSiblingScopesAreDistinct = do
  functionDecl <- onlyFunction "case-match-siblings" $ Text.unlines
    [ "fn match_scope(tagged : U8) -> U8 satisfies C {"
    , "  return match tagged {"
    , "    Left(x, y) => x;"
    , "    Right(x, y) => y;"
    , "  };"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.MatchScope"
  (parameters, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey functionDecl)
  parameter <- exactlyOne "match parameter" parameters
  expression <- onlyReturnExpression functionDecl
  (checked, finalScope) <- checkedCase initialScope expression
  assert
    (grammarV1CheckedCaseExpressionKind checked == GrammarV1MatchCaseExpression)
    "match expression did not retain its case-expression category"
  assert
    (grammarV1ResolvedBinderKey
      (grammarV1CheckedLocalValueBinder (grammarV1CheckedCaseScrutinee checked))
      == grammarV1ResolvedBinderKey parameter)
    "match scrutinee did not resolve before arm scope entry"
  case grammarV1CheckedCaseArms checked of
    [leftArm, rightArm] -> do
      let leftBinders = grammarV1CheckedCaseArmBinders leftArm
          rightBinders = grammarV1CheckedCaseArmBinders rightArm
          allBinders = leftBinders <> rightBinders
      assert (map grammarV1ResolvedBinderDisplayName leftBinders == ["x", "y"])
        "left tuple case binders were not allocated in source order"
      assert (map grammarV1ResolvedBinderDisplayName rightBinders == ["x", "y"])
        "right tuple case binders were not allocated in source order"
      assert
        (List.nub (map grammarV1ResolvedBinderKey allBinders)
          == map grammarV1ResolvedBinderKey allBinders)
        "sibling arms reused a semantic binder key"
      leftX <- headEither "left x binder" leftBinders
      rightY <- lastEither "right y binder" rightBinders
      leftOccurrence <- exactlyOneOccurrence leftArm
      rightOccurrence <- exactlyOneOccurrence rightArm
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder leftOccurrence)
          == grammarV1ResolvedBinderKey leftX)
        "left arm body did not resolve its own x binder"
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder rightOccurrence)
          == grammarV1ResolvedBinderKey rightY)
        "right arm body did not resolve its own y binder"
      case grammarV1ResolveLocal
          (Located (grammarV1ResolvedBinderSourceSpan leftX) "x") finalScope of
        Left (GrammarV1BinderNotInScope _) -> Right ()
        other -> Left ("arm-local x leaked after match scope exit: " <> show other)
      let laterSource = Located (grammarV1ResolvedBinderSourceSpan parameter) "later"
      (laterBinder, _) <- mapLeft show
        (grammarV1BindLocal GrammarV1LetPatternBinder laterSource finalScope)
      assert
        (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey laterBinder) == 5)
        "declaration-wide binder ordinal did not advance across both sibling arms"
    other -> Left ("expected two checked match arms, got " <> show other)

offerRecordAliasesComposeWithLet :: Either String ()
offerRecordAliasesComposeWithLet = do
  functionDecl <- onlyFunction "case-offer-record" $ Text.unlines
    [ "fn offer_scope(endpoint : U8) -> U8 satisfies C {"
    , "  return offer endpoint {"
    , "    Packet{payload as p, tag} => {"
    , "      let copy = p;"
    , "      return copy;"
    , "    }"
    , "    Other{payload as p, tag} => tag;"
    , "  };"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.OfferScope") functionDecl)
  expression <- onlyReturnExpression functionDecl
  (checked, _) <- checkedCase initialScope expression
  assert
    (grammarV1CheckedCaseExpressionKind checked == GrammarV1OfferCaseExpression)
    "offer expression did not retain its case-expression category"
  case grammarV1CheckedCaseArms checked of
    [packetArm, otherArm] -> do
      let packetBinders = grammarV1CheckedCaseArmBinders packetArm
          otherBinders = grammarV1CheckedCaseArmBinders otherArm
      assert (map grammarV1ResolvedBinderDisplayName packetBinders == ["p", "tag"])
        "record field alias/shorthand did not choose the exact local binder names"
      assert (map grammarV1ResolvedBinderDisplayName otherBinders == ["p", "tag"])
        "second record arm did not preserve alias/shorthand binder names"
      packetP <- headEither "Packet p binder" packetBinders
      case grammarV1CheckedCaseArmBodySteps packetArm of
        [ GrammarV1CheckedLetBindingStep _ initializer [copyBinder]
          , GrammarV1CheckedLetOccurrenceStep _ returned
          ] -> do
            assert
              (grammarV1ResolvedBinderKey
                (grammarV1CheckedLocalValueBinder initializer)
                == grammarV1ResolvedBinderKey packetP)
              "arm-local let initializer did not resolve the case alias p"
            assert (grammarV1ResolvedBinderDisplayName copyBinder == "copy")
              "arm-local let did not allocate copy"
            assert
              (grammarV1ResolvedBinderKey
                (grammarV1CheckedLocalValueBinder returned)
                == grammarV1ResolvedBinderKey copyBinder)
              "arm-local return did not resolve the let binder copy"
        other -> Left ("unexpected Packet arm body scope trace: " <> show other)
      otherTag <- lastEither "Other tag binder" otherBinders
      otherOccurrence <- exactlyOneOccurrence otherArm
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder otherOccurrence)
          == grammarV1ResolvedBinderKey otherTag)
        "record shorthand tag did not resolve to the arm-local tag binder"
    other -> Left ("expected two checked offer arms, got " <> show other)

decideUsesCaseArmAuthority :: Either String ()
decideUsesCaseArmAuthority = do
  functionDecl <- onlyFunction "case-decide" $ Text.unlines
    [ "fn decide_scope(token : U8) -> U8 satisfies C {"
    , "  return decide token {"
    , "    Yes(value) => value;"
    , "    No(other) => other;"
    , "  };"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.DecideScope") functionDecl)
  expression <- onlyReturnExpression functionDecl
  (checked, _) <- checkedCase initialScope expression
  assert
    (grammarV1CheckedCaseExpressionKind checked == GrammarV1DecideCaseExpression)
    "decide did not route through the shared case-arm authority"
  assert
    (map (map grammarV1ResolvedBinderDisplayName . grammarV1CheckedCaseArmBinders)
      (grammarV1CheckedCaseArms checked) == [["value"], ["other"]])
    "decide case binders were not preserved exactly"

duplicateCaseBindersReject :: Either String ()
duplicateCaseBindersReject = do
  functionDecl <- onlyFunction "case-duplicate" $ Text.unlines
    [ "fn duplicate_case(tagged : U8) -> U8 satisfies C {"
    , "  return match tagged {"
    , "    Left(item, item) => item;"
    , "  };"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.DuplicateCase") functionDecl)
  expression <- onlyReturnExpression functionDecl
  case grammarV1CheckedCaseExpressionInScope initialScope expression of
    Just (Left (GrammarV1CaseArmBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "item")
          "duplicate case-binder diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "item")
          "duplicate case-binder diagnostic lost first binder"
    other -> Left ("expected duplicate case-binder rejection, got " <> show other)

caseBinderCannotShadowParameter :: Either String ()
caseBinderCannotShadowParameter = do
  functionDecl <- onlyFunction "case-shadow" $ Text.unlines
    [ "fn shadow_case(x : U8) -> U8 satisfies C {"
    , "  return match x {"
    , "    Same(x) => x;"
    , "  };"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.ShadowCase") functionDecl)
  expression <- onlyReturnExpression functionDecl
  case grammarV1CheckedCaseExpressionInScope initialScope expression of
    Just (Left (GrammarV1CaseArmBinderError
      (GrammarV1ActiveShadowing shadowing previous))) -> do
        assert (locatedValue shadowing == "x")
          "case shadowing diagnostic lost arm spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "x")
          "case shadowing diagnostic lost enclosing parameter"
    other -> Left ("expected active case-binder shadow rejection, got " <> show other)

scrutineeCannotSeeFutureArmBinder :: Either String ()
scrutineeCannotSeeFutureArmBinder = do
  functionDecl <- onlyFunction "case-future-scrutinee" $ Text.unlines
    [ "fn future_case(seed : U8) -> U8 satisfies C {"
    , "  return match future {"
    , "    Left(future) => future;"
    , "  };"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.FutureCase") functionDecl)
  expression <- onlyReturnExpression functionDecl
  case grammarV1CheckedCaseExpressionInScope initialScope expression of
    Nothing -> Right ()
    other -> Left ("future arm binder leaked into scrutinee scope: " <> show other)

matchJoinRemainsOutsideCompetence :: Either String ()
matchJoinRemainsOutsideCompetence = do
  functionDecl <- onlyFunction "case-join-wall" $ Text.unlines
    [ "fn join_case(tagged : U8) -> U8 satisfies C {"
    , "  return match tagged join state (saved : U8) {"
    , "    Left(value) => value;"
    , "  };"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.JoinCase") functionDecl)
  expression <- onlyReturnExpression functionDecl
  case grammarV1CheckedCaseExpressionInScope initialScope expression of
    Nothing -> Right ()
    other -> Left ("join-state binder escaped its later SURF-009 slice: " <> show other)

caseBinderAlphaRenamingPreservesIdentity :: Either String ()
caseBinderAlphaRenamingPreservesIdentity = do
  original <- onlyFunction "case-alpha-original" $ Text.unlines
    [ "fn alpha_case(tagged : U8) -> U8 satisfies C {"
    , "  return match tagged {"
    , "    Left(x, y) => y;"
    , "    Right(z) => z;"
    , "  };"
    , "}"
    ]
  renamed <- onlyFunction "case-alpha-renamed" $ Text.unlines
    [ "fn alpha_case(source : U8) -> U8 satisfies C {"
    , "    return match source {"
    , "      Left(a, b) => b;"
    , "      Right(c) => c;"
    , "    };"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.AlphaCase"
  (_, originalScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey original)
  (_, renamedScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey renamed)
  originalExpression <- onlyReturnExpression original
  renamedExpression <- onlyReturnExpression renamed
  (originalChecked, _) <- checkedCase originalScope originalExpression
  (renamedChecked, _) <- checkedCase renamedScope renamedExpression
  let originalBinders = concatMap grammarV1CheckedCaseArmBinders
        (grammarV1CheckedCaseArms originalChecked)
      renamedBinders = concatMap grammarV1CheckedCaseArmBinders
        (grammarV1CheckedCaseArms renamedChecked)
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming case binders changed semantic identity"
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming case binders changed Core identity"
  assert (map grammarV1ResolvedBinderDisplayName originalBinders == ["x", "y", "z"])
    "original case binder spellings were not retained diagnostically"
  assert (map grammarV1ResolvedBinderDisplayName renamedBinders == ["a", "b", "c"])
    "renamed case binder spellings were not retained diagnostically"

checkedCase
  :: Phil.Surface.GrammarV1.BinderScope.GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either
      String
      (GrammarV1CheckedCaseExpression, Phil.Surface.GrammarV1.BinderScope.GrammarV1LexicalScope)
checkedCase scope expression =
  case grammarV1CheckedCaseExpressionInScope scope expression of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked case expression, got " <> show other)

exactlyOneOccurrence
  :: GrammarV1CheckedCaseArm
  -> Either String GrammarV1CheckedLocalValueOccurrence
exactlyOneOccurrence arm =
  case grammarV1CheckedCaseArmBodySteps arm of
    [GrammarV1CheckedLetOccurrenceStep _ occurrence] -> Right occurrence
    other -> Left ("expected one arm-local occurrence, got " <> show other)

onlyReturnExpression
  :: GrammarV1FunctionDecl
  -> Either String (Located GrammarV1Expression)
onlyReturnExpression functionDecl =
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
    [Located _ (GrammarV1ReturnStatement expression)] -> Right expression
    other -> Left ("expected one return statement, got " <> show other)

onlyFunction :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left
      ("expected one function declaration, got " <> show (length declarations))

headEither :: String -> [a] -> Either String a
headEither _ (value : _) = Right value
headEither label [] = Left ("expected " <> label)

lastEither :: String -> [a] -> Either String a
lastEither _ values@(_ : _) = Right (last values)
lastEither label [] = Left ("expected " <> label)

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
