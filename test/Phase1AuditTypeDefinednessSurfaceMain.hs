{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Phase1AuditTypeDefinednessCommon
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Static (StaticContext, emptyStaticContext)
import Phil.Core.Syntax (Name (..), Proposition (..), RefTerm (..), Ty (..), Value (..))
import qualified Phil.Core.Syntax as Syntax
import Phil.Core.Value (ValueResult (..), checkValue)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))

main :: IO ()
main = runCases checks []

checks :: Mode -> [(String, Result)]
checks mode =
  [ ("S01", unsafeSource mode)
  , ("S02", do
        ty <- checked emptyStaticContext "type Safe = {s : Bool | (5 - 3) == (5 - 3)};"
        eq ty (TyRefined (Name "s") TyBool Truth)
        value <- right (checkValue (VBool False) ty emptyCheckState)
        noResidual value)
  , ("S03", capturedSource mode False)
  , ("S04", capturedSource mode True)
  , ("S05", do
        context <- namedContext "Same" (Name "r")
        ty <- checked context captureSource
        eq ty (TyRefined q TyBool (Equal (RefVar q) (RefBool True)))
        checkFalse (checkValue (VBool False) ty emptyCheckState))
  , ("S06", unsafeProofSource mode)
  , ("S07", do
        source <- parsed "type Nested = {x : {y : Bool | true} | true};"
        case grammarV1CheckedType emptyStaticContext emptySurfaceState source of
          Nothing -> Right ()
          other -> Left ("expected explicit primitive-base competence boundary: " <> show other))
  ]

captureSource :: Text
captureSource = "type Captured = {q : Bool | Same(q, true)};"

parsed :: Text -> Either String GrammarV1Type
parsed source = do
  ast <- case parseGrammarV1StructuralSource "type-definedness-audit" source of
    Left diagnostic -> Left ("PRECONDITION parser: " <> show diagnostic)
    Right result -> Right result
  case grammarV1TopLevelDecls ast of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1TypeAliasDeclaration alias -> Right (locatedValue (grammarV1TypeAliasTarget alias))
      other -> Left ("expected alias, got " <> show other)
    other -> Left ("expected one declaration, got " <> show (length other))

checked :: StaticContext -> Text -> Either String Ty
checked context source = do
  ty <- parsed source
  case grammarV1CheckedType context emptySurfaceState ty of
    Just (Right (result, _)) -> Right result
    other -> Left ("not a checked supported source type: " <> show other)

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

unsafeSource :: Mode -> Result
unsafeSource mode = do
  source <- parsed "type Unsafe = {s : Bool | (3 - 5) == (3 - 5)};"
  case grammarV1CheckedType emptyStaticContext emptySurfaceState source of
    Just (Left (StaticallyFalseGoal _)) | mode == Regression -> Right ()
    Just (Right (ty, _)) ->
      if mode == Characterize then do
        eq ty (TyRefined (Name "s") TyBool Truth)
        value <- right (checkValue (VBool False) ty emptyCheckState)
        eq (valueResultType value) ty
        noResidual value
      else checkFalse (checkValue (VBool False) ty emptyCheckState)
    other -> Left ("unexpected source gate result (Nothing is not semantic rejection): " <> show other)

capturedSource :: Mode -> Bool -> Result
capturedSource mode literal = do
  context <- sameContext
  ty <- checked context captureSource
  if mode == Characterize then do
    eq ty (TyRefined q TyBool Truth)
    value <- right (checkValue (VBool literal) ty emptyCheckState)
    noResidual value
  else do
    eq ty (TyRefined q TyBool (Equal (RefVar q) (RefBool True)))
    if literal then right (checkValue (VBool True) ty emptyCheckState) >>= noResidual
               else checkFalse (checkValue (VBool False) ty emptyCheckState)

unsafeProofSource :: Mode -> Result
unsafeProofSource mode = do
  source <- parsed "type UnsafeProof = Proof[(3 - 5) == (3 - 5)];"
  resources <- right (insertBinding Syntax.Unrestricted (Name "truth") (TyProof Truth)
    (resourceContext emptyCheckState))
  let state = emptyCheckState { resourceContext = resources }
  case grammarV1CheckedType emptyStaticContext emptySurfaceState source of
    Just (Left (StaticallyFalseGoal _)) | mode == Regression -> Right ()
    Just (Right (ty, _)) ->
      if mode == Characterize then do
        eq ty (TyProof Truth)
        result <- right (checkValue (VVar (Name "truth")) ty state)
        eq (valueResultState result) state
        eq (residualObligations (valueResultState result)) Map.empty
      else checkFalse (checkValue (VVar (Name "truth")) ty state)
    other -> Left ("unexpected source gate result: " <> show other)
