{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
  )
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..)
  , grammarV1CheckedBorrowResourceFunction
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "FSEM-01 checked linear Bytes loan closes before owner return"
        checkedBorrowReturnsOwner
    , test "FSEM-01 view as borrow block result rejects with production BorrowEscape"
        escapedViewRejectsWithProductionClass
    , test "FSEM-01 live view then Unit result closes loan"
        inspectedViewThenUnitClosesLoan
    , test "FSEM-01 unsupported unrestricted owner never gains invented linear mode"
        unrestrictedOwnerIsOutsideCompetence
    , test "FSEM-01 unknown owner cannot acquire a global fallback"
        unresolvedOwnerIsOutsideCompetence
    , test "FSEM-01 view name cannot shadow its exact owner binder"
        borrowViewShadowRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label outcome = case outcome of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail)
    >> pure False

checkedBorrowReturnsOwner :: Either String ()
checkedBorrowReturnsOwner = do
  result <- checkBounded "fsem01-valid" safe
  case result of
    Just (Right checked) ->
      assert (checkedTerminalControls checked == [Return (TyBytes (RefNat 8))])
        ("expected exact Bytes[8] terminal return, got " <>
          show (checkedTerminalControls checked))
    other -> Left ("expected checked production loan and return, got " <> show other)

escapedViewRejectsWithProductionClass :: Either String ()
escapedViewRejectsWithProductionClass = do
  result <- checkBounded "fsem01-escaped" escaped
  case result of
    Just (Left (GrammarV1BorrowResourceProductionError err)) -> do
      assert (surfaceErrorClass err == BorrowEscape)
        ("expected actual production BorrowEscape class, got " <> show err)
      assert (surfaceErrorDetail err == "shared view escapes its lexical scope")
        ("expected exact escaping borrowed-view diagnostic, got " <> show err)
    other -> Left ("expected production BorrowEscape, got " <> show other)

inspectedViewThenUnitClosesLoan :: Either String ()
inspectedViewThenUnitClosesLoan = do
  result <- checkBounded "fsem01-view-then-unit" viewThenUnit
  case result of
    Just (Right checked) ->
      assert (checkedTerminalControls checked == [Return (TyBytes (RefNat 8))])
        "closing a local view before returning its owner failed"
    other -> Left ("expected legal scoped loan, got " <> show other)

unrestrictedOwnerIsOutsideCompetence :: Either String ()
unrestrictedOwnerIsOutsideCompetence = do
  result <- checkBounded "fsem01-unrestricted" $ Text.unlines
    [ "fn loan(owner : U8) -> U8 satisfies C {"
    , "  borrow owner as view { view; };"
    , "  return owner;"
    , "}"
    ]
  assert (result == Nothing)
    ("U8 cannot be treated as a Linear owner by this bridge: " <> show result)

unresolvedOwnerIsOutsideCompetence :: Either String ()
unresolvedOwnerIsOutsideCompetence = do
  result <- checkBounded "fsem01-unknown" $ Text.unlines
    [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
    , "  borrow strange as view { view; };"
    , "  return owner;"
    , "}"
    ]
  assert (result == Nothing)
    ("unresolved owner must not be supplied from an invented global: " <> show result)

borrowViewShadowRejects :: Either String ()
borrowViewShadowRejects = do
  result <- checkBounded "fsem01-shadow" $ Text.unlines
    [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
    , "  borrow owner as owner { owner; };"
    , "  return owner;"
    , "}"
    ]
  case result of
    Just (Left (GrammarV1BorrowResourceBorrowError _)) -> Right ()
    other -> Left ("expected binder-scope rejection, got " <> show other)

checkBounded
  :: Text.Text
  -> Text.Text
  -> Either String
      (Maybe (Either GrammarV1BorrowResourceError SurfaceCheckResult))
checkBounded label source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls parsed of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1FunctionDeclaration fun ->
          Right $ grammarV1CheckedBorrowResourceFunction
            emptyStaticContext (DeclarationKey "decl.FSEM01Loan") fun
        other -> Left ("expected source function, got " <> show other)
    xs -> Left ("expected one top-level function, got " <> show (length xs))

safe :: Text.Text
safe = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { (); };"
  , "  return owner;"
  , "}"
  ]

escaped :: Text.Text
escaped = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { view; };"
  , "  return owner;"
  , "}"
  ]

viewThenUnit :: Text.Text
viewThenUnit = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { view; (); };"
  , "  return owner;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
