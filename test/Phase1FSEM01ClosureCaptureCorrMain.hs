{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Callable (CallableCheckError (..), CaptureOccurrenceKey (..))
import Phil.Core.CallableScope (CallableScopeError (..), ClosureExtent (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..))
import Phil.Surface.GrammarV1.BinderScope
  (GrammarV1BinderScopeError (..))
import Phil.Surface.GrammarV1.Parser
  (GrammarV1FunctionDecl, GrammarV1SourceFile (..),
   GrammarV1TopLevelDecl (..), GrammarV1Declaration (..),
   parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.SourceClosureCapture
  (SourceClosureError (..), SourceClosureFailureStage (..),
   SourceDirectClosureRun (..), SourceBorrowClosureRun (..),
   grammarV1SourceDirectClosure, grammarV1SourceBorrowClosure)
import Phil.Surface.GrammarV1.SourceClosureCaptureCorrespondence
  (SourceClosureCorrespondenceError (..),
   verifyDirectCaptureCuts, verifyBorrowCaptureCuts)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.corr1.source"

assert :: Bool -> String -> Either String ()
assert ok msg = if ok then Right () else Left msg

parse :: Text -> Either String GrammarV1FunctionDecl
parse input = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "corr1" input)
  case grammarV1TopLevelDecls file of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("unexpected declaration: " ++ show other)
    other -> Left ("expected one parsed function: " ++ show (length other))

direct :: Text -> Either String SourceDirectClosureRun
direct input = do
  fn <- parse input
  case grammarV1SourceDirectClosure emptyStaticContext root fn of
    Just (Right run) -> Right run
    other -> Left ("source not in direct C-1 fragment: " ++ show other)

borrow :: Text -> Either String SourceBorrowClosureRun
borrow input = do
  fn <- parse input
  case grammarV1SourceBorrowClosure emptyStaticContext root fn of
    Just (Right run) -> Right run
    other -> Left ("source not in scoped C-1 fragment: " ++ show other)

checkDirect :: Text -> Int -> Bool -> Either String ()
checkDirect input numCaptures moves = do
  run <- direct input
  assert (verifyDirectCaptureCuts run == Right ())
    "independent native capture cut replay disagrees"
  assert (directFailureStage run == Nothing &&
          directOutcome run == Right () &&
          length (directCuts run) == numCaptures + 1 &&
          directFinal run == Just (last (directCuts run)))
    "accepted source did not retain exact successful cut sequence"
  let initial = directInitial run
      end = last (directCuts run)
      owners = Map.keys (Core.linearBindings initial)
  case owners of
    [owner] -> do
      assert (Map.null (Core.affineBindings end) &&
              Core.unrestrictedBindings end == Core.unrestrictedBindings initial &&
              Core.sharedLoans end == Core.sharedLoans initial &&
              (Map.member owner (Core.linearBindings end) == not moves))
        "native four-collection owner/copy frame mismatch"
      if moves then do
        assert (Core.useBinding owner end == Left (Core.UnknownBinding owner))
          "stale consumed source owner was accepted"
        assert (Map.size (Core.linearBindings end) == 0)
          "Linear capture did not consume unique owner"
      else assert (Core.linearBindings end == Core.linearBindings initial)
        "Unrestricted capture changed Linear owner"
    _ -> Left "expected one exact Linear source parameter"

checkDirectFailure :: Text -> SourceClosureFailureStage
                   -> (SourceClosureError -> Bool) -> Either String ()
checkDirectFailure input stage matches = do
  run <- direct input
  assert (verifyDirectCaptureCuts run == Right ())
    "independent precheck failure replay disagrees"
  assert (directCuts run == [directInitial run] &&
          directFinal run == Nothing &&
          directFailureStage run == Just stage &&
          either matches (const False) (directOutcome run))
    "pre-resource rejection fabricated a native owner state"

checkLexicalFailure :: Text -> (SourceClosureError -> Bool) -> Either String ()
checkLexicalFailure input matches = do
  fn <- parse input
  case grammarV1SourceDirectClosure emptyStaticContext root fn of
    Just (Left err) -> assert (matches err)
      "source lexical rejection had wrong precise error class"
    -- There is deliberately no SourceDirectClosureRun to carry a fake
    -- Core.ResourceContext after this source resolution failure.
    other -> Left ("expected pre-resource lexical rejection: " ++ show other)

checkOutOfFragment :: Text -> Bool -> Either String ()
checkOutOfFragment input isDirect = do
  fn <- parse input
  let result = if isDirect
        then case grammarV1SourceDirectClosure emptyStaticContext root fn of
          Nothing -> True
          _ -> False
        else case grammarV1SourceBorrowClosure emptyStaticContext root fn of
          Nothing -> True
          _ -> False
  assert result "adapter noncompetence was confused with source acceptance"

checkBorrow :: Text -> Either String ()
checkBorrow input = do
  run <- borrow input
  assert (verifyBorrowCaptureCuts run == Right ())
    "native loan/capture correspondence failed"
  let before = borrowInitial run
  case (borrowCuts run, borrowStarted run, borrowClosed run) of
    ([start, loaned, closed], Just active, Just ended) -> do
      assert (borrowOutcome run == Right () &&
              borrowFailureStage run == Nothing &&
              borrowExtent run /= EscapingClosure &&
              start == before && active == loaned &&
              ended == closed && ended == before)
        "valid scoped loan was not closed at the exact owner"
      assert (Core.unrestrictedBindings active == Core.unrestrictedBindings before &&
              Core.affineBindings active == Core.affineBindings before &&
              Core.linearBindings active == Core.linearBindings before &&
              Set.size (Core.sharedLoans active) == 1 &&
              Set.null (Core.sharedLoans closed))
        "native borrowed context altered other resource zones"
    _ -> Left "accepted scoped capture had wrong native context cut count"

checkBorrowFailure :: Text -> SourceClosureFailureStage
                   -> (SourceClosureError -> Bool) -> Either String ()
checkBorrowFailure input stage matches = do
  run <- borrow input
  assert (verifyBorrowCaptureCuts run == Right ())
    "native rejected-loan replay disagreed"
  case (borrowCuts run, borrowStarted run) of
    ([initial, loaned], Just begun) ->
      assert (initial == borrowInitial run && loaned == begun &&
              borrowFailureStage run == Just stage &&
              borrowClosed run == Nothing &&
              either matches (const False) (borrowOutcome run))
        "scoped capture failure invented a loan-close successor"
    _ -> Left "wrong successful native loan prefix on rejection"

mutations :: Text -> Text -> Text -> Either String ()
mutations linear duplicate scoped = do
  good <- direct linear
  dup <- direct duplicate
  loan <- borrow scoped
  assert (verifyDirectCaptureCuts good == Right () &&
          verifyDirectCaptureCuts dup == Right () &&
          verifyBorrowCaptureCuts loan == Right ())
    "baseline CORR-1 source witnesses disagree"
  let start = directInitial good
      fakeCuts = good { directCuts = [start, start] }
      fakeFinal = good { directFinal = Just start }
      fakeSummary = good { directSummary = Nothing }
      fakeStage = good { directFailureStage = Just ClosureNativeUse }
      fakeDup = dup { directFinal = Just (directInitial dup) }
      fakeLoanClosed = loan { borrowClosed = Nothing }
      fakeLoanCuts = loan { borrowCuts = [borrowInitial loan] }
      fakeLoanExtent = loan { borrowExtent = EscapingClosure }
  assert (all (== Left DirectCutOrErrorMismatch)
            [verifyDirectCaptureCuts fakeCuts, verifyDirectCaptureCuts fakeFinal,
             verifyDirectCaptureCuts fakeSummary, verifyDirectCaptureCuts fakeStage,
             verifyDirectCaptureCuts fakeDup])
    "forged direct owner state, failure stage or summary was accepted"
  assert (all (== Left BorrowCutOrErrorMismatch)
            [verifyBorrowCaptureCuts fakeLoanClosed, verifyBorrowCaptureCuts fakeLoanCuts,
             verifyBorrowCaptureCuts fakeLoanExtent])
    "forged scoped loan result or extent was accepted"

main :: IO ()
main = do
  let load key = TextIO.readFile
        ("test/fixtures/fsem01-source-closure-capture-v1/" ++ key ++ ".phil")
  files <- mapM load
    ["direct-linear","direct-mixed","direct-flag","direct-flag-repeat",
     "direct-renamed","duplicate-linear","weakened-mode","unknown-capture",
     "closure-param-shadow","wrong-nominal","recursive-source",
     "local-borrow","derived-borrow","escaped-borrow","wrong-borrow-mode",
     "wrong-borrow-view"]
  let result = case files of
        [linear,mixed,flag,repeatFlag,renamed,duplicate,weak,unknown,shadow,
         nominal,recursive,local,derived,escaped,wrongMode,wrongView] -> do
          checkDirect linear 1 True
          checkDirect mixed 2 True
          checkDirect flag 1 False
          checkDirect repeatFlag 2 False
          checkDirect renamed 2 True
          checkDirectFailure duplicate ClosureCaptureValidation (\e -> case e of
            SourceClosureCaptureError (DuplicateRestrictedCapture _ _) -> True
            _ -> False)
          checkDirectFailure weak ClosureModeValidation
            (== SourceClosureModeMismatch Linear Unrestricted)
          checkLexicalFailure unknown (\e -> case e of
            SourceClosureBinderError (GrammarV1BinderNotInScope _) -> True
            _ -> False)
          checkLexicalFailure shadow (\e -> case e of
            SourceClosureBinderError (GrammarV1ActiveShadowing _ _) -> True
            _ -> False)
          checkOutOfFragment nominal True
          checkOutOfFragment recursive True
          checkBorrow local
          checkBorrow derived
          checkBorrowFailure escaped ClosureLoanScope (\e -> case e of
            SourceClosureScopeError (EscapingClosureCapturesScopedLoan _ key _) ->
              case key of CaptureOccurrenceKey _ -> True
            _ -> False)
          checkBorrowFailure wrongMode ClosureModeValidation
            (== SourceClosureModeMismatch Unrestricted Linear)
          checkOutOfFragment wrongView False
          mutations linear duplicate local
        _ -> Left "source specimen list changed arity"
  case result of
    Right () -> putStrLn
      "PASS: 16 parsed C-1 source specimens, native Γ/A/Δ/loan cuts, precise failure stages, eight forged-evidence refusals"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
