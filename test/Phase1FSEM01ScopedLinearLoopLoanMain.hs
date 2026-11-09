{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 L-3: source-scoped loan must close before one Linear loop backedge.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name, RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..)
  , SourceLinearLoopRun (..) )
import Phil.Surface.Check.Types (RejectionClass (..), SurfaceCheckError (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceLinearLoopTransfer
  ( GrammarV1LinearLoopTrace (..), grammarV1CheckedLinearLoopTransferTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.l3.scoped-loop-loan"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne input = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-scoped-loop-loan" input)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("expected function, got " ++ show other)
    other -> Left ("expected one declaration, got " ++ show (length other))

checked :: Text -> Either String GrammarV1LinearLoopTrace
checked input = do
  fn <- parseOne input
  case grammarV1CheckedLinearLoopTransferTrace
    emptyStaticContext root fn of
      Just (Right trace) -> Right trace
      other -> Left ("source not in the checked L-3 fragment: " ++ show other)

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

contextBefore :: GrammarV1LinearLoopTrace -> Core.ResourceContext
contextBefore e = Core.ResourceContext
  { Core.unrestrictedBindings =
      Map.singleton (name (linearLoopFlagBinder e)) TyBool
  , Core.affineBindings = Map.empty
  , Core.linearBindings =
      Map.singleton (name (linearLoopPayloadBinder e)) bytes8
  , Core.sharedLoans = Set.empty
  }

contextHeader :: GrammarV1LinearLoopTrace -> Core.ResourceContext
contextHeader e = (contextBefore e)
  { Core.linearBindings =
      Map.singleton (name (linearLoopHeaderBinder e)) bytes8 }

assertCuts :: Name -> Name -> Name -> [BorrowTraceCheckpoint]
  -> Either String ()
assertCuts flag slot view cuts = do
  assert (map tracePhase cuts ==
    [TraceBeforeLoan, TraceLoanStarted,
     TraceBodyResult False, TraceLoanClosed])
    ("incorrect production loan start/body/close phases: " ++ show cuts)
  let loanSets = [Set.empty, Set.singleton slot, Set.singleton slot, Set.empty]
  assert (and (zipWith
    (\cut loans ->
      traceOwnerName cut == slot &&
      traceViewName cut == view &&
      traceUnrestrictedOwners cut == Map.singleton flag TyBool &&
      traceAffineOwners cut == Map.empty &&
      traceLinearOwners cut == Map.singleton slot bytes8 &&
      traceActiveLoans cut == loans)
    cuts loanSets))
    "borrow checkpoint was not the exact reached four-collection context"

accepted :: Text -> Either String ()
accepted input = do
  e <- checked input
  view <- maybe (Left "missing source-declared borrow view") Right
    (linearLoopBorrowViewBinder e)
  let flag = name (linearLoopFlagBinder e)
      slot = name (linearLoopHeaderBinder e)
      old = name (linearLoopPayloadBinder e)
      initial = contextBefore e
      header = contextHeader e
      spent = initial
        { Core.linearBindings = Map.empty }
      spentBackedge = header
        { Core.linearBindings = Map.empty }
      run = linearLoopNativeRun e
  assert (old /= slot && slot /= name view && old /= name view)
    "borrow view, old owner and header identities collided"
  assert (name (linearLoopEntryBinder e) == old &&
          name (linearLoopBackedgeBinder e) == slot)
    "source initial/backedge operands did not resolve exactly"
  assert (sourceLinearLoopBefore run == Just initial &&
          sourceLinearLoopEntryConsumed run == Just spent &&
          sourceLinearLoopHeaderBound run == Just header &&
          sourceLinearLoopAfterLoan run == Just header &&
          sourceLinearLoopBackedgeConsumed run == Just spentBackedge &&
          sourceLinearLoopBackedgeRebound run == Just header &&
          sourceLinearLoopReentered run == Just header &&
          sourceLinearLoopEntryType run == Just (Linear,bytes8) &&
          sourceLinearLoopBackedgeType run == Just (Linear,bytes8) &&
          sourceLinearLoopOutcome run == Right () &&
          linearLoopCheckedOutcome e == Right ())
    "successful borrow moved/rebound owner incorrectly or invented a context"
  assertCuts flag slot (name view) (sourceLinearLoopLoanCuts run)
  assert (Core.consumeLinear old initial == Right (bytes8,spent) &&
          Core.insertBinding Linear slot bytes8 spent == Right header &&
          Core.consumeLinear slot header == Right (bytes8,spentBackedge) &&
          Core.insertBinding Linear slot bytes8 spentBackedge == Right header &&
          Core.joinContinuing [header,header] == Right header)
    "direct production Core owner move/rejoin differed from traced source"
  loaned <- either (Left . show) Right (Core.startSharedLoan slot header)
  assert (Core.sharedLoans loaned == Set.singleton slot &&
          Core.consumeLinear slot loaned == Left (Core.OwnerBorrowed slot) &&
          Core.joinContinuing [header,loaned] ==
            Left (Core.EscapingLoans (Set.singleton slot)) &&
          Core.endSharedLoan slot loaned == Right header)
    "active loan was moved/joined or closed loan lost its exact resources"

rejected :: Text -> RejectionClass -> [BorrowTracePhase]
  -> Bool -> Either String ()
rejected input expected phases afterLoan = do
  e <- checked input
  let run = linearLoopNativeRun e
  assert (sourceLinearLoopBefore run == Just (contextBefore e) &&
          sourceLinearLoopEntryConsumed run /= Nothing &&
          sourceLinearLoopHeaderBound run == Just (contextHeader e) &&
          sourceLinearLoopAfterLoan run ==
            (if afterLoan then Just (contextHeader e) else Nothing) &&
          sourceLinearLoopBackedgeConsumed run == Nothing &&
          sourceLinearLoopBackedgeRebound run == Nothing &&
          sourceLinearLoopReentered run == Nothing &&
          linearLoopCheckedOutcome e == sourceLinearLoopOutcome run)
    "rejected loan invented a closed/backedge/reentry resource state"
  assert (map tracePhase (sourceLinearLoopLoanCuts run) == phases)
    ("rejected loan recorded wrong reached prefix: " ++ show run)
  case linearLoopCheckedOutcome e of
    Left err -> assert (surfaceErrorClass err == expected)
      ("wrong exact source rejection class: " ++ show err)
    Right () -> Left "source negative was accepted"

unsupported :: Text -> Either String ()
unsupported input = do
  fn <- parseOne input
  assert
    (case grammarV1CheckedLinearLoopTransferTrace
      emptyStaticContext root fn of
        Just (Right _) -> False
        _ -> True)
    "escaped/out-of-fragment loop-body source was accepted"

main :: IO ()
main = do
  let get key = TextIO.readFile
        ("test/fixtures/fsem01-scoped-linear-loop-loan-v1/" ++ key ++ ".phil")
  acceptedSources <- mapM get
    ["accepted-closed","accepted-uses-view","accepted-renamed"]
  leak <- get "escape-view-result"
  moved <- get "move-borrowed-owner"
  stale <- get "stale-source-owner"
  wrongMode <- get "unrestricted-borrow"
  wrongBackedge <- get "wrong-backedge"
  unproved <- get "unproved-invariant"
  escapedView <- get "view-after-scope"
  doubleBorrow <- get "two-borrows"
  let passed = do
        mapM_ accepted acceptedSources
        rejected leak BorrowEscape
          [TraceBeforeLoan,TraceLoanStarted,
            TraceBodyResult True,TraceEscapeRejected] False
        rejected moved StructuralUse
          [TraceBeforeLoan,TraceLoanStarted] False
        movedEvidence <- checked moved
        case linearLoopCheckedOutcome movedEvidence of
          Left err -> assert
            (surfaceErrorDetail err == Text.pack (show
              (Core.OwnerBorrowed (name (linearLoopHeaderBinder movedEvidence)))))
            "attempted move did not preserve the exact native OwnerBorrowed error"
          Right () -> Left "borrowed owner moved unexpectedly"
        rejected stale StructuralUse [] False
        rejected wrongMode BorrowEscape [TraceBeforeLoan] False
        rejected wrongBackedge TypeMismatch
          [TraceBeforeLoan,TraceLoanStarted,
            TraceBodyResult False,TraceLoanClosed] True
        rejected unproved MissingEvidence [] False
        unsupported escapedView
        unsupported doubleBorrow
  case passed of
    Right () -> putStrLn
      "PASS: 11 parsed L-3 fixtures; source scoped-loan lifecycle, exact four maps, blocked move/join, no fabricated rejected successor"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
