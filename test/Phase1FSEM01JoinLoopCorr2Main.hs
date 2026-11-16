{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 CORR-2: independently replay *bounded* source-checked
-- join/loop native resource cuts. This is neither a general source
-- evaluator nor a Haskell-to-Rocq implementation-refinement theorem.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..)
  , SourceBranchBorrowObservation (..), SourceScopedIfJoinRun (..)
  , SourceLinearLoopRun (..), SourceBoolJoinInvariant (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceScopedBorrowJoin
  ( GrammarV1ScopedBorrowJoinTrace (..)
  , grammarV1CheckedScopedBorrowJoinTrace )
import Phil.Surface.GrammarV1.SourceLinearLoopTransfer
  ( GrammarV1LinearLoopTrace (..)
  , grammarV1CheckedLinearLoopTransferTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

check :: Bool -> String -> Either String ()
check ok message = if ok then Right () else Left message

native :: Show err => Either err a -> Either String a
native = either (Left . show) Right

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

cutContext :: BorrowTraceCheckpoint -> Core.ResourceContext
cutContext cut = Core.ResourceContext
  (traceUnrestrictedOwners cut) (traceAffineOwners cut)
  (traceLinearOwners cut) (traceActiveLoans cut)

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-corr2" source)
  case grammarV1TopLevelDecls file of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("unexpected declaration: " ++ show other)
    other -> Left ("expected one function, got " ++ show (length other))

joinSource :: Text -> Either String GrammarV1ScopedBorrowJoinTrace
joinSource source = do
  fn <- parseOne source
  case grammarV1CheckedScopedBorrowJoinTrace emptyStaticContext
         (DeclarationKey "decl.fsem01.scoped-loan-join.choose") fn of
    Just (Right t) -> Right t
    other -> Left ("not in checked scoped-join fragment: " ++ show other)

loopSource :: Text -> Either String GrammarV1LinearLoopTrace
loopSource source = do
  fn <- parseOne source
  case grammarV1CheckedLinearLoopTransferTrace emptyStaticContext
         (DeclarationKey "decl.fsem01.l2.cycle") fn of
    Just (Right t) -> Right t
    other -> Left ("not in checked linear-loop fragment: " ++ show other)

joinBefore :: GrammarV1ScopedBorrowJoinTrace -> Core.ResourceContext
joinBefore t = Core.ResourceContext
  (Map.singleton (name (scopedBorrowJoinFlagBinder t)) TyBool)
  Map.empty (Map.singleton (name (scopedBorrowJoinPayloadBinder t)) bytes8)
  Set.empty

-- The source binder fixes which owner and view each actual loan belongs to.
-- The four resource collections are reconstructed from independent Core
-- operations, never from trace labels alone.
closedJoinLoan :: Core.ResourceContext -> Name -> Name
  -> SourceBranchBorrowObservation -> Either String ()
closedJoinLoan initial owner view obs = do
  loaned <- native (Core.startSharedLoan owner initial)
  closed <- native (Core.endSharedLoan owner loaned)
  let cuts = sourceBranchBorrowCuts obs
  check (sourceBranchBorrowOutcome obs == Right () &&
         map tracePhase cuts ==
           [TraceBeforeLoan,TraceLoanStarted,TraceBodyResult False,TraceLoanClosed] &&
         all (\cut -> traceOwnerName cut == owner &&
                      traceViewName cut == view) cuts &&
         map cutContext cuts == [initial,loaned,loaned,closed] &&
         closed == initial)
    "source join loan was not independently closed at exact native cuts"

joinSuccess :: GrammarV1ScopedBorrowJoinTrace -> Either String ()
joinSuccess t = do
  let initial = joinBefore t
      owner = name (scopedBorrowJoinPayloadBinder t)
      flag = name (scopedBorrowJoinFlagBinder t)
      run = scopedBorrowJoinRun t
      left = scopedBorrowJoinThenLoan t
      right = scopedBorrowJoinElseLoan t
      verifyArm view observation = case (view,observation) of
        (Nothing,Nothing) -> Right ()
        (Just v,Just obs) -> closedJoinLoan initial owner (name v) obs
        _ -> Left "source borrow view and production observation disagree"
  check (owner /= flag &&
         scopedIfJoinBefore run == Just initial &&
         scopedIfJoinOutcome run == scopedBorrowJoinOutcome t)
    "join initial source identities or ordinary checker outcome diverged"
  verifyArm (scopedBorrowJoinThenView t) left
  verifyArm (scopedBorrowJoinElseView t) right
  joined <- native (Core.joinContinuing [initial,initial])
  check (scopedIfJoinThenRaw run == [initial] &&
         scopedIfJoinThenPruned run == [initial] &&
         scopedIfJoinElseRaw run == [initial] &&
         scopedIfJoinElsePruned run == [initial] &&
         scopedIfJoinJoined run == Just joined &&
         joined == initial &&
         case scopedBorrowJoinOutcome t of
           Right _ -> True
           Left _ -> False)
    "accepted continuing join invented, dropped or changed a Core cut"

data JoinFailure = EscapeLeft | EscapeRight | MoveBorrowed
  deriving (Eq, Show)

joinRejected :: JoinFailure -> GrammarV1ScopedBorrowJoinTrace
  -> Either String ()
joinRejected kind t = do
  let initial = joinBefore t
      owner = name (scopedBorrowJoinPayloadBinder t)
      run = scopedBorrowJoinRun t
      first = kind /= EscapeRight
      selected = if first
        then scopedBorrowJoinThenLoan t else scopedBorrowJoinElseLoan t
      selectedView = if first
        then scopedBorrowJoinThenView t else scopedBorrowJoinElseView t
  loaned <- native (Core.startSharedLoan owner initial)
  obs <- maybe (Left "rejected source has no original loan observation") Right
    selected
  view <- maybe (Left "rejected source has no scoped view") (Right . name)
    selectedView
  let cuts = sourceBranchBorrowCuts obs
      expectedPhases = case kind of
        MoveBorrowed -> [TraceBeforeLoan,TraceLoanStarted]
        _ -> [TraceBeforeLoan,TraceLoanStarted,
              TraceBodyResult True,TraceEscapeRejected]
      expectedContexts = case kind of
        MoveBorrowed -> [initial,loaned]
        _ -> [initial,loaned,loaned,loaned]
  check (map tracePhase cuts == expectedPhases &&
         map cutContext cuts == expectedContexts &&
         all (\cut -> traceOwnerName cut == owner &&
                      traceViewName cut == view) cuts)
    "failed join fabricated a loan-close state or changed the failure prefix"
  case (sourceBranchBorrowOutcome obs,scopedBorrowJoinOutcome t) of
    (Left observed,Left original) -> do
      check (observed == original &&
             scopedIfJoinOutcome run == Left original)
        "join failure payload differs from actual source checker error"
      case kind of
        MoveBorrowed -> do
          check (Core.consumeLinear owner loaned ==
                   Left (Core.OwnerBorrowed owner) &&
                 surfaceErrorClass original == StructuralUse &&
                 surfaceErrorDetail original ==
                   Text.pack (show (Core.OwnerBorrowed owner)))
            "borrowed owner move lost exact native error"
        _ -> check (surfaceErrorClass original == BorrowEscape &&
                    surfaceErrorDetail original ==
                      "shared view escapes its lexical scope")
               "escaped view lost the exact source error"
    other -> Left ("source accepted a rejected join: " ++ show other)
  check (scopedIfJoinBefore run == Just initial &&
         scopedIfJoinJoined run == Nothing &&
         null (scopedIfJoinElseRaw run) &&
         null (scopedIfJoinElsePruned run) &&
         if first
           then null (scopedIfJoinThenRaw run) &&
                null (scopedIfJoinThenPruned run)
           else scopedIfJoinThenRaw run == [initial] &&
                scopedIfJoinThenPruned run == [initial])
    "rejected branch invented the partner branch or continuing successor"

loopBefore :: GrammarV1LinearLoopTrace -> Core.ResourceContext
loopBefore t = Core.ResourceContext
  (Map.singleton (name (linearLoopFlagBinder t)) TyBool)
  Map.empty (Map.fromList $
    (name (linearLoopPayloadBinder t),bytes8) :
    case (linearLoopAlternateBinder t,linearLoopAlternateType t) of
      (Just alt,Just ty) -> [(name alt,ty)]
      _ -> [])
  Set.empty

-- Independently derive the exact entry, new header, consumed backedge and
-- re-entry contexts using the exported normative Core resource operations.
loopPrefix :: GrammarV1LinearLoopTrace ->
  Either String (Core.ResourceContext,Core.ResourceContext,
                 Core.ResourceContext,Core.ResourceContext)
loopPrefix t = do
  let initial = loopBefore t
      old = name (linearLoopPayloadBinder t)
      slot = name (linearLoopHeaderBinder t)
  check (name (linearLoopEntryBinder t) == old &&
         old /= slot && old /= name (linearLoopFlagBinder t) &&
         linearLoopHeaderCheckedMode t == CheckedTypeMode bytes8 Linear)
    "loop declaration-rooted owner, header or type did not match source"
  (ty,spent) <- native (Core.consumeLinear old initial)
  header <- native (Core.insertBinding Linear slot ty spent)
  (spentTy,afterBackedge) <- native (Core.consumeLinear slot header)
  check (ty == bytes8 && spentTy == ty)
    "the native header did not preserve its source checked type"
  Right (initial,spent,header,afterBackedge)

closedLoopLoan :: GrammarV1LinearLoopTrace
  -> Core.ResourceContext -> Either String ()
closedLoopLoan t header = do
  let run = linearLoopNativeRun t
      cuts = sourceLinearLoopLoanCuts run
      owner = name (linearLoopHeaderBinder t)
  case linearLoopBorrowViewBinder t of
    Nothing -> check (null cuts && sourceLinearLoopAfterLoan run == Nothing)
      "loop without a borrow fabricated scoped loan observations"
    Just view -> do
      loaned <- native (Core.startSharedLoan owner header)
      closed <- native (Core.endSharedLoan owner loaned)
      check (map tracePhase cuts ==
               [TraceBeforeLoan,TraceLoanStarted,
                TraceBodyResult False,TraceLoanClosed] &&
             all (\cut -> traceOwnerName cut == owner &&
                          traceViewName cut == name view) cuts &&
             map cutContext cuts == [header,loaned,loaned,closed] &&
             closed == header && sourceLinearLoopAfterLoan run == Just closed &&
             Core.consumeLinear owner loaned ==
               Left (Core.OwnerBorrowed owner) &&
             Core.joinContinuing [header,loaned] ==
               Left (Core.EscapingLoans (Set.singleton owner)))
        "loop loan crossed the backedge or altered real resource cuts"

loopSuccess :: GrammarV1LinearLoopTrace -> Either String ()
loopSuccess t = do
  (initial,spent,header,afterBackedge) <- loopPrefix t
  let run = linearLoopNativeRun t
      slot = name (linearLoopHeaderBinder t)
  rebound <- native (Core.insertBinding Linear slot bytes8 afterBackedge)
  reentered <- native (Core.joinContinuing [header,rebound])
  closedLoopLoan t header
  check (linearLoopInvariantProof t == SourceBoolInvariantProvenTrue &&
         name (linearLoopBackedgeBinder t) == slot &&
         sourceLinearLoopBefore run == Just initial &&
         sourceLinearLoopEntryConsumed run == Just spent &&
         sourceLinearLoopHeaderBound run == Just header &&
         sourceLinearLoopBackedgeConsumed run == Just afterBackedge &&
         sourceLinearLoopBackedgeRebound run == Just rebound &&
         sourceLinearLoopReentered run == Just reentered &&
         sourceLinearLoopEntryType run == Just (Linear,bytes8) &&
         sourceLinearLoopBackedgeType run == Just (Linear,bytes8) &&
         sourceLinearLoopOutcome run == Right () &&
         linearLoopCheckedOutcome t == Right () &&
         reentered == header &&
         Core.consumeLinear (name (linearLoopPayloadBinder t)) header ==
           Left (Core.UnknownBinding (name (linearLoopPayloadBinder t))))
    "successful loop move/rebind/rejoin was not native-prefix exact"

data LoopFailure = StaleOwner | DuplicateHeader | FalseInvariant
  deriving (Eq, Show)

loopRejected :: LoopFailure -> GrammarV1LinearLoopTrace -> Either String ()
loopRejected failure t = do
  (initial,spent,header,_) <- loopPrefix t
  let run = linearLoopNativeRun t
      old = name (linearLoopPayloadBinder t)
      slot = name (linearLoopHeaderBinder t)
      noneLater = sourceLinearLoopBackedgeRebound run == Nothing &&
                  sourceLinearLoopReentered run == Nothing
  check (sourceLinearLoopBefore run == Just initial &&
         sourceLinearLoopEntryConsumed run == Just spent &&
         sourceLinearLoopHeaderBound run == Just header &&
         sourceLinearLoopEntryType run == Just (Linear,bytes8) &&
         null (sourceLinearLoopLoanCuts run) &&
         sourceLinearLoopAfterLoan run == Nothing && noneLater &&
         sourceLinearLoopOutcome run == linearLoopCheckedOutcome t)
    "rejected loop invented a successor or changed its source error"
  err <- case linearLoopCheckedOutcome t of
    Left errorValue -> Right errorValue
    Right () -> Left "source negative unexpectedly accepted by production"
  case failure of
    StaleOwner -> check
      (name (linearLoopBackedgeBinder t) == old &&
       Core.consumeLinear old header == Left (Core.UnknownBinding old) &&
       sourceLinearLoopBackedgeConsumed run == Nothing &&
       surfaceErrorClass err == StructuralUse &&
       surfaceErrorDetail err == "unknown or consumed binding: " <> unName old)
      "stale predecessor did not produce exact StructuralUse error and prefix"
    DuplicateHeader -> do
      alt <- maybe (Left "duplicate fixture lacks an alternate source owner")
        (Right . name) (linearLoopAlternateBinder t)
      (ty,after) <- native (Core.consumeLinear alt header)
      check (ty == bytes8 &&
             name (linearLoopBackedgeBinder t) == alt &&
             sourceLinearLoopBackedgeConsumed run == Just after &&
             sourceLinearLoopBackedgeType run == Just (Linear,bytes8) &&
             Core.insertBinding Linear slot bytes8 after ==
               Left (Core.DuplicateBinding slot) &&
             surfaceErrorClass err == StructuralUse &&
             surfaceErrorDetail err ==
               Text.pack (show (Core.DuplicateBinding slot)))
        "same-width competing owner was rebound over a live header"
    FalseInvariant -> check
      (linearLoopInvariantProof t == SourceBoolInvariantUnproved &&
       sourceLinearLoopBackedgeConsumed run == Nothing &&
       surfaceErrorClass err == MissingEvidence &&
       surfaceErrorDetail err ==
         "loop invariant has no checked proof for this bounded source backedge")
      "unproved source invariant was silently accepted"

tamper :: String -> Either String () -> Either String ()
tamper description result =
  check (case result of Left _ -> True; Right () -> False)
    ("forged production cut or error was accepted: " ++ description)

main :: IO ()
main = do
  let j filename = TextIO.readFile
        ("test/fixtures/fsem01-scoped-borrow-join-v1/" ++ filename ++ ".phil")
      l filename = TextIO.readFile
        ("test/fixtures/fsem01-linear-loop-transfer-v1/" ++ filename ++ ".phil")
      b filename = TextIO.readFile
        ("test/fixtures/fsem01-scoped-linear-loop-loan-v1/" ++ filename ++ ".phil")
  joinBoth <- j "accepted-both"
  joinLeft <- j "accepted-left"
  escapeLeft <- j "escape-left"
  escapeRight <- j "escape-right"
  moved <- j "move-while-loaned"
  loopOk <- l "accepted-owner"
  loopAlt <- l "accepted-same-width-spectator"
  loopStale <- l "stale-original-owner"
  loopDuplicate <- l "duplicate-live-header-owner"
  loopUnproved <- l "unproved-invariant"
  loanOk <- b "accepted-closed"
  let result = do
        jBoth <- joinSource joinBoth
        jLeft <- joinSource joinLeft
        jEscapeLeft <- joinSource escapeLeft
        jEscapeRight <- joinSource escapeRight
        jMoved <- joinSource moved
        lOk <- loopSource loopOk
        lAlt <- loopSource loopAlt
        lStale <- loopSource loopStale
        lDuplicate <- loopSource loopDuplicate
        lUnproved <- loopSource loopUnproved
        lLoan <- loopSource loanOk
        joinSuccess jBoth
        joinSuccess jLeft
        joinRejected EscapeLeft jEscapeLeft
        joinRejected EscapeRight jEscapeRight
        joinRejected MoveBorrowed jMoved
        loopSuccess lOk
        loopSuccess lAlt
        loopSuccess lLoan
        loopRejected StaleOwner lStale
        loopRejected DuplicateHeader lDuplicate
        loopRejected FalseInvariant lUnproved
        let jRun = scopedBorrowJoinRun jBoth
            jBefore = joinBefore jBoth
            lRun = linearLoopNativeRun lOk
            lHeader = sourceLinearLoopHeaderBound lRun
            lBack = sourceLinearLoopBackedgeConsumed lRun
        tamper "joined foreign state" (joinSuccess
          jBoth { scopedBorrowJoinRun = jRun
            { scopedIfJoinJoined = Just
                jBefore { Core.linearBindings = Map.empty } } })
        tamper "left branch missing" (joinSuccess
          jBoth { scopedBorrowJoinRun = jRun
            { scopedIfJoinThenPruned = [] } })
        tamper "made-up loan close" (joinSuccess
          jBoth { scopedBorrowJoinThenLoan = Nothing })
        tamper "forged join error" (joinRejected EscapeLeft
          jEscapeLeft { scopedBorrowJoinRun =
            (scopedBorrowJoinRun jEscapeLeft)
              { scopedIfJoinOutcome =
                Right (SurfaceCheckResult "choose" []) } })
        tamper "header owner dropped" (loopSuccess
          lOk { linearLoopNativeRun = lRun
            { sourceLinearLoopHeaderBound =
                fmap (\ctx -> ctx { Core.linearBindings = Map.empty }) lHeader } })
        tamper "backedge cut dropped" (loopSuccess
          lOk { linearLoopNativeRun = lRun
            { sourceLinearLoopBackedgeConsumed = Nothing } })
        tamper "loan invented" (loopSuccess
          lOk { linearLoopNativeRun = lRun
            { sourceLinearLoopAfterLoan = lHeader } })
        tamper "invented rejected successor" (loopRejected StaleOwner
          lStale { linearLoopNativeRun =
            (linearLoopNativeRun lStale)
              { sourceLinearLoopReentered = lHeader } })
        tamper "foreign consumed owner" (loopSuccess
          lOk { linearLoopNativeRun = lRun
            { sourceLinearLoopBackedgeConsumed =
                fmap (\ctx -> ctx { Core.sharedLoans =
                  Set.singleton (name (linearLoopHeaderBinder lOk)) }) lBack } })
  case result of
    Left e -> putStrLn ("FAIL CORR-2: " ++ e) >> exitFailure
    Right () -> putStrLn
      "PASS CORR-2: 11 parsed source runs, exact Core join/loop/loan cuts and errors; 9 forged replay refusals"
