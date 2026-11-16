{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 CORR-3: independent full finite source-cut representation checks.
-- No global Haskell-to-Rocq implementation refinement is claimed.
module Main (main) where

import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), SourceBranchBorrowObservation (..)
  , SourceScopedIfJoinRun (..), SourceLinearLoopRun (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..))
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

data Snapshot = Snapshot
  { snapU :: [(Name,Ty)]
  , snapA :: [(Name,Ty)]
  , snapL :: [(Name,Ty)]
  , snapLoans :: [Name]
  } deriving (Eq,Show)

snapshot :: Core.ResourceContext -> Snapshot
snapshot context = Snapshot
  (Map.toAscList (Core.unrestrictedBindings context))
  (Map.toAscList (Core.affineBindings context))
  (Map.toAscList (Core.linearBindings context))
  (Set.toAscList (Core.sharedLoans context))

check :: Bool -> String -> Either String ()
check yes why = if yes then Right () else Left why

strictAsc :: Ord a => [a] -> Bool
strictAsc xs = and (zipWith (<) xs (drop 1 xs))

finiteLookup :: Eq a => a -> [(a,b)] -> Maybe b
finiteLookup _ [] = Nothing
finiteLookup key ((candidate,value):rest)
  | key == candidate = Just value
  | otherwise = finiteLookup key rest

-- Validate BEFORE Map/Set reification: those structures would otherwise
-- silently normalize duplicate or out-of-order input.
reify :: Snapshot -> Either String Core.ResourceContext
reify s = do
  let zones = [snapU s,snapA s,snapL s]
      keys = concatMap (map fst) zones
      restricted = Set.fromList (map fst (snapA s ++ snapL s))
  check (all (strictAsc . map fst) zones) "noncanonical binding order"
  check (strictAsc (snapLoans s)) "noncanonical loan order"
  check (Set.size (Set.fromList keys) == length keys)
    "duplicate owner across U/A/L zones"
  check (all (\owner -> Set.member owner restricted) (snapLoans s))
    "loan with no restricted source owner"
  Right (Core.ResourceContext
    (Map.fromList (snapU s)) (Map.fromList (snapA s))
    (Map.fromList (snapL s)) (Set.fromList (snapLoans s)))

-- Native finite analogue of the Rocq ExactFiniteRelation. Compare all
-- collections, then independent list lookup for present and absent names.
checkProjection :: String -> Core.ResourceContext -> Snapshot -> Either String ()
checkProjection label context s = do
  restored <- reify s
  check (restored == context) (label ++ ": finite projection changed context")
  let queries = Set.toAscList (Set.fromList
        (map fst (snapU s ++ snapA s ++ snapL s) ++
         snapLoans s ++ [Name "corr3-absent-a",Name "corr3-absent-b"]))
  forM_ queries $ \key ->
    check
      (finiteLookup key (snapU s) ==
          Map.lookup key (Core.unrestrictedBindings context) &&
       finiteLookup key (snapA s) ==
          Map.lookup key (Core.affineBindings context) &&
       finiteLookup key (snapL s) ==
          Map.lookup key (Core.linearBindings context) &&
       elem key (snapLoans s) ==
          Set.member key (Core.sharedLoans context))
      (label ++ ": finite lookup disagreed at " ++ show key)

cutContext :: BorrowTraceCheckpoint -> Core.ResourceContext
cutContext cut = Core.ResourceContext
  (traceUnrestrictedOwners cut) (traceAffineOwners cut)
  (traceLinearOwners cut) (traceActiveLoans cut)

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-corr3" source)
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
    Just (Right run) -> Right run
    other -> Left ("source join adapter noncompetent: " ++ show other)

loopSource :: Text -> Either String GrammarV1LinearLoopTrace
loopSource source = do
  fn <- parseOne source
  case grammarV1CheckedLinearLoopTransferTrace emptyStaticContext
         (DeclarationKey "decl.fsem01.l2.cycle") fn of
    Just (Right run) -> Right run
    other -> Left ("source loop adapter noncompetent: " ++ show other)

joinCuts :: GrammarV1ScopedBorrowJoinTrace -> [Core.ResourceContext]
joinCuts trace =
  let run = scopedBorrowJoinRun trace
      loans = maybe [] (map cutContext . sourceBranchBorrowCuts)
  in catMaybes [scopedIfJoinBefore run,scopedIfJoinJoined run] ++
     scopedIfJoinThenRaw run ++ scopedIfJoinThenPruned run ++
     scopedIfJoinElseRaw run ++ scopedIfJoinElsePruned run ++
     loans (scopedBorrowJoinThenLoan trace) ++
     loans (scopedBorrowJoinElseLoan trace)

loopCuts :: GrammarV1LinearLoopTrace -> [Core.ResourceContext]
loopCuts trace =
  let run = linearLoopNativeRun trace
  in catMaybes
       [sourceLinearLoopBefore run,sourceLinearLoopEntryConsumed run,
        sourceLinearLoopHeaderBound run,sourceLinearLoopAfterLoan run,
        sourceLinearLoopBackedgeConsumed run,sourceLinearLoopBackedgeRebound run,
        sourceLinearLoopReentered run] ++
     map cutContext (sourceLinearLoopLoanCuts run)

checkJoin :: GrammarV1ScopedBorrowJoinTrace -> Either String ()
checkJoin t = do
  let run = scopedBorrowJoinRun t
      owner = grammarV1ResolvedBinderCoreName (scopedBorrowJoinPayloadBinder t)
  check (scopedIfJoinOutcome run == scopedBorrowJoinOutcome t &&
         not (null (joinCuts t)))
    "source join result and observed replay diverged"
  forM_ (zip [(0::Int)..] (joinCuts t)) $ \(i,ctx) ->
    checkProjection ("source join cut " ++ show i) ctx (snapshot ctx)
  case scopedBorrowJoinOutcome t of
    Right _ -> do
      joined <- maybe (Left "accepted source join has no joined cut") Right
        (scopedIfJoinJoined run)
      check (Map.lookup owner (Core.linearBindings joined) ==
               Just (TyBytes (RefNat 8)) &&
             Set.null (Core.sharedLoans joined))
        "accepted source join lost finite owner/closed-loan projection"
    Left err ->
      check (scopedIfJoinJoined run == Nothing &&
             elem (surfaceErrorClass err) [BorrowEscape,StructuralUse])
        "rejected join invented successor or changed error class"

checkLoop :: GrammarV1LinearLoopTrace -> Either String ()
checkLoop t = do
  let run = linearLoopNativeRun t
      old = grammarV1ResolvedBinderCoreName (linearLoopPayloadBinder t)
      slot = grammarV1ResolvedBinderCoreName (linearLoopHeaderBinder t)
  check (sourceLinearLoopOutcome run == linearLoopCheckedOutcome t &&
         not (null (loopCuts t)) && old /= slot)
    "source loop outcome, owner identity or replay diverged"
  forM_ (zip [(0::Int)..] (loopCuts t)) $ \(i,ctx) ->
    checkProjection ("source loop cut " ++ show i) ctx (snapshot ctx)
  header <- maybe (Left "source loop never reached checked header") Right
    (sourceLinearLoopHeaderBound run)
  check (Map.notMember old (Core.linearBindings header) &&
         Map.lookup slot (Core.linearBindings header) ==
           Just (TyBytes (RefNat 8)))
    "source loop original owner resurrected or header not installed"
  case linearLoopCheckedOutcome t of
    Right () -> do
      reentered <- maybe (Left "accepted loop lacks a reentry cut") Right
        (sourceLinearLoopReentered run)
      check (reentered == header &&
             Set.null (Core.sharedLoans reentered) &&
             Map.notMember old (Core.linearBindings reentered))
        "accepted loop finite relation changed the checked header"
    Left err ->
      check (sourceLinearLoopReentered run == Nothing &&
             sourceLinearLoopBackedgeRebound run == Nothing &&
             elem (surfaceErrorClass err) [StructuralUse,MissingEvidence])
        "rejected loop invented continuation or changed rejection class"

mustReject :: String -> Either String () -> Either String ()
mustReject label result =
  check (case result of Left _ -> True; Right () -> False)
    ("CORR-3 accepted forged finite source checkpoint: " ++ label)

main :: IO ()
main = do
  let j name = TextIO.readFile
        ("test/fixtures/fsem01-scoped-borrow-join-v1/" ++ name ++ ".phil")
      l name = TextIO.readFile
        ("test/fixtures/fsem01-linear-loop-transfer-v1/" ++ name ++ ".phil")
      b name = TextIO.readFile
        ("test/fixtures/fsem01-scoped-linear-loop-loan-v1/" ++ name ++ ".phil")
  sourceJoins <- mapM j
    ["accepted-both","accepted-left","escape-left",
     "escape-right","move-while-loaned"]
  sourceLoops <- mapM l
    ["accepted-owner","accepted-same-width-spectator",
     "stale-original-owner","duplicate-live-header-owner","unproved-invariant"]
  sourceLoan <- b "accepted-closed"
  let result = do
        joins <- mapM joinSource sourceJoins
        loops <- mapM loopSource (sourceLoops ++ [sourceLoan])
        mapM_ checkJoin joins
        mapM_ checkLoop loops
        base <- case joins of
          (good:_) -> maybe (Left "missing initial join source cut") Right
            (scopedIfJoinBefore (scopedBorrowJoinRun good))
          [] -> Left "missing positive join source"
        alt <- case loops of
          (_:two:_) -> maybe (Left "missing two-owner loop source cut") Right
            (sourceLinearLoopBefore (linearLoopNativeRun two))
          _ -> Left "missing spectator loop fixture"
        let s = snapshot base
            two = snapshot alt
        mustReject "duplicate owner" (checkProjection "duplicate" base
          (s { snapL = snapL s ++ snapL s }))
        mustReject "owner omitted" (checkProjection "omitted" base
          (s { snapL = [] }))
        mustReject "cross-mode duplicate" (checkProjection "duplicate zone" base
          (s { snapA = snapL s }))
        mustReject "orphaned loan" (checkProjection "orphaned" base
          (s { snapLoans = [Name "corr3-foreign-loan"] }))
        mustReject "loan fabricated" (checkProjection "fake loan" base
          (s { snapLoans = map fst (snapL s) }))
        mustReject "reversed two-owner order" (checkProjection "order" alt
          (two { snapL = reverse (snapL two) }))
        mustReject "wrong checked type" (checkProjection "type" base
          (s { snapL = [(key,TyBool) | (key,_) <- snapL s] }))
        mustReject "spurious unrestricted" (checkProjection "extra U" base
          (s { snapU = [(Name "corr3-spurious",TyBool)] }))
        mustReject "spurious affine" (checkProjection "extra A" base
          (s { snapA = [(Name "corr3-spurious",TyBool)] }))
  case result of
    Left err -> putStrLn ("FAIL CORR-3: " ++ err) >> exitFailure
    Right () -> putStrLn
      "PASS CORR-3: 11 real source join/loop witnesses, all U/A/L/loan cuts, nine forged finite projections rejected"
