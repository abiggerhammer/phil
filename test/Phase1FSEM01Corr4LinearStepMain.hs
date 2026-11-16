{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 CORR-4: independent finite-list Linear consume/insert decisions
-- compared with actual Core operations at six checked Grammar-v1 loop cuts.
-- Finite conformance, not universal Haskell <-> Rocq refinement.
module Main (main) where

import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), SourceLinearLoopRun (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceLinearLoopTransfer
  ( GrammarV1LinearLoopTrace (..)
  , grammarV1CheckedLinearLoopTransferTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

data Snapshot = Snapshot
  { snapU :: [(Name, Ty)]
  , snapA :: [(Name, Ty)]
  , snapL :: [(Name, Ty)]
  , snapLoans :: [Name]
  } deriving (Eq, Show)

snapshot :: Core.ResourceContext -> Snapshot
snapshot context = Snapshot
  (Map.toAscList (Core.unrestrictedBindings context))
  (Map.toAscList (Core.affineBindings context))
  (Map.toAscList (Core.linearBindings context))
  (Set.toAscList (Core.sharedLoans context))

check :: Bool -> String -> Either String ()
check yes message = if yes then Right () else Left message

strictAsc :: Ord a => [a] -> Bool
strictAsc values = and (zipWith (<) values (drop 1 values))

allNames :: Snapshot -> [Name]
allNames snap = map fst (snapU snap ++ snapA snap ++ snapL snap)

valid :: Snapshot -> Bool
valid snap =
  let zones = [snapU snap, snapA snap, snapL snap]
      names = allNames snap
      restricted = map fst (snapA snap ++ snapL snap)
  in all (strictAsc . map fst) zones &&
     strictAsc (snapLoans snap) &&
     Set.size (Set.fromList names) == length names &&
     all (\owner -> elem owner restricted) (snapLoans snap)

-- Generated finite steps may prepend a new key rather than sorting it.
-- Reject duplicate/cross-zone owners before comparing an output.
unique :: Snapshot -> Bool
unique snap =
  let names = allNames snap
      loans = snapLoans snap
  in Set.size (Set.fromList names) == length names &&
     Set.size (Set.fromList loans) == length loans &&
     all (\owner -> elem owner (map fst (snapA snap ++ snapL snap))) loans

finiteLookup :: Eq a => a -> [(a,b)] -> Maybe b
finiteLookup _ [] = Nothing
finiteLookup key ((candidate,value):rest)
  | key == candidate = Just value
  | otherwise = finiteLookup key rest

finiteConsume :: Name -> Snapshot -> Either Core.CheckError (Ty,Snapshot)
finiteConsume owner snap
  | elem owner (snapLoans snap) = Left (Core.OwnerBorrowed owner)
  | Just ty <- finiteLookup owner (snapL snap) =
      Right (ty,snap { snapL = filter ((/= owner) . fst) (snapL snap) })
  | Just _ <- finiteLookup owner (snapU snap) =
      Left (Core.WrongStructuralMode owner Linear Unrestricted)
  | Just _ <- finiteLookup owner (snapA snap) =
      Left (Core.WrongStructuralMode owner Linear Affine)
  | otherwise = Left (Core.UnknownBinding owner)

finiteInsert :: Name -> Ty -> Snapshot
  -> Either Core.CheckError Snapshot
finiteInsert owner ty snap
  | elem owner (allNames snap) = Left (Core.DuplicateBinding owner)
  | otherwise = Right (snap { snapL = (owner,ty) : snapL snap })

-- Query keys are drawn from BOTH sides, including every actual Map/Set name
-- and independent absent probes: an extra or missing owner cannot hide.
checkProjection :: String -> Core.ResourceContext -> Snapshot
  -> Either String ()
checkProjection label context finite = do
  check (unique finite) (label ++ ": duplicate/invalid finite owner")
  let actual = snapshot context
      queries = Set.toAscList (Set.fromList
        (allNames finite ++ snapLoans finite ++
         allNames actual ++ snapLoans actual ++
         [Name "corr4-absent-a",Name "corr4-absent-b"]))
  forM_ queries $ \key ->
    check
      (finiteLookup key (snapU finite) ==
          Map.lookup key (Core.unrestrictedBindings context) &&
       finiteLookup key (snapA finite) ==
          Map.lookup key (Core.affineBindings context) &&
       finiteLookup key (snapL finite) ==
          Map.lookup key (Core.linearBindings context) &&
       elem key (snapLoans finite) ==
          Set.member key (Core.sharedLoans context))
      (label ++ ": finite/native projection differs at " ++ show key)

checkConsume :: String -> Name -> Core.ResourceContext
  -> Maybe Core.ResourceContext -> Either String ()
checkConsume label owner before reached = do
  let finite = snapshot before
  check (valid finite) (label ++ ": input is not canonical")
  case (finiteConsume owner finite, Core.consumeLinear owner before) of
    (Left expected,Left observed) ->
      check (expected == observed && reached == Nothing)
        (label ++ ": native diagnostic or failure prefix differs")
    (Right (fTy,fNext),Right (nTy,nNext)) -> do
      check (fTy == nTy && reached == Just nNext)
        (label ++ ": source/native success identity differs")
      checkProjection label nNext fNext
    other -> Left (label ++ ": finite/native consume mismatch: " ++ show other)

checkInsert :: String -> Name -> Ty -> Core.ResourceContext
  -> Maybe Core.ResourceContext -> Either String ()
checkInsert label owner ty before reached = do
  let finite = snapshot before
  check (valid finite) (label ++ ": input is not canonical")
  case (finiteInsert owner ty finite,
        Core.insertBinding Linear owner ty before) of
    (Left expected,Left observed) ->
      check (expected == observed && reached == Nothing)
        (label ++ ": native duplicate error or failure prefix differs")
    (Right fNext,Right nNext) -> do
      check (reached == Just nNext)
        (label ++ ": source/native inserted state differs")
      checkProjection label nNext fNext
    other -> Left (label ++ ": finite/native insert mismatch: " ++ show other)

cutContext :: BorrowTraceCheckpoint -> Core.ResourceContext
cutContext cut = Core.ResourceContext
  (traceUnrestrictedOwners cut) (traceAffineOwners cut)
  (traceLinearOwners cut) (traceActiveLoans cut)

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-corr4" source)
  case grammarV1TopLevelDecls file of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("unexpected declaration: " ++ show other)
    others -> Left ("expected one function, got " ++ show (length others))

loopSource :: Text -> Either String GrammarV1LinearLoopTrace
loopSource source = do
  fn <- parseOne source
  case grammarV1CheckedLinearLoopTransferTrace emptyStaticContext
         (DeclarationKey "decl.fsem01.l2.cycle") fn of
    Just (Right run) -> Right run
    other -> Left ("checked source loop adapter noncompetent: " ++ show other)

required :: String -> Maybe a -> Either String a
required label = maybe (Left ("missing real checker cut: " ++ label)) Right

checkLoop :: GrammarV1LinearLoopTrace -> Either String ()
checkLoop source = do
  let run = linearLoopNativeRun source
      old = grammarV1ResolvedBinderCoreName (linearLoopPayloadBinder source)
      slot = grammarV1ResolvedBinderCoreName (linearLoopHeaderBinder source)
      backedge = grammarV1ResolvedBinderCoreName (linearLoopBackedgeBinder source)
      bytes8 = TyBytes (RefNat 8)
  before <- required "before" (sourceLinearLoopBefore run)
  spent <- required "entry consumed" (sourceLinearLoopEntryConsumed run)
  header <- required "header bound" (sourceLinearLoopHeaderBound run)
  check (old /= slot && linearLoopCheckedOutcome source ==
           sourceLinearLoopOutcome run && valid (snapshot before))
    "source owner/success/failure identity mismatch"
  checkConsume "source entry move" old before (Just spent)
  checkInsert "source fresh header" slot bytes8 spent (Just header)
  case sourceLinearLoopLoanCuts run of
    [] -> Right ()
    [_beforeLoan, loanStarted, _bodyResult, _closed] ->
      checkConsume "source live-loan refusal"
        slot (cutContext loanStarted) Nothing
    other -> Left ("unexpected borrowed-source checkpoint sequence " ++
                   show (length other))
  case sourceLinearLoopBackedgeConsumed run of
    Just backSpent -> do
      checkConsume "source continuing actual" backedge header (Just backSpent)
      checkInsert "source backedge rebind" slot bytes8 backSpent
        (sourceLinearLoopBackedgeRebound run)
      case sourceLinearLoopBackedgeRebound run of
        Just rebound -> do
          check (sourceLinearLoopReentered run == Just header &&
                 Core.joinContinuing [header,rebound] == Right header)
            "source checked loop successor or join is not exact"
        Nothing ->
          check (sourceLinearLoopReentered run == Nothing)
            "duplicate-live-header invented a reentry"
    Nothing
      | backedge == old -> do
          checkConsume "stale original source owner" old header Nothing
          check (sourceLinearLoopReentered run == Nothing)
            "stale source owner invented a reentry"
      | otherwise ->
          check (sourceLinearLoopReentered run == Nothing &&
                 case sourceLinearLoopOutcome run of
                   Left _ -> True
                   Right _ -> False)
            "unproved invariant was silently treated as a resource step"

reject :: String -> Either String () -> Either String ()
reject label result =
  check (case result of Left _ -> True; Right () -> False)
    ("forged finite transition accepted: " ++ label)

main :: IO ()
main = do
  let path name =
        "test/fixtures/fsem01-linear-loop-transfer-v1/" ++ name ++ ".phil"
      loanPath =
        "test/fixtures/fsem01-scoped-linear-loop-loan-v1/accepted-closed.phil"
  sources <- mapM (TextIO.readFile . path)
    ["accepted-owner","accepted-same-width-spectator",
     "stale-original-owner","duplicate-live-header-owner",
     "unproved-invariant"]
  borrowed <- TextIO.readFile loanPath
  let outcome = do
        traces <- mapM loopSource (sources ++ [borrowed])
        mapM_ checkLoop traces
        good <- case traces of
          first : _ -> Right first
          [] -> Left "no real source traces"
        let nativeRun = linearLoopNativeRun good
        before <- required "forged projection before" (sourceLinearLoopBefore nativeRun)
        spent <- required "forged projection consumed"
          (sourceLinearLoopEntryConsumed nativeRun)
        header <- required "forged projection header"
          (sourceLinearLoopHeaderBound nativeRun)
        let s = snapshot before
            old = grammarV1ResolvedBinderCoreName (linearLoopPayloadBinder good)
            slot = grammarV1ResolvedBinderCoreName (linearLoopHeaderBinder good)
            forgedExtra = s { snapU = (Name "corr4-forged", TyBool) : snapU s }
        reject "extra binding at actual source cut"
          (checkProjection "forged extra" before forgedExtra)
        reject "omitted Linear owner"
          (checkProjection "missing Linear" before (s { snapL = [] }))
        reject "owner moved to wrong mode"
          (checkProjection "wrong mode" before (s { snapA = snapL s, snapL = [] }))
        reject "wrong checked type"
          (checkProjection "wrong type" before
            (s { snapL = [(key,TyBool) | (key,_) <- snapL s] }))
        reject "fabricated shared loan"
          (checkProjection "loan" before (s { snapLoans = [old] }))
        reject "duplicate linear key"
          (checkProjection "duplicate" before (s { snapL = snapL s ++ snapL s }))
        reject "tampered entry-consumed cut"
          (checkLoop (good { linearLoopNativeRun = nativeRun
            { sourceLinearLoopEntryConsumed =
                Just (spent { Core.linearBindings =
                  Map.singleton (Name "corr4-forged-entry") TyBool }) } }))
        reject "tampered header cut"
          (checkLoop (good { linearLoopNativeRun = nativeRun
            { sourceLinearLoopHeaderBound =
                Just (header { Core.linearBindings = Map.empty }) } }))
        checkConsume "synthetic consumed owner" old spent Nothing
        let x = Name "corr4-synthetic"
            unrestricted = Core.ResourceContext
              (Map.singleton x TyBool) Map.empty Map.empty Set.empty
            affine = Core.ResourceContext
              Map.empty (Map.singleton x TyBool) Map.empty Set.empty
            linear = Core.ResourceContext
              Map.empty Map.empty (Map.singleton x TyBool) Set.empty
            borrowedCtx = linear { Core.sharedLoans = Set.singleton x }
        checkConsume "wrong unrestricted mode" x unrestricted Nothing
        checkConsume "wrong affine mode" x affine Nothing
        checkConsume "missing linear owner" x Core.emptyContext Nothing
        checkConsume "borrowed linear owner" x borrowedCtx Nothing
        forM_ [unrestricted,affine,linear] $ \ctx ->
          checkInsert "duplicate in every mode" x TyBool ctx Nothing
        fresh <- either (Left . show) Right
          (Core.insertBinding Linear x TyBool Core.emptyContext)
        checkInsert "fresh owner" x TyBool Core.emptyContext (Just fresh)
        check (finiteConsume x (snapshot borrowedCtx) ==
                 Left (Core.OwnerBorrowed x))
          "loan did not precede the actual present linear owner"
        check (case finiteInsert slot (TyBytes (RefNat 8))
                          (snapshot header) of
                 Left (Core.DuplicateBinding _) -> True
                 _ -> False)
          "duplicate header was not refused before insertion"
  case outcome of
    Left why -> putStrLn ("FAIL CORR-4: " ++ why) >> exitFailure
    Right () -> putStrLn
      "PASS CORR-4: six real checked loop source traces, finite consume/insert vs native Core and exact error prefixes, forged-state and wrong-mode controls"
