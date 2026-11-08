{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: finite-context conformance over real Haskell Core.Map/Set.
-- All four zones, actual operations and adversarial finite evidence.
module Main (main) where

import Control.Monad (foldM, forM_)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Context (ResourceContext (..), CheckError (..))
import qualified Phil.Core.Context as Core
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import System.Exit (exitFailure)

data FiniteSnapshot = FiniteSnapshot
  { snapUnrestricted :: [(Name, Ty)]
  , snapAffine :: [(Name, Ty)]
  , snapLinear :: [(Name, Ty)]
  , snapLoans :: [Name]
  } deriving (Eq, Show)

snapshot :: ResourceContext -> FiniteSnapshot
snapshot ctx = FiniteSnapshot
  (Map.toAscList (unrestrictedBindings ctx))
  (Map.toAscList (affineBindings ctx))
  (Map.toAscList (linearBindings ctx))
  (Set.toAscList (sharedLoans ctx))

assert :: Bool -> String -> Either String ()
assert yes message = if yes then Right () else Left message

ascending :: Ord a => [a] -> Bool
ascending xs = and (zipWith (<) xs (drop 1 xs))

-- Map.fromList must not silently repair malformed lists: refuse duplicate
-- names, unsorted zones, or loans without restricted owners first.
reify :: FiniteSnapshot -> Either String ResourceContext
reify snap = do
  let u = snapUnrestricted snap
      a = snapAffine snap
      l = snapLinear snap
      loans = snapLoans snap
      names = map fst (u ++ a ++ l)
      restricted = Set.fromList (map fst (a ++ l))
  assert (Set.size (Set.fromList names) == length names)
    "cross-zone or within-zone duplicate binding"
  assert (all (ascending . map fst) [u,a,l])
    "noncanonical binding order"
  assert (ascending loans) "duplicate/out-of-order loan"
  assert (all (\name -> Set.member name restricted) loans)
    "orphaned loan"
  Right ResourceContext
    { unrestrictedBindings = Map.fromList u
    , affineBindings = Map.fromList a
    , linearBindings = Map.fromList l
    , sharedLoans = Set.fromList loans
    }

-- Deliberately independent list lookup for the finite representation.
finiteLookup :: Name -> [(Name, Ty)] -> Maybe Ty
finiteLookup name xs = case xs of
  [] -> Nothing
  (key,ty):rest ->
    if key == name then Just ty else finiteLookup name rest

checkSnapshot :: String -> ResourceContext -> Either String ()
checkSnapshot label ctx = do
  let snap = snapshot ctx
      names = map fst
        (snapUnrestricted snap ++ snapAffine snap ++ snapLinear snap)
      queries = names ++ snapLoans snap ++
        [Name "absent-1", Name "absent-2"]
  restored <- reify snap
  assert (restored == ctx) (label ++ ": reification changed Map/Set")
  forM_ queries $ \name ->
    assert
      (finiteLookup name (snapUnrestricted snap) ==
          Map.lookup name (unrestrictedBindings ctx) &&
       finiteLookup name (snapAffine snap) ==
          Map.lookup name (affineBindings ctx) &&
       finiteLookup name (snapLinear snap) ==
          Map.lookup name (linearBindings ctx) &&
       elem name (snapLoans snap) ==
          Set.member name (sharedLoans ctx))
      (label ++ ": finite lookup and production map/set disagree")

-- Removing the selected name from each whole domain exposes any mutation of
-- another name, including an additional key not in the original context.
checkFrame :: String -> Name -> ResourceContext -> ResourceContext
  -> Either String ()
checkFrame label target before after = do
  let without = Map.delete target
  assert (without (unrestrictedBindings before) ==
          without (unrestrictedBindings after))
    (label ++ ": unrelated unrestricted map changed")
  assert (without (affineBindings before) ==
          without (affineBindings after))
    (label ++ ": unrelated affine map changed")
  assert (without (linearBindings before) ==
          without (linearBindings after))
    (label ++ ": unrelated linear map changed")
  assert (Set.delete target (sharedLoans before) ==
          Set.delete target (sharedLoans after))
    (label ++ ": unrelated loan set changed")
  checkSnapshot (label ++ " before") before
  checkSnapshot (label ++ " after") after

fromCore :: Show e => Either e a -> Either String a
fromCore = either (Left . show) Right

modeAt :: Int -> Mode
modeAt i = case rem i 3 of
  0 -> Unrestricted
  1 -> Affine
  _ -> Linear

nameAt :: Int -> Name
nameAt i = Name (Text.pack ("owner-" ++ show i))

tyAt :: Int -> Ty
tyAt i = case modeAt i of
  Unrestricted -> TyBool
  Affine -> TyOpaque (Text.pack ("affine-token-" ++ show i))
  Linear -> TyBytes (RefNat (fromIntegral (i + 8)))

build :: Int -> Either String ResourceContext
build count = foldM go Core.emptyContext [0..count - 1]
  where
    go ctx i = fromCore (Core.insertBinding
      (modeAt i) (nameAt i) (tyAt i) ctx)

expectFailure :: (Eq e, Show e, Show a) => e -> Either e a
  -> String -> Either String ()
expectFailure expected actual label = case actual of
  Left err -> assert (err == expected)
    (label ++ ": wrong error: " ++ show err)
  Right value -> Left (label ++ ": unexpectedly accepted " ++ show value)

checkFixture :: Int -> Either String ()
checkFixture count = do
  ctx <- build count
  checkSnapshot "initial finite context" ctx
  let unres = nameAt 0
      affine = nameAt 1
      linear = nameAt 2
      newName = Name "fresh-owner"
  forM_ [Unrestricted,Affine,Linear] $ \mode -> do
    next <- fromCore (Core.insertBinding mode newName TyUnit ctx)
    checkFrame ("insert " ++ show mode) newName ctx next
    let zone = case mode of
          Unrestricted -> unrestrictedBindings next
          Affine -> affineBindings next
          Linear -> linearBindings next
    assert (Map.lookup newName zone == Just TyUnit)
      "insertion lost target mode/type"
    expectFailure (DuplicateBinding newName)
      (Core.insertBinding mode newName TyUnit next)
      "duplicate fresh-owner insertion"
  forM_ [0..count - 1] $ \i ->
    expectFailure (DuplicateBinding (nameAt i))
      (Core.insertBinding (modeAt i) (nameAt i) (tyAt i) ctx)
      "duplicate existing binding"
  (readTy, readCtx) <- fromCore (Core.useUnrestricted unres ctx)
  assert (readTy == tyAt 0 && readCtx == ctx)
    "unrestricted read mutated resources"
  (affineTy, afterAffine) <- fromCore (Core.consumeAffine affine ctx)
  assert (affineTy == tyAt 1 &&
    Map.notMember affine (affineBindings afterAffine))
    "affine consumption did not remove exactly its owner"
  checkFrame "consume affine" affine ctx afterAffine
  (linearTy, afterLinear) <- fromCore (Core.consumeLinear linear ctx)
  assert (linearTy == tyAt 2 &&
    Map.notMember linear (linearBindings afterLinear))
    "linear consumption did not remove exactly its owner"
  checkFrame "consume linear" linear ctx afterLinear
  expectFailure (UnknownBinding linear)
    (Core.consumeLinear linear afterLinear) "linear reuse"
  expectFailure (WrongStructuralMode unres Affine Unrestricted)
    (Core.consumeAffine unres ctx) "wrong mode"
  expectFailure (WrongStructuralMode affine Linear Affine)
    (Core.consumeLinear affine ctx) "wrong linear mode"
  expectFailure (WrongStructuralMode unres Affine Unrestricted)
    (Core.startSharedLoan unres ctx) "loan of unrestricted"
  forM_ [(affine,Affine),(linear,Linear)] $ \(owner,mode) -> do
    loaned <- fromCore (Core.startSharedLoan owner ctx)
    assert (Set.member owner (sharedLoans loaned))
      "loan start missed exact owner"
    checkFrame ("start loan " ++ show mode) owner ctx loaned
    expectFailure (LoanAlreadyActive owner)
      (Core.startSharedLoan owner loaned) "duplicate loan"
    case mode of
      Affine -> expectFailure (OwnerBorrowed owner)
        (Core.consumeAffine owner loaned) "borrowed affine consumption"
      Linear -> expectFailure (OwnerBorrowed owner)
        (Core.consumeLinear owner loaned) "borrowed linear consumption"
      Unrestricted -> Left "invalid test mode"
    ended <- fromCore (Core.endSharedLoan owner loaned)
    checkFrame ("end loan " ++ show mode) owner loaned ended
    assert (ended == ctx) "start/end loan not an exact restoration"
    expectFailure (LoanNotActive owner)
      (Core.endSharedLoan owner ended) "inactive loan end"
  let snap = snapshot ctx
      rejects result = case result of
        Left _ -> True
        Right _ -> False
  assert (rejects (reify (snap
    { snapLinear = snapLinear snap ++ snapLinear snap })))
    "duplicate linear binding was normalized"
  assert (rejects (reify (snap
    { snapAffine = snapAffine snap ++ [(unres, TyUnit)] })))
    "cross-zone duplicate was normalized"
  assert (rejects (reify (snap
    { snapLoans = [Name "foreign-loan"] })))
    "foreign loan was normalized"
  if count < 7 then Right () else do
    let first = nameAt 1
        second = nameAt 4
        inverted = snap
          { snapUnrestricted = reverse (snapUnrestricted snap) }
    assert (rejects (reify inverted)) "unsorted binding zone was accepted"
    loanedFirst <- fromCore (Core.startSharedLoan first ctx)
    loanedBoth <- fromCore (Core.startSharedLoan second loanedFirst)
    checkSnapshot "two unrelated active loans" loanedBoth
    (_,afterConsume) <- fromCore (Core.consumeLinear linear loanedBoth)
    checkFrame "linear consume with other active loans"
      linear loanedBoth afterConsume
    assert (sharedLoans afterConsume == Set.fromList [first,second])
      "unrelated active loans lost during consumption"

main :: IO ()
main = do
  case mapM_ checkFixture [3,7,15] of
    Right () -> putStrLn
      "PASS: finite U/A/L contexts, full-domain frames and malformed evidence"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
