{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusStep (..)
  , FocusedRequirement (..)
  , FocusingError (..)
  , canonicalizeProposition
  , checkBranchExhaustiveness
  , elaborateRefTermAs
  , focusProposition
  , focusSessionHead
  , resolveMode
  , validateStaticContext
  )
import Phil.Core.Static
  ( StaticContext
  , StaticError (..)
  , declareOpaqueClaim
  , declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Mode (..)
  , Name (Name)
  , Outcome (Outcome)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "transparent claims expand deterministically" testTransparentExpansion
    , test "nested transparent claims expand transitively" testNestedTransparentExpansion
    , test "transparent claim recursion is rejected" testTransparentRecursion
    , test "unknown claims are rejected" testUnknownClaim
    , test "transparent definitions cannot contain free refinement variables" testFreeVariableDefinition
    , test "claim arity is checked from Sigma" testClaimArity
    , test "claim argument sorts are checked from Sigma" testClaimArgumentSort
    , test "duplicate claim declarations are rejected" testDuplicateClaim
    , test "duplicate claim parameters are rejected" testDuplicateClaimParameter
    , test "Nat claim parameters receive canonical UInt-to-Nat coercions" testClaimNatCoercion
    , test "Nat-to-UInt claim coercions are never implicit" testNoReverseClaimCoercion
    , test "ordered Nat contexts receive canonical UInt-to-Nat coercions" testOrderNatCoercion
    , test "explicit expected Nat elaboration inserts UInt-to-Nat" testExpectedNatCoercion
    , test "transparent unresolved goals route to the decision-procedure boundary" testTransparentNeedsSolver
    , test "opaque unresolved goals route to an explicit mechanism boundary" testOpaqueNeedsExplicit
    , test "matching evidence discharges an opaque claim" testOpaqueEvidence
    , test "matching evidence survives transparent claim expansion" testTransparentEvidence
    , test "literal normalization discharges a goal definitionally" testDefinitionDischarge
    , test "statically false goals reject before solver dispatch" testStaticallyFalse
    , test "Nat subtraction side conditions survive goal normalization" testSubtractionPrerequisite
    , test "known-false subtraction side conditions reject before the main goal" testFalseSubtractionPrerequisite
    , test "structural mode resolution is deterministic" testResolveMode
    , test "guarded session heads are exposed deterministically" testSessionHead
    , test "branch exhaustiveness accepts exactly the declared labels" testBranchExhaustive
    , test "branch exhaustiveness reports missing and extra handlers" testBranchMismatch
    , test "duplicate branch handlers are rejected" testDuplicateHandler
    , test "duplicate declared branch labels are rejected" testDuplicateDeclaredBranch
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

var :: Text -> RefTerm
var = RefVar . name

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

underLimitContext :: Either String StaticContext
underLimitContext =
  mapLeft show $
    declareTransparentClaim
      "UnderLimit"
      [(name "n", SortNat)]
      (LessEqual (var "n") (RefNat 10))
      emptyStaticContext

testTransparentExpansion :: Either String ()
testTransparentExpansion = do
  sigma <- underLimitContext
  (canonical, trace) <- mapLeft show $
    canonicalizeProposition sigma emptyCheckState (Atom "UnderLimit" [RefNat 4])
  assert (canonical == Truth) "transparent claim did not normalize after expansion"
  assert
    (ExpandedTransparentClaim "UnderLimit" `elem` trace)
    "transparent expansion was absent from the focusing trace"

testNestedTransparentExpansion :: Either String ()
testNestedTransparentExpansion = do
  sigma0 <- underLimitContext
  sigma <- mapLeft show $
    declareTransparentClaim
      "Allowed"
      [(name "n", SortNat)]
      (Conjunction
        (Atom "UnderLimit" [var "n"])
        (NotEqual (var "n") (RefNat 0)))
      sigma0
  (canonical, trace) <- mapLeft show $
    canonicalizeProposition sigma emptyCheckState (Atom "Allowed" [RefNat 3])
  assert (canonical == Truth) "nested transparent claims did not normalize to true"
  assert
    (ExpandedTransparentClaim "Allowed" `elem` trace
      && ExpandedTransparentClaim "UnderLimit" `elem` trace)
    "nested expansion trace omitted a transparent claim"

testTransparentRecursion :: Either String ()
testTransparentRecursion = do
  sigma0 <- mapLeft show $
    declareTransparentClaim "A" [(name "x", SortNat)] (Atom "B" [var "x"]) emptyStaticContext
  sigma <- mapLeft show $
    declareTransparentClaim "B" [(name "x", SortNat)] (Atom "A" [var "x"]) sigma0
  case validateStaticContext sigma of
    Left (RecursiveTransparentClaim cycleNames) ->
      assert ("A" `elem` cycleNames && "B" `elem` cycleNames) "recursive-claim diagnostic lost the cycle"
    other -> Left ("mutual transparent recursion was not rejected: " ++ show other)

testUnknownClaim :: Either String ()
testUnknownClaim =
  case focusProposition emptyStaticContext emptyCheckState (Atom "Missing" []) of
    Left (UnknownClaim "Missing") -> Right ()
    other -> Left ("unknown claim did not fail at Sigma lookup: " ++ show other)

testFreeVariableDefinition :: Either String ()
testFreeVariableDefinition = do
  sigma <- mapLeft show $
    declareTransparentClaim
      "Bad"
      [(name "x", SortNat)]
      (Equal (var "x") (var "free"))
      emptyStaticContext
  case validateStaticContext sigma of
    Left (FocusSortError _) -> Right ()
    other -> Left ("free variable in transparent claim was accepted: " ++ show other)

testClaimArity :: Either String ()
testClaimArity = do
  sigma <- underLimitContext
  case focusProposition sigma emptyCheckState (Atom "UnderLimit" []) of
    Left (ClaimArityMismatch "UnderLimit" 1 0) -> Right ()
    other -> Left ("claim arity mismatch was not rejected: " ++ show other)

testClaimArgumentSort :: Either String ()
testClaimArgumentSort = do
  sigma <- underLimitContext
  case focusProposition sigma emptyCheckState (Atom "UnderLimit" [RefBool True]) of
    Left (ClaimArgumentSortMismatch "UnderLimit" 0 SortNat SortBool) -> Right ()
    other -> Left ("claim argument sort mismatch was accepted: " ++ show other)

testDuplicateClaim :: Either String ()
testDuplicateClaim = do
  sigma <- underLimitContext
  case declareOpaqueClaim "UnderLimit" [] sigma of
    Left (DuplicateClaim "UnderLimit") -> Right ()
    other -> Left ("duplicate claim declaration was accepted: " ++ show other)

testDuplicateClaimParameter :: Either String ()
testDuplicateClaimParameter =
  case declareOpaqueClaim
    "BadParams"
    [(name "x", SortNat), (name "x", SortNat)]
    emptyStaticContext of
      Left (DuplicateClaimParameter "BadParams" parameter) ->
        assert (parameter == name "x") "duplicate parameter diagnostic named the wrong binder"
      other -> Left ("duplicate claim parameters were accepted: " ++ show other)

testClaimNatCoercion :: Either String ()
testClaimNatCoercion = do
  sigma <- underLimitContext
  state <- withBinding Unrestricted (name "count") (TyUInt 16) emptyCheckState
  (canonical, trace) <- mapLeft show $
    canonicalizeProposition sigma state (Atom "UnderLimit" [var "count"])
  assert
    (canonical == LessEqual (RefToNat (var "count")) (RefNat 10))
    "UInt claim argument did not elaborate to an explicit Nat coercion"
  assert
    (InsertedUIntToNat (var "count") `elem` trace)
    "canonical claim-argument coercion was not traced"

testNoReverseClaimCoercion :: Either String ()
testNoReverseClaimCoercion = do
  sigma <- mapLeft show $
    declareOpaqueClaim "NeedsU16" [(name "x", SortUInt 16)] emptyStaticContext
  case focusProposition sigma emptyCheckState (Atom "NeedsU16" [RefNat 1]) of
    Left (ClaimArgumentSortMismatch "NeedsU16" 0 (SortUInt 16) SortNat) -> Right ()
    other -> Left ("Nat was implicitly coerced to UInt: " ++ show other)

testOrderNatCoercion :: Either String ()
testOrderNatCoercion = do
  state <- withBinding Unrestricted (name "count") (TyUInt 16) emptyCheckState
  (canonical, trace) <- mapLeft show $
    canonicalizeProposition emptyStaticContext state (LessThan (var "count") (RefNat 3))
  assert
    (canonical == LessThan (RefToNat (var "count")) (RefNat 3))
    "mixed UInt/Nat order did not insert toNat"
  assert (InsertedUIntToNat (var "count") `elem` trace) "order coercion was not traced"

testExpectedNatCoercion :: Either String ()
testExpectedNatCoercion = do
  state <- withBinding Unrestricted (name "count") (TyUInt 32) emptyCheckState
  (term, trace) <- mapLeft show $
    elaborateRefTermAs emptyStaticContext state SortNat (var "count")
  assert (term == RefToNat (var "count")) "expected Nat elaboration did not insert toNat"
  assert (InsertedUIntToNat (var "count") `elem` trace) "expected-sort coercion was not traced"

testTransparentNeedsSolver :: Either String ()
testTransparentNeedsSolver = do
  sigma <- underLimitContext
  state <- withBinding Unrestricted (name "n") (TyOpaqueSorted "N" SortNat) emptyCheckState
  plan <- mapLeft show $ focusProposition sigma state (Atom "UnderLimit" [var "n"])
  assert
    (focusedMechanism (focusGoal plan) == FocusNeedsDecisionProcedure)
    "unresolved transparent goal did not stop at decision-procedure boundary"

testOpaqueNeedsExplicit :: Either String ()
testOpaqueNeedsExplicit = do
  sigma <- digestContext
  state <- payloadState
  plan <- mapLeft show $ focusProposition sigma state (Atom "DigestMatches" [var "payloadId"])
  assert
    (focusedMechanism (focusGoal plan) == FocusNeedsExplicitMechanism)
    "opaque claim was incorrectly routed to the transparent solver"

testOpaqueEvidence :: Either String ()
testOpaqueEvidence = do
  sigma <- digestContext
  state0 <- payloadState
  state <- withBinding
    Unrestricted
    (name "digestProof")
    (TyProof (Atom "DigestMatches" [var "payloadId"]))
    state0
  plan <- mapLeft show $ focusProposition sigma state (Atom "DigestMatches" [var "payloadId"])
  assert
    (focusedMechanism (focusGoal plan) == FocusByEvidence (name "digestProof"))
    "matching opaque evidence was not used before explicit-mechanism fallback"

testTransparentEvidence :: Either String ()
testTransparentEvidence = do
  sigma <- underLimitContext
  state0 <- withBinding Unrestricted (name "n") (TyOpaqueSorted "N" SortNat) emptyCheckState
  state <- withBinding
    Unrestricted
    (name "limitProof")
    (TyProof (Atom "UnderLimit" [var "n"]))
    state0
  plan <- mapLeft show $ focusProposition sigma state (Atom "UnderLimit" [var "n"])
  assert
    (focusedMechanism (focusGoal plan) == FocusByEvidence (name "limitProof"))
    "evidence for a transparent named claim did not match its canonical expansion"

testDefinitionDischarge :: Either String ()
testDefinitionDischarge = do
  plan <- mapLeft show $
    focusProposition emptyStaticContext emptyCheckState (LessEqual (RefNat 2) (RefNat 3))
  assert
    (focusedMechanism (focusGoal plan) == FocusByDefinition
      && focusedCanonical (focusGoal plan) == Truth)
    "literal proposition was not definitionally discharged"

testStaticallyFalse :: Either String ()
testStaticallyFalse =
  case focusProposition emptyStaticContext emptyCheckState (LessThan (RefNat 3) (RefNat 2)) of
    Left (StaticallyFalseGoal Falsehood) -> Right ()
    other -> Left ("statically false proposition reached a later mechanism: " ++ show other)

testSubtractionPrerequisite :: Either String ()
testSubtractionPrerequisite = do
  state0 <- withBinding Unrestricted (name "a") (TyOpaqueSorted "A" SortNat) emptyCheckState
  state <- withBinding Unrestricted (name "b") (TyOpaqueSorted "B" SortNat) state0
  let subtraction = RefSub (var "a") (var "b")
  plan <- mapLeft show $
    focusProposition emptyStaticContext state (Equal subtraction subtraction)
  assert
    (focusedMechanism (focusGoal plan) == FocusByDefinition)
    "self-equality around subtraction did not normalize"
  case focusPrerequisites plan of
    [requirement] -> do
      assert
        (focusedCanonical requirement == LessEqual (var "b") (var "a"))
        "subtraction prerequisite has the wrong canonical proposition"
      assert
        (focusedMechanism requirement == FocusNeedsDecisionProcedure)
        "symbolic subtraction prerequisite did not route to decision procedure"
    other -> Left ("subtraction prerequisite was lost or duplicated: " ++ show other)

testFalseSubtractionPrerequisite :: Either String ()
testFalseSubtractionPrerequisite = do
  let subtraction = RefSub (RefNat 1) (RefNat 2)
  case focusProposition emptyStaticContext emptyCheckState (Equal subtraction subtraction) of
    Left (StaticallyFalseGoal Falsehood) -> Right ()
    other -> Left ("known-false subtraction prerequisite was hidden by normalization: " ++ show other)

testResolveMode :: Either String ()
testResolveMode = do
  gamma <- withBinding Unrestricted (name "g") TyBool emptyCheckState
  affine <- withBinding Affine (name "a") TyBool emptyCheckState
  linear <- withBinding Linear (name "d") TyBool emptyCheckState
  assert (resolveMode gamma (name "g") == Right Unrestricted) "Gamma mode did not resolve"
  assert (resolveMode affine (name "a") == Right Affine) "affine mode did not resolve"
  assert (resolveMode linear (name "d") == Right Linear) "linear mode did not resolve"

testSessionHead :: Either String ()
testSessionHead = do
  let x = name "X"
      session = Rec x (Receive (name "msg") TyBool (SessionVar x))
  case focusSessionHead session of
    Right (Receive binder TyBool _) ->
      assert (binder == name "msg") "guarded unfolding exposed the wrong binder"
    other -> Left ("guarded session head was not exposed: " ++ show other)

testBranchExhaustive :: Either String ()
testBranchExhaustive =
  mapLeft show $ checkBranchExhaustiveness choiceBranches ["accepted", "rejected"]

testBranchMismatch :: Either String ()
testBranchMismatch =
  case checkBranchExhaustiveness choiceBranches ["accepted", "other"] of
    Left (BranchHandlerMismatch ["rejected"] ["other"]) -> Right ()
    other -> Left ("branch mismatch was not reported precisely: " ++ show other)

testDuplicateHandler :: Either String ()
testDuplicateHandler =
  case checkBranchExhaustiveness choiceBranches ["accepted", "accepted", "rejected"] of
    Left (DuplicateBranchHandlerLabel "accepted") -> Right ()
    other -> Left ("duplicate handler label was accepted: " ++ show other)

testDuplicateDeclaredBranch :: Either String ()
testDuplicateDeclaredBranch =
  case checkBranchExhaustiveness
    [ Branch "same" Nothing (End (Outcome "success"))
    , Branch "same" Nothing (End (Outcome "failure"))
    ]
    ["same"] of
      Left (DuplicateDeclaredBranchLabel "same") -> Right ()
      other -> Left ("duplicate declared branch was accepted: " ++ show other)

digestContext :: Either String StaticContext
digestContext =
  mapLeft show $
    declareOpaqueClaim
      "DigestMatches"
      [(name "payload", SortStableId "Payload")]
      emptyStaticContext

payloadState :: Either String CheckState
payloadState =
  withBinding
    Unrestricted
    (name "payloadId")
    (TyOpaqueSorted "PayloadId" (SortStableId "Payload"))
    emptyCheckState

choiceBranches :: [Branch]
choiceBranches =
  [ Branch "accepted" Nothing (End (Outcome "success"))
  , Branch "rejected" Nothing (End (Outcome "failure"))
  ]

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode binding ty state = do
  context <- mapLeft show $ insertBinding mode binding ty (resourceContext state)
  Right state { resourceContext = context }

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
