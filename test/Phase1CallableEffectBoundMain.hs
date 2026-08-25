{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.Static (InterfaceRevision (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-011 exact inferred footprint satisfies public bound" exactBoundAccepts
    , test "CALL-011 narrower implementation satisfies wider public bound" narrowerBodyAccepts
    , test "CALL-011 empty implementation remains valid under nonempty public bound" emptyBodyAccepts
    , test "CALL-011 wider implementation rejects undeclared effect" widerBodyRejects
    , test "CALL-011 rejection reports exact undeclared effect delta" rejectionReportsExactDelta
    , test "CALL-011 public bound remains distinct from narrower body footprint" publicBoundRemainsStable
    , test "CALL-011 effect checking is canonical under body traversal order" effectOrderingIsCanonical
    , test "CALL-011 possession-only higher-order use remains within pure bound" possessionOnlyRemainsPure
    , test "CALL-011 reachable higher-order invocation can exceed enclosing bound" invocationCanExceedEnclosingBound
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactBoundAccepts :: Either String ()
exactBoundAccepts = do
  checked <- mapLeft show $ checkCallableEffectBound ioContract ioEffects
  assert
    (checkedCallableInferredEffects checked == ioEffects)
    "exact body footprint changed during checking"
  assert
    (checkedCallablePublicEffectBound checked == ioEffects)
    "exact public bound changed during checking"

narrowerBodyAccepts :: Either String ()
narrowerBodyAccepts = do
  checked <- mapLeft show $ checkCallableEffectBound ioContract (Set.singleton readEffect)
  assert
    (checkedCallableInferredEffects checked == Set.singleton readEffect)
    "narrow body footprint was widened to public contract"

emptyBodyAccepts :: Either String ()
emptyBodyAccepts = do
  checked <- mapLeft show $ checkCallableEffectBound ioContract Set.empty
  assert
    (Set.null (checkedCallableInferredEffects checked))
    "empty body acquired public may-effects"

widerBodyRejects :: Either String ()
widerBodyRejects =
  case checkCallableEffectBound ioContract widerEffects of
    Left (CallableEffectBoundExceeded revision extra publicBound) -> do
      assert (revision == ioInterface) "effect diagnostic named wrong interface revision"
      assert (extra == Set.singleton deleteEffect) "effect diagnostic named wrong undeclared delta"
      assert (publicBound == ioEffects) "effect diagnostic changed the public bound"
    other -> Left ("wider implementation did not reject: " <> show other)

rejectionReportsExactDelta :: Either String ()
rejectionReportsExactDelta =
  let inferred = Set.fromList [readEffect, deleteEffect, auditEffect]
      expectedExtra = Set.fromList [deleteEffect, auditEffect]
  in case checkCallableEffectBound ioContract inferred of
    Left (CallableEffectBoundExceeded _ extra _) ->
      assert (extra == expectedExtra) "rejection did not report exact undeclared effect set"
    other -> Left ("multi-effect widening did not reject: " <> show other)

publicBoundRemainsStable :: Either String ()
publicBoundRemainsStable = do
  checked <- mapLeft show $ checkCallableEffectBound ioContract (Set.singleton readEffect)
  assert
    (checkedCallablePublicEffectBound checked == ioEffects)
    "narrow implementation silently narrowed stabilized public contract"
  assert
    (checkedCallableInterfaceRevision checked == ioInterface)
    "narrow implementation changed callable interface identity"

effectOrderingIsCanonical :: Either String ()
effectOrderingIsCanonical = do
  let left = inferReachableCallableEffects
        [InvokeCallable readOnlyContract, InvokeCallable installOnlyContract]
      right = inferReachableCallableEffects
        [InvokeCallable installOnlyContract, InvokeCallable readOnlyContract]
  checkedLeft <- mapLeft show $ checkCallableEffectBound ioContract left
  checkedRight <- mapLeft show $ checkCallableEffectBound ioContract right
  assert (checkedLeft == checkedRight)
    "body traversal order changed checked effect semantics"

possessionOnlyRemainsPure :: Either String ()
possessionOnlyRemainsPure = do
  let inferred = inferReachableCallableEffects
        [ PossessCallable ioContract
        , PassCallable ioContract
        , StoreCallable ioContract
        , ReturnCallable ioContract
        ]
  checked <- mapLeft show $ checkCallableEffectBound pureContract inferred
  assert (Set.null (checkedCallableInferredEffects checked))
    "mere possession exceeded a pure enclosing contract"

invocationCanExceedEnclosingBound :: Either String ()
invocationCanExceedEnclosingBound =
  let inferred = inferReachableCallableEffects [InvokeCallable ioContract]
  in case checkCallableEffectBound readOnlyContract inferred of
    Left (CallableEffectBoundExceeded _ extra _) ->
      assert (extra == Set.singleton installEffect)
        "reachable invocation widening reported wrong effect"
    other -> Left ("reachable invocation silently widened enclosing contract: " <> show other)

readEffect, installEffect, deleteEffect, auditEffect :: SemanticEffect
readEffect = SemanticEffect "read"
installEffect = SemanticEffect "install-if-absent"
deleteEffect = SemanticEffect "delete"
auditEffect = SemanticEffect "audit"

ioEffects, widerEffects :: Set.Set SemanticEffect
ioEffects = Set.fromList [readEffect, installEffect]
widerEffects = Set.insert deleteEffect ioEffects

ioInterface :: InterfaceRevision
ioInterface = InterfaceRevision "callable.io.interface.v1"

pureContract, ioContract, readOnlyContract, installOnlyContract :: CallableContract
pureContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.pure.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.empty
  }

ioContract = CallableContract
  { callableContractInterfaceRevision = ioInterface
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = ioEffects
  }

readOnlyContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.read.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.singleton readEffect
  }

installOnlyContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.install.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.singleton installEffect
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
