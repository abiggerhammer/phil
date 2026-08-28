{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Process (ProcessKey (..))
import Phil.Core.ProcessCausality
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-006 independent cross-process events are incomparable" independentEventsAreUnordered
    , test "CONC-006 both independent relative orders are admitted" bothIndependentOrdersAccepted
    , test "CONC-006 declaration/enumeration order is nonsemantic" declarationOrderDoesNotMatter
    , test "CONC-006 local and rendezvous causality violations reject" causalViolationRejects
    , test "CONC-006 explicit architecture causality adds only declared order" explicitArchitectureOrder
    , test "CONC-006 causal cycles reject" causalCycleRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

independentEventsAreUnordered :: Either String ()
independentEventsAreUnordered = do
  order <- baselineOrder
  assert (incomparableEvents order aIndependent bIndependent)
    "independent events acquired an undeclared cross-process order"
  assert (orderedBefore order aIndependent syncEvent)
    "process A local order did not constrain its rendezvous predecessor"
  assert (orderedBefore order bIndependent syncEvent)
    "process B local order did not constrain its rendezvous predecessor"
  assert (orderedBefore order syncEvent aAfter)
    "rendezvous did not constrain process A successor"
  assert (orderedBefore order syncEvent bAfter)
    "rendezvous did not constrain process B successor"

bothIndependentOrdersAccepted :: Either String ()
bothIndependentOrdersAccepted = do
  order <- baselineOrder
  mapLeft show $ validateEventLinearization order traceAFirst
  mapLeft show $ validateEventLinearization order traceBFirst

declarationOrderDoesNotMatter :: Either String ()
declarationOrderDoesNotMatter = do
  normal <- baselineOrder
  reversed <- mapLeft show $ buildProcessPartialOrder
    (reverse events)
    (reverse processSequences)
    []
  assert (normal == reversed)
    "event/process declaration order changed the source partial order"

causalViolationRejects :: Either String ()
causalViolationRejects = do
  order <- baselineOrder
  case validateEventLinearization order
      [aStart, bStart, syncEvent, aIndependent, bIndependent, aAfter, bAfter] of
    Left (LinearizationViolatesCausality _) -> Right ()
    other -> Left ("causality-violating trace did not reject: " <> show other)

explicitArchitectureOrder :: Either String ()
explicitArchitectureOrder = do
  order <- mapLeft show $ buildProcessPartialOrder events processSequences
    [ArchitectureCausalEdge "architecture.requires-a-before-b" aIndependent bIndependent]
  assert (orderedBefore order aIndependent bIndependent)
    "explicit architecture edge did not enter source causality"
  mapLeft show $ validateEventLinearization order traceAFirst
  case validateEventLinearization order traceBFirst of
    Left (LinearizationViolatesCausality edge) ->
      assert
        ( causalBefore edge == aIndependent
          && causalAfter edge == bIndependent
          && causalOrigin edge == ExplicitArchitectureCausality "architecture.requires-a-before-b" )
        "architecture-order rejection lost the exact declared edge"
    other -> Left ("trace violating explicit architecture causality was accepted: " <> show other)

causalCycleRejects :: Either String ()
causalCycleRejects =
  case buildProcessPartialOrder events processSequences
      [ArchitectureCausalEdge "bad-backedge" syncEvent aIndependent] of
    Left (CyclicProcessCausality _ _) -> Right ()
    other -> Left ("cyclic causal graph did not reject: " <> show other)

baselineOrder :: Either String ProcessPartialOrder
baselineOrder = mapLeft show $ buildProcessPartialOrder events processSequences []

events :: [ProcessEvent]
events =
  [ local aStart processA
  , local aIndependent processA
  , local bStart processB
  , local bIndependent processB
  , ProcessEvent syncEvent (SynchronousRendezvousEvent processA processB)
  , local aAfter processA
  , local bAfter processB
  ]

processSequences :: [(ProcessKey, [ProcessEventKey])]
processSequences =
  [ (processA, [aStart, aIndependent, syncEvent, aAfter])
  , (processB, [bStart, bIndependent, syncEvent, bAfter])
  ]

traceAFirst, traceBFirst :: [ProcessEventKey]
traceAFirst = [aStart, bStart, aIndependent, bIndependent, syncEvent, aAfter, bAfter]
traceBFirst = [bStart, aStart, bIndependent, aIndependent, syncEvent, bAfter, aAfter]

local :: ProcessEventKey -> ProcessKey -> ProcessEvent
local key processKey = ProcessEvent key (LocalProcessEvent processKey)

processA, processB :: ProcessKey
processA = ProcessKey "process-a"
processB = ProcessKey "process-b"

aStart, aIndependent, bStart, bIndependent, syncEvent, aAfter, bAfter :: ProcessEventKey
aStart = ProcessEventKey "a.start"
aIndependent = ProcessEventKey "a.independent"
bStart = ProcessEventKey "b.start"
bIndependent = ProcessEventKey "b.independent"
syncEvent = ProcessEventKey "rendezvous.ab"
aAfter = ProcessEventKey "a.after"
bAfter = ProcessEventKey "b.after"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
