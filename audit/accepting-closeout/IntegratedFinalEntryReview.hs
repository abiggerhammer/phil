{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified EntryFixture as F
import qualified ClosureFixture as C
import qualified DirectFixture as DF
import qualified Phil.Assurance as A
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (EvidenceUse (..))
import Phil.Core.Value (ValueResult (..))
import System.Exit (exitFailure)

-- EntryFixture is the exact prior OriginalEntryBoundary driver, changed ONLY
-- from module Main(main) to module EntryFixture. Its sources, predicates,
-- expected diagnostics and actual-result fixtures are otherwise unchanged.
-- We invoke 15 prior cases intact. K11 explicitly adopts #1398's documented
-- final-entry boundary: diagnostic/direct-authority routes remain legitimate,
-- but a residual-free result has no retained historical producer association.
-- No production source, checked result, or historical test assertion is edited.

residualFreeFinalBoundary :: Either String ()
residualFreeFinalBoundary = do
  (spec,result,_,entries,fixture) <- F.authorityFixture F.Direct
  let residuals = [key | EvidenceResidual key _ <- valueResultEvidence result]
  if null residuals then Right () else Left "direct fixture unexpectedly has a residual"
  -- This remains a valid separate authority-aware consumer case. An arbitrary
  -- setup failure cannot count as the intended producer-association rejection.
  _ <- either (Left . show) Right $
    F.genericClose entries (F.fromDirectFixture fixture)
  F.exactError A.OriginalCheckEventClosureProducerAssociationRequired $
    F.nativeClose DF.handoffConfig spec D.emptyDischargePolicy result (F.fromDirectFixture fixture)

main :: IO ()
main = do
  results <- sequence
    [ test "K01" "definitional original event closes with adequate local support" (F.fullScope C.definition)
    , test "K02" "algebraic original event closes with adequate local support" (F.fullScope C.algebra)
    , test "K03" "explicit-prerequisite event closes with adequate support" (F.fullScope C.explicit)
    , test "K04" "definitional prerequisite cannot be exported under a local parent" (F.exportRequired C.definition)
    , test "K05" "certificate prerequisite cannot be exported under a local parent" (F.exportRequired C.algebra)
    , test "K06" "a smaller graph cannot replace actual event support" F.missingSupport
    , test "K07" "another valid event package cannot substitute for this event" F.otherEvent
    , test "K08" "retained residual requires the exact scope metadata" F.wrongScope
    , test "K09" "permitted whole-tree export retains its conditional contract" F.wholeTreeExport
    , test "K10" "real direct evidence reaches its authority-aware final consumer" (F.authorityAccepts F.Direct)
    , test "K11" "residual-free final entry enforces producer association" residualFreeFinalBoundary
    , test "K12" "direct authority belongs to the same actual event" F.wrongAuthorityEvent
    , test "K13" "the consuming evidence revision must match" F.wrongFinalEvidence
    , test "K14" "final evidence cannot drop exact direct support" F.droppedDirectSupport
    , test "K15" "real arithmetic fact reaches its authority-aware final consumer" (F.authorityAccepts F.Arithmetic)
    , test "K16" "bounded entry cannot infer missing local arithmetic authority" (F.boundedAuthorityRejection F.Arithmetic)
    ]
  putStrLn "COMPLETE reviewed_final_entry_groups=16"
  unless (and results) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False
