{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified PreservationFixture as F
import qualified Phil.Assurance as A
import Phil.Core.Checker (CheckState (..), LogicalSubjectSupport (..))
import Phil.Core.Context (ResourceContext (..))
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..))
import System.Exit (exitFailure)

-- PreservationFixture is the unchanged previous audit driver with ONLY its
-- module export renamed. It obtains checked literal/type, ValueResult and
-- residual support from Phil. No state, proof or resolved tree is fabricated.
-- The permitted runtime disposition discharges no refinement using a consumed
-- owner; it tests durable interpretation independently of evidence availability.

prepared :: Mode -> Either String (ValueResult,Obligation,D.DischargePolicy)
prepared mode = do
  (before,result) <- F.fixture F.boundTy F.targetTy mode
  let after = valueResultState result
      ctx = resourceContext after
  F.assert (resourceContext before /= ctx) "restricted value was not consumed"
  F.assert (Map.notMember F.payload (unrestrictedBindings ctx)
    && Map.notMember F.payload (affineBindings ctx)
    && Map.notMember F.payload (linearBindings ctx)) "consumed owner remains available"
  obligation <- maybe (Left "actual residual missing") Right $
    Map.lookup (residualObligationId F.spec) (residualObligations after)
  F.assert (obligation == F.rootFor F.target) "actual original requirement changed"
  support <- maybe (Left "captured logical subject missing") Right $
    Map.lookup (obligationId obligation) (residualLogicalSubjects after)
  F.assert (logicalSupportObligation support == obligation) "support names a different event"
  F.assert (Map.lookup F.payload (logicalSupportBindings support) == Just F.boundTy)
    "original refined type not retained"
  F.assert (Map.notMember F.payload (logicalSupportUnrestrictedBindings support))
    "restricted captured subject became unrestricted authority"
  policy <- F.right $ D.bindRuntime (F.runtimeFor obligation) D.emptyDischargePolicy
  pure (result,obligation,policy)

ordinary :: Mode -> Either String (ValueResult,D.DischargePolicy,D.ResolvedObligation)
ordinary mode = do
  (result,obligation,policy) <- prepared mode
  resolved <- F.right $ D.resolveObligation emptyStaticContext (valueResultState result) policy obligation
  F.assert (D.resolvedObligation resolved == obligation) "ordinary resolver changed event"
  F.assert (D.resolvedDisposition resolved == D.RuntimeBound (F.runtimeFor obligation))
    "ordinary resolver did not retain exact declared runtime responsibility"
  F.assert (null (D.resolvedPrerequisites resolved)) "unexpected child"
  pure (result,policy,resolved)

adapter :: Mode -> Either String ()
adapter mode = do
  (result,policy,expected) <- ordinary mode
  actual <- F.right $ A.resolveOriginalCheckEvent emptyStaticContext policy F.spec result
  F.assert (actual == expected) "event adapter changed legitimate runtime disposition or identity"

main :: IO ()
main = do
  results <- sequence
    [ test "C01" "linear actual check consumes owner and retains exact refined support" (prepared Linear >> pure ())
    , test "C02" "linear ordinary resolver interprets exact residual under declared runtime policy" (ordinary Linear >> pure ())
    , test "C03" "affine actual check consumes owner and retains exact refined support" (prepared Affine >> pure ())
    , test "C04" "affine ordinary resolver interprets exact residual under declared runtime policy" (ordinary Affine >> pure ())
    , test "R01" "linear original-event adapter preserves legitimate retained interpretation" (adapter Linear)
    , test "R02" "affine original-event adapter preserves legitimate retained interpretation" (adapter Affine)
    ]
  putStrLn "COMPLETE correctness_groups=6"
  unless (and results) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False
