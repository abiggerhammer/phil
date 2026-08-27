{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping
  ( BoundaryRepresentationId (BoundaryRepresentationId)
  , ValueTypeRevision (ValueTypeRevision)
  )
import Phil.Core.Syntax (GrammarId (GrammarId))
import Phil.Examples.Phase1.TargetStrengtheningWitnesses
  ( uploadTargetStrengtheningStage
  )
import Phil.Systems.BoundaryTargetRelation
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle (targetStrengtheningStageRevision)
  , TargetStrengtheningStageRevision (TargetStrengtheningStageRevision)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "BND-013 complete checked zero-copy relation is admitted" checkedZeroCopySucceeds
    , test "BND-013 missing endian/alignment relation rejects" missingEndianRejects
    , test "BND-013 stale target-stage relation rejects" staleStageRejects
    , test "BND-013 pointer reinterpretation alone rejects" pointerReinterpretationRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedZeroCopySucceeds :: Either String ()
checkedZeroCopySucceeds =
  mapLeft show $
    verifyBoundaryTargetRealization uploadTargetStrengtheningStage
      (CheckedZeroCopy completeRelation)

missingEndianRejects :: Either String ()
missingEndianRejects =
  case verifyBoundaryTargetRealization uploadTargetStrengtheningStage
      (CheckedZeroCopy completeRelation { zeroCopyEndianAlignmentPaddingTagging = "" }) of
    Left (BoundaryTargetMissingFact "endian/alignment/padding/tagging") -> Right ()
    other -> Left ("missing endian/alignment fact did not reject exactly: " <> show other)

staleStageRejects :: Either String ()
staleStageRejects =
  case verifyBoundaryTargetRealization uploadTargetStrengtheningStage
      (CheckedZeroCopy completeRelation
        { zeroCopyTargetStageRevision = TargetStrengtheningStageRevision "stale-target-stage"
        }) of
    Left (BoundaryTargetStageRevisionMismatch _ _) -> Right ()
    other -> Left ("stale target-stage relation did not reject exactly: " <> show other)

pointerReinterpretationRejects :: Either String ()
pointerReinterpretationRejects =
  case verifyBoundaryTargetRealization uploadTargetStrengtheningStage
      (PointerReinterpretation "cast buffer pointer to semantic struct") of
    Left (BoundaryTargetPointerReinterpretationRejected _) -> Right ()
    other -> Left ("pointer reinterpretation was accepted: " <> show other)

completeRelation :: ZeroCopyTargetRelation
completeRelation = ZeroCopyTargetRelation
  { zeroCopyTargetStageRevision = targetStrengtheningStageRevision uploadTargetStrengtheningStage
  , zeroCopyBoundaryRepresentation = BoundaryRepresentationId "UploadBoundary@rev1"
  , zeroCopyGrammarRevision = GrammarId "UploadGrammar@rev1"
  , zeroCopyValueTypeRevision = ValueTypeRevision "UploadMessage@rev1"
  , zeroCopySourceSemanticLayout = "message tag and payload constructors correspond exactly"
  , zeroCopyConcreteMemoryLayout = "packed target record layout v1"
  , zeroCopyEndianAlignmentPaddingTagging = "little-endian fields; 4-byte alignment; no implicit padding; explicit tag"
  , zeroCopyLifetimeRules = "view lifetime is bounded by the owned frame lifetime"
  , zeroCopyOwnershipRules = "owned frame remains owner; zero-copy semantic view is non-owning"
  , zeroCopyDeviceStorageConstraints = "host-addressable immutable frame storage"
  , zeroCopyTargetAssumptionsCarriers = "target ABI/layout qualification profile v1"
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
