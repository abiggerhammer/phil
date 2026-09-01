module Main (main) where

import BoundarySubjectKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then putStrLn ("PASS: " ++ label)
  else error ("boundary subject correspondence failed: " ++ label)

isTransfer :: BoundarySubjectTransferDecision -> BoundarySubjectTransferDecision -> Bool
isTransfer expected actual = case (expected, actual) of
  (BoundarySubjectTransferAcceptedDecision, BoundarySubjectTransferAcceptedDecision) -> True
  (BoundarySubjectRuntimeCoincidenceDecision, BoundarySubjectRuntimeCoincidenceDecision) -> True
  (BoundarySubjectTransportKindDecision, BoundarySubjectTransportKindDecision) -> True
  (BoundarySubjectCopyRevisionDecision, BoundarySubjectCopyRevisionDecision) -> True
  (BoundarySubjectByteEqualityDecision, BoundarySubjectByteEqualityDecision) -> True
  (BoundarySubjectTransferLawDecision, BoundarySubjectTransferLawDecision) -> True
  (BoundarySubjectEvidenceReferenceDecision, BoundarySubjectEvidenceReferenceDecision) -> True
  (BoundarySubjectValidityScopeDecision, BoundarySubjectValidityScopeDecision) -> True
  _ -> False

isZeroCopy :: ZeroCopyRealizationDecision -> ZeroCopyRealizationDecision -> Bool
isZeroCopy expected actual = case (expected, actual) of
  (ZeroCopyRealizationAcceptedDecision, ZeroCopyRealizationAcceptedDecision) -> True
  (ZeroCopyPointerReinterpretationDecision, ZeroCopyPointerReinterpretationDecision) -> True
  (ZeroCopyStageRevisionDecision, ZeroCopyStageRevisionDecision) -> True
  (ZeroCopyBoundaryRepresentationDecision, ZeroCopyBoundaryRepresentationDecision) -> True
  (ZeroCopyGrammarDecision, ZeroCopyGrammarDecision) -> True
  (ZeroCopyValueTypeDecision, ZeroCopyValueTypeDecision) -> True
  (ZeroCopySourceSemanticLayoutDecision, ZeroCopySourceSemanticLayoutDecision) -> True
  (ZeroCopyConcreteMemoryLayoutDecision, ZeroCopyConcreteMemoryLayoutDecision) -> True
  (ZeroCopyEndianAlignmentPaddingTaggingDecision, ZeroCopyEndianAlignmentPaddingTaggingDecision) -> True
  (ZeroCopyLifetimeRulesDecision, ZeroCopyLifetimeRulesDecision) -> True
  (ZeroCopyOwnershipRulesDecision, ZeroCopyOwnershipRulesDecision) -> True
  (ZeroCopyDeviceStorageConstraintsDecision, ZeroCopyDeviceStorageConstraintsDecision) -> True
  (ZeroCopyTargetAssumptionsCarriersDecision, ZeroCopyTargetAssumptionsCarriersDecision) -> True
  _ -> False

transfer :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> BoundarySubjectTransferDecision
transfer = decideBoundarySubjectTransferByFacts

zeroCopy
  :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> ZeroCopyRealizationDecision
zeroCopy = decideZeroCopyRealizationByFacts

main :: IO ()
main = do
  assert "exact checked boundary transfer accepts" $
    isTransfer BoundarySubjectTransferAcceptedDecision
      (transfer True True True True True True True)
  assert "runtime coincidence rejects before all transfer facts" $
    isTransfer BoundarySubjectRuntimeCoincidenceDecision
      (transfer False True True True True True True)
  assert "copy transport kind is required" $
    isTransfer BoundarySubjectTransportKindDecision
      (transfer True False True True True True True)
  assert "copy relation revision is required" $
    isTransfer BoundarySubjectCopyRevisionDecision
      (transfer True True False True True True True)
  assert "byte equality revision is required" $
    isTransfer BoundarySubjectByteEqualityDecision
      (transfer True True True False True True True)
  assert "evidence transfer law revision is required" $
    isTransfer BoundarySubjectTransferLawDecision
      (transfer True True True True False True True)
  assert "evidence reference must be exact" $
    isTransfer BoundarySubjectEvidenceReferenceDecision
      (transfer True True True True True False True)
  assert "validity scope is final boundary-transfer gate" $
    isTransfer BoundarySubjectValidityScopeDecision
      (transfer True True True True True True False)

  assert "complete checked zero-copy relation accepts" $
    isZeroCopy ZeroCopyRealizationAcceptedDecision
      (zeroCopy True True True True True True True True True True True True)
  assert "pointer reinterpretation rejects before zero-copy facts" $
    isZeroCopy ZeroCopyPointerReinterpretationDecision
      (zeroCopy False True True True True True True True True True True True)
  assert "zero-copy stage must match exactly" $
    isZeroCopy ZeroCopyStageRevisionDecision
      (zeroCopy True False True True True True True True True True True True)
  assert "boundary representation revision is required" $
    isZeroCopy ZeroCopyBoundaryRepresentationDecision
      (zeroCopy True True False True True True True True True True True True)
  assert "grammar revision is required" $
    isZeroCopy ZeroCopyGrammarDecision
      (zeroCopy True True True False True True True True True True True True)
  assert "semantic value type revision is required" $
    isZeroCopy ZeroCopyValueTypeDecision
      (zeroCopy True True True True False True True True True True True True)
  assert "source semantic layout fact is required" $
    isZeroCopy ZeroCopySourceSemanticLayoutDecision
      (zeroCopy True True True True True False True True True True True True)
  assert "concrete memory layout fact is required" $
    isZeroCopy ZeroCopyConcreteMemoryLayoutDecision
      (zeroCopy True True True True True True False True True True True True)
  assert "endian alignment padding tagging fact is required" $
    isZeroCopy ZeroCopyEndianAlignmentPaddingTaggingDecision
      (zeroCopy True True True True True True True False True True True True)
  assert "lifetime rules fact is required" $
    isZeroCopy ZeroCopyLifetimeRulesDecision
      (zeroCopy True True True True True True True True False True True True)
  assert "ownership rules fact is required" $
    isZeroCopy ZeroCopyOwnershipRulesDecision
      (zeroCopy True True True True True True True True True False True True)
  assert "device storage constraints fact is required" $
    isZeroCopy ZeroCopyDeviceStorageConstraintsDecision
      (zeroCopy True True True True True True True True True True False True)
  assert "target assumptions carriers fact is final zero-copy gate" $
    isZeroCopy ZeroCopyTargetAssumptionsCarriersDecision
      (zeroCopy True True True True True True True True True True True False)
