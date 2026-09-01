module Main (main) where

import SystemsControlPreservationKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then putStrLn ("PASS: " ++ label)
  else error ("systems control correspondence failed: " ++ label)

isBranch :: BranchPreservationDecision -> BranchPreservationDecision -> Bool
isBranch expected actual = case (expected, actual) of
  (BranchPreservationAcceptedDecision, BranchPreservationAcceptedDecision) -> True
  (BranchOutcomeDomainDecision, BranchOutcomeDomainDecision) -> True
  (BranchOwnerFateDomainDecision, BranchOwnerFateDomainDecision) -> True
  (BranchOwnerFateRealizationDecision, BranchOwnerFateRealizationDecision) -> True
  (BranchControlClassDecision, BranchControlClassDecision) -> True
  (BranchTrackedOwnerDecision, BranchTrackedOwnerDecision) -> True
  _ -> False

isState :: StateProjectionDecision -> StateProjectionDecision -> Bool
isState expected actual = case (expected, actual) of
  (StateProjectionAcceptedDecision, StateProjectionAcceptedDecision) -> True
  (StateProjectionKindDecision, StateProjectionKindDecision) -> True
  (StateSlotDomainDecision, StateSlotDomainDecision) -> True
  (StateRestrictedOwnerModeDecision, StateRestrictedOwnerModeDecision) -> True
  (StateFixedSubjectDecision, StateFixedSubjectDecision) -> True
  (StateRestrictedOwnerUniqueDecision, StateRestrictedOwnerUniqueDecision) -> True
  (StateLinearOwnersCoveredDecision, StateLinearOwnersCoveredDecision) -> True
  (StateScopedLoanEscapeDecision, StateScopedLoanEscapeDecision) -> True
  (ClosureCaptureCarrierDecision, ClosureCaptureCarrierDecision) -> True
  (ClosureCarrierSharingDecision, ClosureCarrierSharingDecision) -> True
  _ -> False

isProtocol :: ProtocolPreservationDecision -> ProtocolPreservationDecision -> Bool
isProtocol expected actual = case (expected, actual) of
  (ProtocolPreservationAcceptedDecision, ProtocolPreservationAcceptedDecision) -> True
  (ProtocolBasisDecision, ProtocolBasisDecision) -> True
  (ProtocolTargetSiteDecision, ProtocolTargetSiteDecision) -> True
  (ProtocolTransportUseDecision, ProtocolTransportUseDecision) -> True
  (ProtocolOutcomeDomainDecision, ProtocolOutcomeDomainDecision) -> True
  (ProtocolInstanceDecision, ProtocolInstanceDecision) -> True
  (ProtocolRoleDecision, ProtocolRoleDecision) -> True
  (ProtocolSuccessorFreshDecision, ProtocolSuccessorFreshDecision) -> True
  (ProtocolPredecessorConsumedDecision, ProtocolPredecessorConsumedDecision) -> True
  (ProtocolSuccessorProducedDecision, ProtocolSuccessorProducedDecision) -> True
  (ProtocolLineageDecision, ProtocolLineageDecision) -> True
  _ -> False

isBoundary :: BoundaryCommitDecision -> BoundaryCommitDecision -> Bool
isBoundary expected actual = case (expected, actual) of
  (BoundaryCommitAcceptedDecision, BoundaryCommitAcceptedDecision) -> True
  (BoundarySourceRuntimeFactDecision, BoundarySourceRuntimeFactDecision) -> True
  (BoundaryTransportDecision, BoundaryTransportDecision) -> True
  (BoundaryOwnerDecision, BoundaryOwnerDecision) -> True
  (BoundarySubjectDecision, BoundarySubjectDecision) -> True
  (BoundaryLengthDecision, BoundaryLengthDecision) -> True
  (BoundaryRuntimeKindDecision, BoundaryRuntimeKindDecision) -> True
  (BoundaryRuntimeRevisionEvidenceDecision, BoundaryRuntimeRevisionEvidenceDecision) -> True
  (BoundaryProtocolTransitionDecision, BoundaryProtocolTransitionDecision) -> True
  (BoundaryCommitSuccessorDecision, BoundaryCommitSuccessorDecision) -> True
  (BoundaryFailureTerminalDecision, BoundaryFailureTerminalDecision) -> True
  (BoundaryCompleteBeforeSuccessDecision, BoundaryCompleteBeforeSuccessDecision) -> True
  _ -> False

isSystems :: SystemsControlDecision -> SystemsControlDecision -> Bool
isSystems expected actual = case (expected, actual) of
  (SystemsControlAcceptedDecision, SystemsControlAcceptedDecision) -> True
  (SystemsControlBranchDecision, SystemsControlBranchDecision) -> True
  (SystemsControlStateDecision, SystemsControlStateDecision) -> True
  (SystemsControlProtocolDecision, SystemsControlProtocolDecision) -> True
  (SystemsControlBoundaryDecision, SystemsControlBoundaryDecision) -> True
  _ -> False

main :: IO ()
main = do
  assert "SYS-007 branch preservation accepts" $
    isBranch BranchPreservationAcceptedDecision
      (decideBranchPreservationByFacts True True True True True)
  assert "SYS-007 branch outcome domain is exact" $
    isBranch BranchOutcomeDomainDecision
      (decideBranchPreservationByFacts False True True True True)
  assert "SYS-007 branch owner-fate domain is exact" $
    isBranch BranchOwnerFateDomainDecision
      (decideBranchPreservationByFacts True False True True True)
  assert "SYS-007 every owner fate is realized exactly once" $
    isBranch BranchOwnerFateRealizationDecision
      (decideBranchPreservationByFacts True True False True True)
  assert "SYS-007 terminal/fatal control class is preserved" $
    isBranch BranchControlClassDecision
      (decideBranchPreservationByFacts True True True False True)
  assert "SYS-007 tracked values must be owning values" $
    isBranch BranchTrackedOwnerDecision
      (decideBranchPreservationByFacts True True True True False)

  assert "SYS-008 state projection accepts" $
    isState StateProjectionAcceptedDecision
      (decideStateProjectionByFacts True True True True True True True True True)
  assert "SYS-008 state projection kind is exact" $
    isState StateProjectionKindDecision
      (decideStateProjectionByFacts False True True True True True True True True)
  assert "SYS-008 state slot domain is exact" $
    isState StateSlotDomainDecision
      (decideStateProjectionByFacts True False True True True True True True True)
  assert "SYS-008 restricted owner modes are exact" $
    isState StateRestrictedOwnerModeDecision
      (decideStateProjectionByFacts True True False True True True True True True)
  assert "SYS-008 fixed subjects are exact" $
    isState StateFixedSubjectDecision
      (decideStateProjectionByFacts True True True False True True True True True)
  assert "SYS-008 restricted owners are unique" $
    isState StateRestrictedOwnerUniqueDecision
      (decideStateProjectionByFacts True True True True False True True True True)
  assert "SYS-008 all incoming linear owners are covered" $
    isState StateLinearOwnersCoveredDecision
      (decideStateProjectionByFacts True True True True True False True True True)
  assert "SYS-008 scoped loans do not escape" $
    isState StateScopedLoanEscapeDecision
      (decideStateProjectionByFacts True True True True True True False True True)
  assert "SYS-008 each restricted capture has one carrier" $
    isState ClosureCaptureCarrierDecision
      (decideStateProjectionByFacts True True True True True True True False True)
  assert "SYS-008 restricted capture carriers are unshared" $
    isState ClosureCarrierSharingDecision
      (decideStateProjectionByFacts True True True True True True True True False)

  assert "SYS-009 protocol preservation accepts" $
    isProtocol ProtocolPreservationAcceptedDecision
      (decideProtocolPreservationByFacts True True True True True True True True True True)
  assert "SYS-009 protocol basis must be checked" $
    isProtocol ProtocolBasisDecision
      (decideProtocolPreservationByFacts False True True True True True True True True True)
  assert "SYS-009 target site is exact" $
    isProtocol ProtocolTargetSiteDecision
      (decideProtocolPreservationByFacts True False True True True True True True True True)
  assert "SYS-009 transport use is exact" $
    isProtocol ProtocolTransportUseDecision
      (decideProtocolPreservationByFacts True True False True True True True True True True)
  assert "SYS-009 outcome domain is exact" $
    isProtocol ProtocolOutcomeDomainDecision
      (decideProtocolPreservationByFacts True True True False True True True True True True)
  assert "SYS-009 protocol instance is exact" $
    isProtocol ProtocolInstanceDecision
      (decideProtocolPreservationByFacts True True True True False True True True True True)
  assert "SYS-009 protocol role is exact" $
    isProtocol ProtocolRoleDecision
      (decideProtocolPreservationByFacts True True True True True False True True True True)
  assert "SYS-009 successor is fresh" $
    isProtocol ProtocolSuccessorFreshDecision
      (decideProtocolPreservationByFacts True True True True True True False True True True)
  assert "SYS-009 predecessor is consumed exactly once" $
    isProtocol ProtocolPredecessorConsumedDecision
      (decideProtocolPreservationByFacts True True True True True True True False True True)
  assert "SYS-009 successor is produced exactly once" $
    isProtocol ProtocolSuccessorProducedDecision
      (decideProtocolPreservationByFacts True True True True True True True True False True)
  assert "SYS-009 endpoint lineage is acyclic" $
    isProtocol ProtocolLineageDecision
      (decideProtocolPreservationByFacts True True True True True True True True True False)

  assert "SYS-010 boundary commit accepts" $
    isBoundary BoundaryCommitAcceptedDecision
      (decideBoundaryCommitByFacts True True True True True True True True True True True)
  assert "SYS-010 source runtime fact is exact" $
    isBoundary BoundarySourceRuntimeFactDecision
      (decideBoundaryCommitByFacts False True True True True True True True True True True)
  assert "SYS-010 transport is exact" $
    isBoundary BoundaryTransportDecision
      (decideBoundaryCommitByFacts True False True True True True True True True True True)
  assert "SYS-010 owner is exact" $
    isBoundary BoundaryOwnerDecision
      (decideBoundaryCommitByFacts True True False True True True True True True True True)
  assert "SYS-010 semantic subject is exact" $
    isBoundary BoundarySubjectDecision
      (decideBoundaryCommitByFacts True True True False True True True True True True True)
  assert "SYS-010 length binding is exact" $
    isBoundary BoundaryLengthDecision
      (decideBoundaryCommitByFacts True True True True False True True True True True True)
  assert "SYS-010 runtime site kind is exact" $
    isBoundary BoundaryRuntimeKindDecision
      (decideBoundaryCommitByFacts True True True True True False True True True True True)
  assert "SYS-010 runtime revision/evidence are exact" $
    isBoundary BoundaryRuntimeRevisionEvidenceDecision
      (decideBoundaryCommitByFacts True True True True True True False True True True True)
  assert "SYS-010 protocol transition is exact" $
    isBoundary BoundaryProtocolTransitionDecision
      (decideBoundaryCommitByFacts True True True True True True True False True True True)
  assert "SYS-010 commit produces a successor" $
    isBoundary BoundaryCommitSuccessorDecision
      (decideBoundaryCommitByFacts True True True True True True True True False True True)
  assert "SYS-010 failure remains terminal" $
    isBoundary BoundaryFailureTerminalDecision
      (decideBoundaryCommitByFacts True True True True True True True True True False True)
  assert "SYS-010 success occurs only after complete transfer" $
    isBoundary BoundaryCompleteBeforeSuccessDecision
      (decideBoundaryCommitByFacts True True True True True True True True True True False)

  assert "SYS-007--010 cumulative stage accepts" $
    isSystems SystemsControlAcceptedDecision
      (decideSystemsControlByFacts True True True True)
  assert "SYS-007 predecessor branch stage is required" $
    isSystems SystemsControlBranchDecision
      (decideSystemsControlByFacts False True True True)
  assert "SYS-008 state stage is required" $
    isSystems SystemsControlStateDecision
      (decideSystemsControlByFacts True False True True)
  assert "SYS-009 protocol stage is required" $
    isSystems SystemsControlProtocolDecision
      (decideSystemsControlByFacts True True False True)
  assert "SYS-010 boundary stage is required" $
    isSystems SystemsControlBoundaryDecision
      (decideSystemsControlByFacts True True True False)
