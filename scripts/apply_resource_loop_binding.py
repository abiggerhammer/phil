from pathlib import Path


path = Path("src/Phil/Systems/ControlStateProjection.hs")
text = path.read_text()
old = """import qualified ResourceJoinKernel as ResourceJoinKernel
import qualified ResourceScopeKernel as ResourceScopeKernel
"""
new = """import qualified ResourceJoinKernel as ResourceJoinKernel
import qualified ResourceLoopKernel as ResourceLoopKernel
import qualified ResourceScopeKernel as ResourceScopeKernel
"""
assert old in text
text = text.replace(old, new, 1)

old = """  checkResourceJoinKernel
  checkResourceScopeProjectionKernel function
"""
new = """  checkResourceJoinKernel
  checkResourceScopeProjectionKernel function
  checkResourceLoopProjectionKernel
"""
assert old in text
text = text.replace(old, new, 1)

marker = """    checkResourceScopeProjectionKernel function = do
"""
assert marker in text
helper = r'''    checkResourceLoopProjectionKernel =
      case stateBoundaryKind boundary of
        OrdinaryJoinBoundary -> Right ()
        LoopStateBoundary ->
          case ResourceLoopKernel.decideLoopProjectionByFacts
              loopKindMatches
              resourceJoinAccepted
              slotDomainExact
              requirementsExact of
            ResourceLoopKernel.LoopProjectionAcceptedDecision -> Right ()
            _ -> resourceLoopKernelInvariant "loop-projection"
      where
        loopKindMatches = case stateProjectionKind projection of
          LoopInitialEntry -> True
          LoopBackedge -> True
          OrdinaryJoinPredecessor -> False
        slotDomainExact =
          Map.keysSet (stateBoundarySlots boundary)
            == Map.keysSet (stateProjectionBindings projection)
        requirementsExact = all bindingMatchesDeclaredRequirement
          (Map.toAscList (stateBoundarySlots boundary))
        bindingMatchesDeclaredRequirement (slotKey, slot) =
          case Map.lookup slotKey (stateProjectionBindings projection) of
            Nothing -> False
            Just ref -> modeMatches slot ref && subjectMatches slot ref
        modeMatches slot ref = case stateSlotMode slot of
          Unrestricted ->
            Map.notMember ref (stateProjectionIncomingRestricted projection)
          expectedMode ->
            Map.lookup ref (stateProjectionIncomingRestricted projection)
              == Just expectedMode
        subjectMatches slot ref = case stateSlotSubjectRequirement slot of
          AnyStateSubject -> True
          FixedStateSubject subject ->
            maybe False (Set.member ref) (Map.lookup subject subjectIndex)
        resourceJoinAccepted = case ResourceJoinKernel.decideResourceProjectionByFacts
            allIncomingLinearExactlyOnceBound
            noInventedLinearOwners
            allBoundLinearSubjectsAdmissible of
          ResourceJoinKernel.ResourceProjectionAcceptedDecision -> True
          _ -> False
        bindingCounts = Map.fromListWith (+)
          [ (ref, 1 :: Int)
          | ref <- Map.elems (stateProjectionBindings projection)
          ]
        incomingLinear = Set.fromList
          [ ref
          | (ref, mode) <- Map.toAscList
              (stateProjectionIncomingRestricted projection)
          , mode == Linear
          ]
        linearBindings =
          [ (slotKey, ref)
          | (slotKey, ref) <- Map.toAscList
              (stateProjectionBindings projection)
          , Just slot <- [Map.lookup slotKey (stateBoundarySlots boundary)]
          , stateSlotMode slot == Linear
          ]
        allIncomingLinearExactlyOnceBound = all
          (\ref -> Map.findWithDefault 0 ref bindingCounts == 1)
          (Set.toList incomingLinear)
        noInventedLinearOwners = all
          (\(_, ref) ->
            Map.lookup ref (stateProjectionIncomingRestricted projection)
              == Just Linear)
          linearBindings
        allBoundLinearSubjectsAdmissible = all subjectAdmissible linearBindings
        subjectAdmissible (slotKey, ref) =
          case Map.lookup slotKey (stateBoundarySlots boundary) of
            Nothing -> False
            Just slot -> case stateSlotSubjectRequirement slot of
              AnyStateSubject -> True
              FixedStateSubject subject ->
                maybe False (Set.member ref) (Map.lookup subject subjectIndex)

'''
text = text.replace(marker, helper + marker, 1)

old = """resourceScopeKernelInvariant :: String -> Either e a
resourceScopeKernelInvariant label =
  error (\"ResourceScopeKernel mismatch: \" <> label)
"""
new = """resourceScopeKernelInvariant :: String -> Either e a
resourceScopeKernelInvariant label =
  error (\"ResourceScopeKernel mismatch: \" <> label)

resourceLoopKernelInvariant :: String -> Either e a
resourceLoopKernelInvariant label =
  error (\"ResourceLoopKernel mismatch: \" <> label)
"""
assert old in text
text = text.replace(old, new, 1)
path.write_text(text)

path = Path("src/Phil/Core/Value.hs")
text = path.read_text()
close = """  , Value (..)
  )
"""
replacement = """  , Value (..)
  )
import qualified ResourceLoopKernel as ResourceLoopKernel
"""
assert close in text
text = text.replace(close, replacement, 1)

old = """      case transportRequirement sourceTy targetTy of
        TransportDefinitionallyEqual -> Left (TransportNotRequired sourceTy)
        TransportUnsupported -> Left (UnsupportedTransport sourceTy targetTy)
        TransportRequires proposition -> do
          evidenceUses <- mapLeft ValueRefinementError $
            dischargePropositionUsing proofName proposition (valueResultState source)
          Right source
            { valueResultType = targetTy
            , valueResultEvidence = appendEvidenceList evidenceUses (valueResultEvidence source)
            }
"""
new = """      case transportRequirement sourceTy targetTy of
        TransportDefinitionallyEqual ->
          case ResourceLoopKernel.decideStateTransportByFacts
              (definitionallyEqualTy sourceTy targetTy) False of
            ResourceLoopKernel.StateTransportAcceptedDecision ->
              Left (TransportNotRequired sourceTy)
            _ -> resourceLoopKernelInvariant \"definitional-transport\"
        TransportUnsupported -> Left (UnsupportedTransport sourceTy targetTy)
        TransportRequires proposition -> do
          evidenceUses <- mapLeft ValueRefinementError $
            dischargePropositionUsing proofName proposition (valueResultState source)
          let explicitEvidenceAccepted = not (null evidenceUses)
          case ResourceLoopKernel.decideStateTransportByFacts
              (definitionallyEqualTy sourceTy targetTy)
              explicitEvidenceAccepted of
            ResourceLoopKernel.StateTransportAcceptedDecision ->
              Right source
                { valueResultType = targetTy
                , valueResultEvidence = appendEvidenceList evidenceUses (valueResultEvidence source)
                }
            _ -> resourceLoopKernelInvariant \"explicit-transport\"
"""
assert old in text
text = text.replace(old, new, 1)

marker = """compareTypes :: Ty -> Ty -> EqualityBoundary
"""
helper = """resourceLoopKernelInvariant :: String -> Either e a
resourceLoopKernelInvariant label =
  error (\"ResourceLoopKernel mismatch: \" <> label)

"""
assert marker in text
text = text.replace(marker, helper + marker, 1)
path.write_text(text)

path = Path("phil-core.cabal")
text = path.read_text()
old = """      ResourceJoinKernel
      ResourceScopeKernel
"""
new = """      ResourceJoinKernel
      ResourceLoopKernel
      ResourceScopeKernel
"""
assert old in text
text = text.replace(old, new, 1)
path.write_text(text)
