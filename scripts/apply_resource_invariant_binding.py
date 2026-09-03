from pathlib import Path

path = Path("src/Phil/Systems/ControlStateInvariant.hs")
text = path.read_text()

old = '''import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey
  , SystemsValueRef
  )
'''
new = '''import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey
  , SystemsValueRef
  )
import qualified ResourceInvariantKernel as ResourceInvariantKernel
'''
assert old in text
text = text.replace(old, new, 1)

old = '''  let expectedPredecessors = Set.fromList (map stateProjectionKey projections)
      actualPredecessors = Map.keysSet predecessors
  requireEqual (StateInvariantPredecessorDomainMismatch (stateBoundaryKey boundary))
    expectedPredecessors actualPredecessors
  mapM_ checkOne (sortOn stateProjectionKey projections)
'''
new = '''  let expectedPredecessors = Set.fromList (map stateProjectionKey projections)
      actualPredecessors = Map.keysSet predecessors
  requireEqual (StateInvariantPredecessorDomainMismatch (stateBoundaryKey boundary))
    expectedPredecessors actualPredecessors
  establishedProjectionKeys <- mapM checkOne (sortOn stateProjectionKey projections)
  let predecessorsDistinct =
        firstDuplicate (map stateProjectionKey projections) == Nothing
      -- This fact is sequenced only after the real structural checker above
      -- returned Right ().  No structural success is fabricated here.
      structuralAccepted = True
      expectedSlotsForKernel = Map.keysSet (stateBoundarySlots boundary)
      witnessesExact = all
        (\\projection ->
          case Map.lookup (stateProjectionKey projection) predecessors of
            Nothing -> False
            Just predecessor ->
              Map.keysSet (stateInvariantPredecessorSlots predecessor)
                == expectedSlotsForKernel)
        projections
      invariantEstablished =
        Set.fromList establishedProjectionKeys == expectedPredecessors
  case ResourceInvariantKernel.decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished of
    ResourceInvariantKernel.InvariantBoundaryAcceptedDecision -> Right ()
    _ -> resourceInvariantKernelInvariant
'''
assert old in text
text = text.replace(old, new, 1)

old = '''      establishInvariant
        staticContext
        projectionKey
        (stateInvariantPredecessorState predecessor)
        instantiated
'''
new = '''      establishInvariant
        staticContext
        projectionKey
        (stateInvariantPredecessorState predecessor)
        instantiated
      Right projectionKey
'''
assert old in text
text = text.replace(old, new, 1)

old = '''firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
'''
new = '''resourceInvariantKernelInvariant :: a
resourceInvariantKernelInvariant =
  error "ResourceInvariantKernel mismatch: accepted invariant boundary rejected"

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
'''
assert old in text
text = text.replace(old, new, 1)
path.write_text(text)

cabal = Path("phil-core.cabal")
text = cabal.read_text()
old = '''      ResourceJoinKernel
      ResourceLoopKernel
      ResourceObligationKernel
      ResourceScopeKernel
'''
new = '''      ResourceInvariantKernel
      ResourceJoinKernel
      ResourceLoopKernel
      ResourceObligationKernel
      ResourceScopeKernel
'''
assert old in text
text = text.replace(old, new, 1)
cabal.write_text(text)
