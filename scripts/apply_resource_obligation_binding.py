from pathlib import Path

process = Path("src/Phil/Core/Process.hs")
text = process.read_text()
old = "import Phil.Core.Syntax (Control (..), Outcome, Ty)\n"
new = "import Phil.Core.Syntax (Control (..), Outcome, Ty)\nimport qualified ResourceObligationKernel as ResourceObligationKernel\n"
assert old in text
text = text.replace(old, new, 1)

old = '''joinBranches :: [ProcessFlow] -> Either ProcessError ProcessFlow
joinBranches [] = Left EmptyBranchSet
joinBranches flows = do
  let paths = concatMap unProcessFlow flows
      continuingPaths = filter ((== Continue) . pathControl) paths
  joinedContext <-
    case continuingPaths of
      [] -> pure Nothing
      _ -> Just <$> mapLeft BranchJoinError
        (joinContinuing (map (resourceContext . pathState) continuingPaths))
  pure (ProcessFlow (map (normalizeContinue joinedContext) paths))
'''
new = '''joinBranches :: [ProcessFlow] -> Either ProcessError ProcessFlow
joinBranches [] = Left EmptyBranchSet
joinBranches flows = do
  let paths = concatMap unProcessFlow flows
      continuingPaths = filter ((== Continue) . pathControl) paths
  joinedContext <-
    case continuingPaths of
      [] -> pure Nothing
      _ -> Just <$> mapLeft BranchJoinError
        (joinContinuing (map (resourceContext . pathState) continuingPaths))
  let normalizedPaths = map (normalizeContinue joinedContext) paths
  pure (ProcessFlow (zipWith checkObligationReconvergence paths normalizedPaths))

checkObligationReconvergence :: FlowPath -> FlowPath -> FlowPath
checkObligationReconvergence before after
  | pathControl before /= Continue = after
  | all obligationPreserved obligationIds = after
  | otherwise = resourceObligationKernelInvariant
  where
    beforeObligations = residualObligations (pathState before)
    afterObligations = residualObligations (pathState after)
    obligationIds = Set.toList
      (Map.keysSet beforeObligations `Set.union` Map.keysSet afterObligations)
    obligationPreserved obligationId =
      case ResourceObligationKernel.decidePendingObligationReconvergenceByFacts
          (Map.member obligationId beforeObligations)
          (Map.member obligationId afterObligations) of
        ResourceObligationKernel.PendingObligationAcceptedDecision -> True
        ResourceObligationKernel.PendingObligationLostDecision -> False

resourceObligationKernelInvariant :: a
resourceObligationKernelInvariant =
  error "ResourceObligationKernel mismatch: continuing-path obligation lost at reconvergence"
'''
assert old in text
text = text.replace(old, new, 1)
process.write_text(text)

cabal = Path("phil-core.cabal")
text = cabal.read_text()
old = '''      ResourceJoinKernel
      ResourceLoopKernel
      ResourceScopeKernel
'''
new = '''      ResourceJoinKernel
      ResourceLoopKernel
      ResourceObligationKernel
      ResourceScopeKernel
'''
assert old in text
text = text.replace(old, new, 1)
cabal.write_text(text)
