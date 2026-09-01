module Main (main) where

import ProviderQualificationLineageCoreKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then putStrLn ("PASS: " ++ label)
  else error ("provider lineage core correspondence failed: " ++ label)

isIdentity :: QualificationIdentityDecision -> QualificationIdentityDecision -> Bool
isIdentity expected actual = case (expected, actual) of
  (QualificationIdentityAcceptedDecision, QualificationIdentityAcceptedDecision) -> True
  (QualificationEvidenceClaimDecision, QualificationEvidenceClaimDecision) -> True
  (QualificationAdmissionClaimDecision, QualificationAdmissionClaimDecision) -> True
  (QualificationAdmissionEvidenceDecision, QualificationAdmissionEvidenceDecision) -> True
  (QualificationAdmissionInterfaceDecision, QualificationAdmissionInterfaceDecision) -> True
  _ -> False

isRegistry :: QualificationRegistryDecision -> QualificationRegistryDecision -> Bool
isRegistry expected actual = case (expected, actual) of
  (QualificationRegistryAcceptedDecision, QualificationRegistryAcceptedDecision) -> True
  (QualificationNodeKeyDecision, QualificationNodeKeyDecision) -> True
  (QualificationGroundKeyDecision, QualificationGroundKeyDecision) -> True
  _ -> False

isRoot :: QualificationRootDecision -> QualificationRootDecision -> Bool
isRoot expected actual = case (expected, actual) of
  (QualificationRootAcceptedDecision, QualificationRootAcceptedDecision) -> True
  (QualificationUnknownRootDecision, QualificationUnknownRootDecision) -> True
  _ -> False

isNode :: QualificationDependencyNodeDecision -> QualificationDependencyNodeDecision -> Bool
isNode expected actual = case (expected, actual) of
  (QualificationDependencyNodeAcceptedDecision, QualificationDependencyNodeAcceptedDecision) -> True
  (QualificationRejectedAdmissionDecision, QualificationRejectedAdmissionDecision) -> True
  (QualificationUnknownAdmissionDecision, QualificationUnknownAdmissionDecision) -> True
  (QualificationUnknownGroundDecision, QualificationUnknownGroundDecision) -> True
  (QualificationRejectedGroundDecision, QualificationRejectedGroundDecision) -> True
  _ -> False

isClosure :: QualificationDependencyClosureDecision -> QualificationDependencyClosureDecision -> Bool
isClosure expected actual = case (expected, actual) of
  (QualificationDependencyClosureAcceptedDecision, QualificationDependencyClosureAcceptedDecision) -> True
  (QualificationDependencyUngroundedDecision, QualificationDependencyUngroundedDecision) -> True
  _ -> False

main :: IO ()
main = do
  assert "exact claim/evidence/admission identity accepts" $
    isIdentity QualificationIdentityAcceptedDecision
      (decideQualificationIdentityByFacts True True True True)
  assert "evidence claim revision is first identity gate" $
    isIdentity QualificationEvidenceClaimDecision
      (decideQualificationIdentityByFacts False True True True)
  assert "admission claim revision is required" $
    isIdentity QualificationAdmissionClaimDecision
      (decideQualificationIdentityByFacts True False True True)
  assert "admission evidence revision is required" $
    isIdentity QualificationAdmissionEvidenceDecision
      (decideQualificationIdentityByFacts True True False True)
  assert "admission interface revision is final identity gate" $
    isIdentity QualificationAdmissionInterfaceDecision
      (decideQualificationIdentityByFacts True True True False)

  assert "exact dependency registries accept" $
    isRegistry QualificationRegistryAcceptedDecision
      (decideQualificationRegistryByFacts True True)
  assert "node key mismatch precedes ground registry mismatch" $
    isRegistry QualificationNodeKeyDecision
      (decideQualificationRegistryByFacts False False)
  assert "ground registry keys must be exact" $
    isRegistry QualificationGroundKeyDecision
      (decideQualificationRegistryByFacts True False)

  assert "known root accepts" $
    isRoot QualificationRootAcceptedDecision
      (decideQualificationRootByFacts True)
  assert "unknown root rejects" $
    isRoot QualificationUnknownRootDecision
      (decideQualificationRootByFacts False)

  assert "accepted dependency node with exact references accepts" $
    isNode QualificationDependencyNodeAcceptedDecision
      (decideQualificationDependencyNodeByFacts True True True True)
  assert "rejected admission is first node gate" $
    isNode QualificationRejectedAdmissionDecision
      (decideQualificationDependencyNodeByFacts False True True True)
  assert "unknown admission dependency rejects" $
    isNode QualificationUnknownAdmissionDecision
      (decideQualificationDependencyNodeByFacts True False True True)
  assert "unknown ground rejects" $
    isNode QualificationUnknownGroundDecision
      (decideQualificationDependencyNodeByFacts True True False True)
  assert "rejected ground is final node-validation gate" $
    isNode QualificationRejectedGroundDecision
      (decideQualificationDependencyNodeByFacts True True True False)

  assert "direct ground survives propagation" $
    propagateGroundPresence True []
  assert "dependency ground is inherited" $
    propagateGroundPresence False [False, True, False]
  assert "multiple absent dependency grounds remain absent" $
    not (propagateGroundPresence False [False, False, False])
  assert "direct ground remains present despite absent dependencies" $
    propagateGroundPresence True [False, False]

  assert "fully grounded reachable closure accepts" $
    isClosure QualificationDependencyClosureAcceptedDecision
      (decideQualificationDependencyClosureByFacts True)
  assert "ungrounded reachable closure rejects" $
    isClosure QualificationDependencyUngroundedDecision
      (decideQualificationDependencyClosureByFacts False)
