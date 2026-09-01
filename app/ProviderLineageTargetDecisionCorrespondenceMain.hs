module Main (main) where

import ProviderQualificationLineageTargetKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then putStrLn ("PASS: " ++ label)
  else error ("provider lineage target correspondence failed: " ++ label)

isReuse :: TargetReuseDecision -> TargetReuseDecision -> Bool
isReuse expected actual = case (expected, actual) of
  (TargetReuseAcceptedDecision, TargetReuseAcceptedDecision) -> True
  (TargetReuseSemanticLayerDecision, TargetReuseSemanticLayerDecision) -> True
  (TargetReuseSemanticSubjectDecision, TargetReuseSemanticSubjectDecision) -> True
  (TargetReusePriorClaimDecision, TargetReusePriorClaimDecision) -> True
  (TargetReusePriorInterfaceDecision, TargetReusePriorInterfaceDecision) -> True
  (TargetReusePriorImplementationDecision, TargetReusePriorImplementationDecision) -> True
  (TargetReusePriorTranslationDecision, TargetReusePriorTranslationDecision) -> True
  (TargetReuseNewClaimDecision, TargetReuseNewClaimDecision) -> True
  (TargetReuseNewInterfaceDecision, TargetReuseNewInterfaceDecision) -> True
  (TargetReuseNewImplementationDecision, TargetReuseNewImplementationDecision) -> True
  (TargetReuseNewTranslationDecision, TargetReuseNewTranslationDecision) -> True
  (TargetReuseDistinctProfileDecision, TargetReuseDistinctProfileDecision) -> True
  _ -> False

isApplicability :: AdmissionApplicabilityDecision -> AdmissionApplicabilityDecision -> Bool
isApplicability expected actual = case (expected, actual) of
  (AdmissionApplicabilityAcceptedDecision, AdmissionApplicabilityAcceptedDecision) -> True
  (AdmissionApplicabilityRejectedDecision, AdmissionApplicabilityRejectedDecision) -> True
  (AdmissionApplicabilityAdmissionRevisionDecision, AdmissionApplicabilityAdmissionRevisionDecision) -> True
  (AdmissionApplicabilityClaimRevisionDecision, AdmissionApplicabilityClaimRevisionDecision) -> True
  (AdmissionApplicabilityTargetEvidenceRevisionDecision, AdmissionApplicabilityTargetEvidenceRevisionDecision) -> True
  (AdmissionApplicabilityTargetEvidenceClaimDecision, AdmissionApplicabilityTargetEvidenceClaimDecision) -> True
  (AdmissionApplicabilityInterfaceEvidenceDecision, AdmissionApplicabilityInterfaceEvidenceDecision) -> True
  (AdmissionApplicabilityImplementationEvidenceDecision, AdmissionApplicabilityImplementationEvidenceDecision) -> True
  (AdmissionApplicabilityTargetEvidenceDecision, AdmissionApplicabilityTargetEvidenceDecision) -> True
  (AdmissionApplicabilityArtifactEvidenceDecision, AdmissionApplicabilityArtifactEvidenceDecision) -> True
  (AdmissionApplicabilityAbiEvidenceDecision, AdmissionApplicabilityAbiEvidenceDecision) -> True
  (AdmissionApplicabilitySelectedAdmissionDecision, AdmissionApplicabilitySelectedAdmissionDecision) -> True
  (AdmissionApplicabilitySelectedEvidenceDecision, AdmissionApplicabilitySelectedEvidenceDecision) -> True
  (AdmissionApplicabilitySelectedOccurrenceDecision, AdmissionApplicabilitySelectedOccurrenceDecision) -> True
  (AdmissionApplicabilitySelectedInstanceDecision, AdmissionApplicabilitySelectedInstanceDecision) -> True
  (AdmissionApplicabilitySelectedRealizationDecision, AdmissionApplicabilitySelectedRealizationDecision) -> True
  (AdmissionApplicabilitySelectedInterfaceDecision, AdmissionApplicabilitySelectedInterfaceDecision) -> True
  (AdmissionApplicabilitySelectedImplementationDecision, AdmissionApplicabilitySelectedImplementationDecision) -> True
  (AdmissionApplicabilitySelectedTargetDecision, AdmissionApplicabilitySelectedTargetDecision) -> True
  (AdmissionApplicabilitySelectedArtifactDecision, AdmissionApplicabilitySelectedArtifactDecision) -> True
  (AdmissionApplicabilitySelectedAbiDecision, AdmissionApplicabilitySelectedAbiDecision) -> True
  _ -> False

reuse :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> TargetReuseDecision
reuse = decideTargetReuseByFacts

app :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
    -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
    -> AdmissionApplicabilityDecision
app = decideAdmissionApplicabilityByFacts

main :: IO ()
main = do
  assert "PROV-013 exact cross-target reuse accepts" $
    isReuse TargetReuseAcceptedDecision
      (reuse True True True True True True True True True True True)
  assert "PROV-013 semantic layer is first gate" $
    isReuse TargetReuseSemanticLayerDecision
      (reuse False True True True True True True True True True True)
  assert "PROV-013 semantic subject is required" $
    isReuse TargetReuseSemanticSubjectDecision
      (reuse True False True True True True True True True True True)
  assert "PROV-013 prior claim must match" $
    isReuse TargetReusePriorClaimDecision
      (reuse True True False True True True True True True True True)
  assert "PROV-013 prior interface must match" $
    isReuse TargetReusePriorInterfaceDecision
      (reuse True True True False True True True True True True True)
  assert "PROV-013 prior implementation must match" $
    isReuse TargetReusePriorImplementationDecision
      (reuse True True True True False True True True True True True)
  assert "PROV-013 prior translation evidence is required" $
    isReuse TargetReusePriorTranslationDecision
      (reuse True True True True True False True True True True True)
  assert "PROV-013 new claim must match" $
    isReuse TargetReuseNewClaimDecision
      (reuse True True True True True True False True True True True)
  assert "PROV-013 new interface must match" $
    isReuse TargetReuseNewInterfaceDecision
      (reuse True True True True True True True False True True True)
  assert "PROV-013 new implementation must match" $
    isReuse TargetReuseNewImplementationDecision
      (reuse True True True True True True True True False True True)
  assert "PROV-013 new translation evidence is required" $
    isReuse TargetReuseNewTranslationDecision
      (reuse True True True True True True True True True False True)
  assert "PROV-013 target profiles must be distinct" $
    isReuse TargetReuseDistinctProfileDecision
      (reuse True True True True True True True True True True False)

  assert "PROV-014 exact concrete applicability accepts" $
    isApplicability AdmissionApplicabilityAcceptedDecision
      (app True True True True True True True True True True True True True True True True True True True True)
  assert "PROV-014 rejected admission is first gate" $
    isApplicability AdmissionApplicabilityRejectedDecision
      (app False True True True True True True True True True True True True True True True True True True True)
  assert "PROV-014 admission revision must match" $
    isApplicability AdmissionApplicabilityAdmissionRevisionDecision
      (app True False True True True True True True True True True True True True True True True True True True)
  assert "PROV-014 claim revision must match" $
    isApplicability AdmissionApplicabilityClaimRevisionDecision
      (app True True False True True True True True True True True True True True True True True True True True)
  assert "PROV-014 target evidence revision must match" $
    isApplicability AdmissionApplicabilityTargetEvidenceRevisionDecision
      (app True True True False True True True True True True True True True True True True True True True True)
  assert "PROV-014 target evidence claim must match" $
    isApplicability AdmissionApplicabilityTargetEvidenceClaimDecision
      (app True True True True False True True True True True True True True True True True True True True True)
  assert "PROV-014 applicability interface must match evidence" $
    isApplicability AdmissionApplicabilityInterfaceEvidenceDecision
      (app True True True True True False True True True True True True True True True True True True True True)
  assert "PROV-014 applicability implementation must match evidence" $
    isApplicability AdmissionApplicabilityImplementationEvidenceDecision
      (app True True True True True True False True True True True True True True True True True True True True)
  assert "PROV-014 applicability target must match evidence" $
    isApplicability AdmissionApplicabilityTargetEvidenceDecision
      (app True True True True True True True False True True True True True True True True True True True True)
  assert "PROV-014 applicability artifact must match evidence" $
    isApplicability AdmissionApplicabilityArtifactEvidenceDecision
      (app True True True True True True True True False True True True True True True True True True True True)
  assert "PROV-014 applicability ABI must match evidence" $
    isApplicability AdmissionApplicabilityAbiEvidenceDecision
      (app True True True True True True True True True False True True True True True True True True True True)
  assert "PROV-014 selected admission must match" $
    isApplicability AdmissionApplicabilitySelectedAdmissionDecision
      (app True True True True True True True True True True False True True True True True True True True True)
  assert "PROV-014 selected evidence must match" $
    isApplicability AdmissionApplicabilitySelectedEvidenceDecision
      (app True True True True True True True True True True True False True True True True True True True True)
  assert "PROV-014 selected occurrence must match" $
    isApplicability AdmissionApplicabilitySelectedOccurrenceDecision
      (app True True True True True True True True True True True True False True True True True True True True)
  assert "PROV-014 selected instance must match" $
    isApplicability AdmissionApplicabilitySelectedInstanceDecision
      (app True True True True True True True True True True True True True False True True True True True True)
  assert "PROV-014 selected realization must match" $
    isApplicability AdmissionApplicabilitySelectedRealizationDecision
      (app True True True True True True True True True True True True True True False True True True True True)
  assert "PROV-014 selected interface must match" $
    isApplicability AdmissionApplicabilitySelectedInterfaceDecision
      (app True True True True True True True True True True True True True True True False True True True True)
  assert "PROV-014 selected implementation must match" $
    isApplicability AdmissionApplicabilitySelectedImplementationDecision
      (app True True True True True True True True True True True True True True True True False True True True)
  assert "PROV-014 selected target must match" $
    isApplicability AdmissionApplicabilitySelectedTargetDecision
      (app True True True True True True True True True True True True True True True True True False True True)
  assert "PROV-014 selected artifact must match" $
    isApplicability AdmissionApplicabilitySelectedArtifactDecision
      (app True True True True True True True True True True True True True True True True True True False True)
  assert "PROV-014 selected ABI must match" $
    isApplicability AdmissionApplicabilitySelectedAbiDecision
      (app True True True True True True True True True True True True True True True True True True True False)
