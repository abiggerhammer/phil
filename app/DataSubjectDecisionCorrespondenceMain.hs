module Main (main) where

import Control.Monad (unless)
import DataSubjectKernel

assert :: String -> Bool -> IO ()
assert label condition = do
  unless condition (error ("FAIL: " ++ label))
  putStrLn ("PASS: " ++ label)

isPrerequisitesAccepted :: DataSubjectPrerequisiteDecision -> Bool
isPrerequisitesAccepted decision = case decision of
  DataSubjectPrerequisitesAccepted -> True
  _ -> False

isPriorNotConsumed :: DataSubjectPrerequisiteDecision -> Bool
isPriorNotConsumed decision = case decision of
  DataSubjectPriorNotConsumedDecision -> True
  _ -> False

isReplacementNotConstructed :: DataSubjectPrerequisiteDecision -> Bool
isReplacementNotConstructed decision = case decision of
  DataSubjectReplacementNotConstructedDecision -> True
  _ -> False

isPriorNotStable :: DataSubjectPrerequisiteDecision -> Bool
isPriorNotStable decision = case decision of
  DataSubjectPriorNotStableDecision -> True
  _ -> False

isReplacementNotStable :: DataSubjectPrerequisiteDecision -> Bool
isReplacementNotStable decision = case decision of
  DataSubjectReplacementNotStableDecision -> True
  _ -> False

isKindMismatch :: DataSubjectPrerequisiteDecision -> Bool
isKindMismatch decision = case decision of
  DataSubjectKindMismatchDecision -> True
  _ -> False

isTemplateMissingSubject :: DataSubjectPrerequisiteDecision -> Bool
isTemplateMissingSubject decision = case decision of
  DataSubjectEvidenceTemplateMissingSubjectDecision -> True
  _ -> False

isEvidencePriorMismatch :: DataSubjectPrerequisiteDecision -> Bool
isEvidencePriorMismatch decision = case decision of
  DataSubjectEvidencePriorMismatchDecision -> True
  _ -> False

isEvidenceNotStable :: DataSubjectPrerequisiteDecision -> Bool
isEvidenceNotStable decision = case decision of
  DataSubjectEvidenceNotStableDecision -> True
  _ -> False

isEvidenceKindMismatch :: DataSubjectPrerequisiteDecision -> Bool
isEvidenceKindMismatch decision = case decision of
  DataSubjectEvidenceKindMismatchDecision -> True
  _ -> False

isModeAccepted :: DataSubjectTransportModeDecision -> Bool
isModeAccepted decision = case decision of
  DataSubjectTransportModeAccepted -> True
  _ -> False

isUnexpectedTransport :: DataSubjectTransportModeDecision -> Bool
isUnexpectedTransport decision = case decision of
  DataSubjectUnexpectedTransportDecision -> True
  _ -> False

isTransportRequired :: DataSubjectTransportModeDecision -> Bool
isTransportRequired decision = case decision of
  DataSubjectTransportRequiredDecision -> True
  _ -> False

isTransportAccepted :: DataSubjectTransportDecision -> Bool
isTransportAccepted decision = case decision of
  DataSubjectTransportAcceptedDecision -> True
  _ -> False

isDispositionRejected :: DataSubjectTransportDecision -> Bool
isDispositionRejected decision = case decision of
  DataSubjectTransportDispositionRejectedDecision -> True
  _ -> False

isRevisionMissing :: DataSubjectTransportDecision -> Bool
isRevisionMissing decision = case decision of
  DataSubjectTransportRevisionMissingDecision -> True
  _ -> False

isTransportEvidenceMismatch :: DataSubjectTransportDecision -> Bool
isTransportEvidenceMismatch decision = case decision of
  DataSubjectTransportEvidenceMismatchDecision -> True
  _ -> False

isTransportPriorMismatch :: DataSubjectTransportDecision -> Bool
isTransportPriorMismatch decision = case decision of
  DataSubjectTransportPriorMismatchDecision -> True
  _ -> False

isTransportReplacementMismatch :: DataSubjectTransportDecision -> Bool
isTransportReplacementMismatch decision = case decision of
  DataSubjectTransportReplacementMismatchDecision -> True
  _ -> False

isSourceMismatch :: DataSubjectTransportDecision -> Bool
isSourceMismatch decision = case decision of
  DataSubjectTransportSourcePropositionMismatchDecision -> True
  _ -> False

isTargetMismatch :: DataSubjectTransportDecision -> Bool
isTargetMismatch decision = case decision of
  DataSubjectTransportTargetPropositionMismatchDecision -> True
  _ -> False

main :: IO ()
main = do
  let prerequisites = decideDataSubjectPrerequisites
      transport = decideDataSubjectTransport
  assert "all prerequisite facts accept"
    (isPrerequisitesAccepted (prerequisites True True True True True True True True True))
  assert "prior consumption rejects first"
    (isPriorNotConsumed (prerequisites False False False False False False False False False))
  assert "replacement construction is second gate"
    (isReplacementNotConstructed (prerequisites True False False False False False False False False))
  assert "prior stability is third gate"
    (isPriorNotStable (prerequisites True True False False False False False False False))
  assert "replacement stability is fourth gate"
    (isReplacementNotStable (prerequisites True True True False False False False False False))
  assert "stable kind match is fifth gate"
    (isKindMismatch (prerequisites True True True True False False False False False))
  assert "evidence template subject mention is sixth gate"
    (isTemplateMissingSubject (prerequisites True True True True True False False False False))
  assert "exact evidence prior binding is seventh gate"
    (isEvidencePriorMismatch (prerequisites True True True True True True False False False))
  assert "evidence stability is eighth gate"
    (isEvidenceNotStable (prerequisites True True True True True True True False False))
  assert "evidence kind match is ninth gate"
    (isEvidenceKindMismatch (prerequisites True True True True True True True True False))

  assert "same subject without transport accepts"
    (isModeAccepted (decideDataSubjectTransportMode True False))
  assert "same subject with transport rejects"
    (isUnexpectedTransport (decideDataSubjectTransportMode True True))
  assert "changed subject without transport requires transport"
    (isTransportRequired (decideDataSubjectTransportMode False False))
  assert "changed subject with transport proceeds"
    (isModeAccepted (decideDataSubjectTransportMode False True))

  assert "all exact transport facts accept"
    (isTransportAccepted (transport True True True True True True True))
  assert "transport disposition rejects first"
    (isDispositionRejected (transport False False False False False False False))
  assert "transport revision is second gate"
    (isRevisionMissing (transport True False False False False False False))
  assert "transport evidence reference is third gate"
    (isTransportEvidenceMismatch (transport True True False False False False False))
  assert "transport prior identity is fourth gate"
    (isTransportPriorMismatch (transport True True True False False False False))
  assert "transport replacement identity is fifth gate"
    (isTransportReplacementMismatch (transport True True True True False False False))
  assert "transport source proposition is sixth gate"
    (isSourceMismatch (transport True True True True True False False))
  assert "transport target proposition is final gate"
    (isTargetMismatch (transport True True True True True True False))
