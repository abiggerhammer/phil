module Main (main) where

import BoundaryEncodingKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "qualified encoding accepts exact reflected facts"
        (assertQualifiedAccepted (decideQualifiedEncodingByFacts True True True))
    , test "unadmitted encoder rejects first"
        (assertEncoderNotAdmitted (decideQualifiedEncodingByFacts False False False))
    , test "representation mismatch precedes owner mismatch"
        (assertEncodingRepresentationMismatch (decideQualifiedEncodingByFacts True False False))
    , test "owner mismatch rejects last"
        (assertEncodingOwnerMismatch (decideQualifiedEncodingByFacts True True False))
    , test "generated evidence plan preserves exact coordinates"
        assertExactGeneratedPlan
    , test "noncanonical legal member is accepted when canonicality is not required"
        (assertCanonicalityAccepted
          (decideEncodingCanonicality CanonicalityNotRequired NonCanonicalLegalGrammarMember))
    , test "canonical member is accepted when canonicality is required"
        (assertCanonicalityAccepted
          (decideEncodingCanonicality CanonicalEncodingRequired CanonicalGrammarMember))
    , test "declared canonicality rejects a noncanonical legal member"
        (assertNonCanonicalRejected
          (decideEncodingCanonicality CanonicalEncodingRequired NonCanonicalLegalGrammarMember))
    , test "raw memory never establishes serialization correspondence"
        (assertRawMemoryRejected
          (decideBoundarySerializationByFacts RawMemoryLayout True True))
    , test "matching C struct shape never establishes serialization correspondence"
        (assertMatchingStructRejected
          (decideBoundarySerializationByFacts MatchingCStructShape True True))
    , test "checked wire representation mismatch rejects before subject"
        (assertSerializationRepresentationMismatch
          (decideBoundarySerializationByFacts CheckedWireCorrespondence False False))
    , test "checked wire subject mismatch rejects last"
        (assertSerializationSubjectMismatch
          (decideBoundarySerializationByFacts CheckedWireCorrespondence True False))
    , test "exact checked wire facts accept"
        (assertSerializationAccepted
          (decideBoundarySerializationByFacts CheckedWireCorrespondence True True))
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

assertQualifiedAccepted :: QualifiedEncodingDecision -> Either String ()
assertQualifiedAccepted decision = case decision of
  QualifiedEncodingDecisionAccepted -> Right ()
  _ -> Left "expected QualifiedEncodingDecisionAccepted"

assertEncoderNotAdmitted :: QualifiedEncodingDecision -> Either String ()
assertEncoderNotAdmitted decision = case decision of
  QualifiedEncoderNotAdmittedDecision -> Right ()
  _ -> Left "expected QualifiedEncoderNotAdmittedDecision"

assertEncodingRepresentationMismatch :: QualifiedEncodingDecision -> Either String ()
assertEncodingRepresentationMismatch decision = case decision of
  QualifiedEncodingRepresentationMismatchDecision -> Right ()
  _ -> Left "expected QualifiedEncodingRepresentationMismatchDecision"

assertEncodingOwnerMismatch :: QualifiedEncodingDecision -> Either String ()
assertEncodingOwnerMismatch decision = case decision of
  QualifiedEncodingOutputOwnerMismatchDecision -> Right ()
  _ -> Left "expected QualifiedEncodingOutputOwnerMismatchDecision"

assertExactGeneratedPlan :: Either String ()
assertExactGeneratedPlan =
  case planGeneratedEncoding "encoder" "representation" "owner" of
    MkGeneratedEncodingPlan implementation representation owner
      | implementation == "encoder"
      , representation == "representation"
      , owner == "owner" -> Right ()
      | otherwise -> Left "generated encoding plan changed an exact coordinate"

assertCanonicalityAccepted :: EncodingCanonicalityDecision -> Either String ()
assertCanonicalityAccepted decision = case decision of
  EncodingCanonicalityAccepted -> Right ()
  _ -> Left "expected EncodingCanonicalityAccepted"

assertNonCanonicalRejected :: EncodingCanonicalityDecision -> Either String ()
assertNonCanonicalRejected decision = case decision of
  NonCanonicalEncodingRejectedDecision -> Right ()
  _ -> Left "expected NonCanonicalEncodingRejectedDecision"

assertRawMemoryRejected :: BoundarySerializationDecision -> Either String ()
assertRawMemoryRejected decision = case decision of
  RawMemoryLayoutRejectedDecision -> Right ()
  _ -> Left "expected RawMemoryLayoutRejectedDecision"

assertMatchingStructRejected :: BoundarySerializationDecision -> Either String ()
assertMatchingStructRejected decision = case decision of
  MatchingCStructShapeRejectedDecision -> Right ()
  _ -> Left "expected MatchingCStructShapeRejectedDecision"

assertSerializationRepresentationMismatch :: BoundarySerializationDecision -> Either String ()
assertSerializationRepresentationMismatch decision = case decision of
  SerializationRepresentationMismatchDecision -> Right ()
  _ -> Left "expected SerializationRepresentationMismatchDecision"

assertSerializationSubjectMismatch :: BoundarySerializationDecision -> Either String ()
assertSerializationSubjectMismatch decision = case decision of
  SerializationSubjectMismatchDecision -> Right ()
  _ -> Left "expected SerializationSubjectMismatchDecision"

assertSerializationAccepted :: BoundarySerializationDecision -> Either String ()
assertSerializationAccepted decision = case decision of
  BoundarySerializationDecisionAccepted -> Right ()
  _ -> Left "expected BoundarySerializationDecisionAccepted"
