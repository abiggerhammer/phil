module BoundaryEncodingKernel where

import qualified Prelude

data EncodingCanonicality =
   CanonicalityNotRequired
 | CanonicalEncodingRequired

data EncodingForm =
   CanonicalGrammarMember
 | NonCanonicalLegalGrammarMember

data SerializationBasis =
   CheckedWireCorrespondence
 | RawMemoryLayout
 | MatchingCStructShape

data QualifiedEncodingDecision =
   QualifiedEncodingDecisionAccepted
 | QualifiedEncoderNotAdmittedDecision
 | QualifiedEncodingRepresentationMismatchDecision
 | QualifiedEncodingOutputOwnerMismatchDecision

decideQualifiedEncodingByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> QualifiedEncodingDecision
decideQualifiedEncodingByFacts encoderAdmitted representationMatches outputOwnerMatches =
  case encoderAdmitted of {
   Prelude.True ->
    case representationMatches of {
     Prelude.True ->
      case outputOwnerMatches of {
       Prelude.True -> QualifiedEncodingDecisionAccepted;
       Prelude.False -> QualifiedEncodingOutputOwnerMismatchDecision};
     Prelude.False -> QualifiedEncodingRepresentationMismatchDecision};
   Prelude.False -> QualifiedEncoderNotAdmittedDecision}

data GeneratedEncodingPlan implementation representation owner =
   MkGeneratedEncodingPlan implementation representation owner

planGeneratedEncoding :: a1 -> a2 -> a3 -> GeneratedEncodingPlan a1 a2 a3
planGeneratedEncoding implementationId representationId outputOwner =
  MkGeneratedEncodingPlan implementationId representationId outputOwner

data EncodingCanonicalityDecision =
   EncodingCanonicalityAccepted
 | NonCanonicalEncodingRejectedDecision

decideEncodingCanonicality :: EncodingCanonicality -> EncodingForm ->
                              EncodingCanonicalityDecision
decideEncodingCanonicality requirement encodingForm =
  case requirement of {
   CanonicalityNotRequired -> EncodingCanonicalityAccepted;
   CanonicalEncodingRequired ->
    case encodingForm of {
     CanonicalGrammarMember -> EncodingCanonicalityAccepted;
     NonCanonicalLegalGrammarMember -> NonCanonicalEncodingRejectedDecision}}

data BoundarySerializationDecision =
   BoundarySerializationDecisionAccepted
 | RawMemoryLayoutRejectedDecision
 | MatchingCStructShapeRejectedDecision
 | SerializationRepresentationMismatchDecision
 | SerializationSubjectMismatchDecision

decideBoundarySerializationByFacts :: SerializationBasis -> Prelude.Bool ->
                                      Prelude.Bool ->
                                      BoundarySerializationDecision
decideBoundarySerializationByFacts basis representationMatches subjectMatches =
  case basis of {
   CheckedWireCorrespondence ->
    case representationMatches of {
     Prelude.True ->
      case subjectMatches of {
       Prelude.True -> BoundarySerializationDecisionAccepted;
       Prelude.False -> SerializationSubjectMismatchDecision};
     Prelude.False -> SerializationRepresentationMismatchDecision};
   RawMemoryLayout -> RawMemoryLayoutRejectedDecision;
   MatchingCStructShape -> MatchingCStructShapeRejectedDecision}

