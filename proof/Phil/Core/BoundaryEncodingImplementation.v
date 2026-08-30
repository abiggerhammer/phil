From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import BoundaryEncoding.

Set Implicit Arguments.

(*
  PHIL-BND-ENCODE-001 — representation-neutral implementation correspondence.

  Production reflects concrete Haskell admission/equality facts into Boolean
  inputs. This layer owns the Certified rejection order for qualified encoding,
  the exact generated-evidence construction coordinates, the explicit
  canonicality decision, and checked-wire serialization gating.
*)

Inductive QualifiedEncodingDecision : Type :=
| QualifiedEncodingDecisionAccepted
| QualifiedEncoderNotAdmittedDecision
| QualifiedEncodingRepresentationMismatchDecision
| QualifiedEncodingOutputOwnerMismatchDecision.

Definition decideQualifiedEncodingByFacts
  (encoderAdmitted representationMatches outputOwnerMatches : bool)
  : QualifiedEncodingDecision :=
  if encoderAdmitted then
    if representationMatches then
      if outputOwnerMatches then
        QualifiedEncodingDecisionAccepted
      else QualifiedEncodingOutputOwnerMismatchDecision
    else QualifiedEncodingRepresentationMismatchDecision
  else QualifiedEncoderNotAdmittedDecision.

Record GeneratedEncodingPlan
  (implementation representation owner : Type) : Type :=
  mkGeneratedEncodingPlan {
    plannedEncoderImplementation : implementation;
    plannedEncodingRepresentation : representation;
    plannedEncodingOutputOwner : owner
  }.

Definition planGeneratedEncoding
  {implementation representation owner : Type}
  (implementationId : implementation)
  (representationId : representation)
  (outputOwner : owner)
  : GeneratedEncodingPlan implementation representation owner :=
  {| plannedEncoderImplementation := implementationId;
     plannedEncodingRepresentation := representationId;
     plannedEncodingOutputOwner := outputOwner |}.

Inductive EncodingCanonicalityDecision : Type :=
| EncodingCanonicalityAccepted
| NonCanonicalEncodingRejectedDecision.

Definition decideEncodingCanonicality
  (requirement : EncodingCanonicality)
  (encodingForm : EncodingForm) : EncodingCanonicalityDecision :=
  match requirement, encodingForm with
  | CanonicalEncodingRequired, NonCanonicalLegalGrammarMember =>
      NonCanonicalEncodingRejectedDecision
  | _, _ => EncodingCanonicalityAccepted
  end.

Inductive BoundarySerializationDecision : Type :=
| BoundarySerializationDecisionAccepted
| RawMemoryLayoutRejectedDecision
| MatchingCStructShapeRejectedDecision
| SerializationRepresentationMismatchDecision
| SerializationSubjectMismatchDecision.

Definition decideBoundarySerializationByFacts
  (basis : SerializationBasis)
  (representationMatches subjectMatches : bool)
  : BoundarySerializationDecision :=
  match basis with
  | RawMemoryLayout => RawMemoryLayoutRejectedDecision
  | MatchingCStructShape => MatchingCStructShapeRejectedDecision
  | CheckedWireCorrespondence =>
      if representationMatches then
        if subjectMatches then
          BoundarySerializationDecisionAccepted
        else SerializationSubjectMismatchDecision
      else SerializationRepresentationMismatchDecision
  end.

Theorem qualified_encoding_all_reflected_facts_accept :
  decideQualifiedEncodingByFacts true true true =
    QualifiedEncodingDecisionAccepted.
Proof. reflexivity. Qed.

Theorem qualified_encoding_acceptance_requires_all_reflected_facts :
  forall encoderAdmitted representationMatches outputOwnerMatches,
    decideQualifiedEncodingByFacts
      encoderAdmitted representationMatches outputOwnerMatches =
      QualifiedEncodingDecisionAccepted ->
    encoderAdmitted = true /\
    representationMatches = true /\
    outputOwnerMatches = true.
Proof.
  intros encoderAdmitted representationMatches outputOwnerMatches Haccepted.
  destruct encoderAdmitted; simpl in Haccepted; try discriminate.
  destruct representationMatches; simpl in Haccepted; try discriminate.
  destruct outputOwnerMatches; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem qualified_encoder_not_admitted_has_precedence :
  forall representationMatches outputOwnerMatches,
    decideQualifiedEncodingByFacts
      false representationMatches outputOwnerMatches =
      QualifiedEncoderNotAdmittedDecision.
Proof. reflexivity. Qed.

Theorem qualified_encoding_representation_mismatch_has_precedence :
  forall outputOwnerMatches,
    decideQualifiedEncodingByFacts true false outputOwnerMatches =
      QualifiedEncodingRepresentationMismatchDecision.
Proof. reflexivity. Qed.

Theorem qualified_encoding_owner_mismatch_is_last :
  decideQualifiedEncodingByFacts true true false =
    QualifiedEncodingOutputOwnerMismatchDecision.
Proof. reflexivity. Qed.

Theorem qualified_encoding_decision_sound_complete :
  forall encoder requestedRepresentation expectedOwner actualOwner
         encoderAdmitted representationMatches outputOwnerMatches,
    (encoderAdmitted = true <->
      encoderAdmission encoder = EncodingAdmitted) ->
    (representationMatches = true <->
      encoderRepresentation encoder = requestedRepresentation) ->
    (outputOwnerMatches = true <-> expectedOwner = actualOwner) ->
    (decideQualifiedEncodingByFacts
      encoderAdmitted representationMatches outputOwnerMatches =
      QualifiedEncodingDecisionAccepted <->
     encoderAdmission encoder = EncodingAdmitted /\
     encoderRepresentation encoder = requestedRepresentation /\
     expectedOwner = actualOwner).
Proof.
  intros encoder requestedRepresentation expectedOwner actualOwner
    encoderAdmitted representationMatches outputOwnerMatches
    Hadmitted Hrepresentation Howner.
  split.
  - intro Haccepted.
    apply qualified_encoding_acceptance_requires_all_reflected_facts in Haccepted.
    destruct Haccepted as [HadmittedFact [HrepresentationFact HownerFact]].
    repeat split.
    + apply (proj1 Hadmitted). exact HadmittedFact.
    + apply (proj1 Hrepresentation). exact HrepresentationFact.
    + apply (proj1 Howner). exact HownerFact.
  - intros [HadmittedEq [HrepresentationEq HownerEq]].
    assert (HadmittedFact : encoderAdmitted = true).
    { apply (proj2 Hadmitted). exact HadmittedEq. }
    assert (HrepresentationFact : representationMatches = true).
    { apply (proj2 Hrepresentation). exact HrepresentationEq. }
    assert (HownerFact : outputOwnerMatches = true).
    { apply (proj2 Howner). exact HownerEq. }
    rewrite HadmittedFact, HrepresentationFact, HownerFact.
    reflexivity.
Qed.

Theorem generated_encoding_plan_is_exact :
  forall implementation representation owner
         (implementationId : implementation)
         (representationId : representation)
         (outputOwner : owner),
    plannedEncoderImplementation
      (planGeneratedEncoding implementationId representationId outputOwner) =
      implementationId /\
    plannedEncodingRepresentation
      (planGeneratedEncoding implementationId representationId outputOwner) =
      representationId /\
    plannedEncodingOutputOwner
      (planGeneratedEncoding implementationId representationId outputOwner) =
      outputOwner.
Proof.
  intros.
  repeat split; reflexivity.
Qed.

Theorem canonicality_decision_matches_certified_cases :
  decideEncodingCanonicality
      CanonicalityNotRequired NonCanonicalLegalGrammarMember =
      EncodingCanonicalityAccepted /\
  decideEncodingCanonicality
      CanonicalEncodingRequired CanonicalGrammarMember =
      EncodingCanonicalityAccepted /\
  decideEncodingCanonicality
      CanonicalEncodingRequired NonCanonicalLegalGrammarMember =
      NonCanonicalEncodingRejectedDecision.
Proof.
  repeat split; reflexivity.
Qed.

Theorem raw_memory_serialization_rejects_before_identity_facts :
  forall representationMatches subjectMatches,
    decideBoundarySerializationByFacts
      RawMemoryLayout representationMatches subjectMatches =
      RawMemoryLayoutRejectedDecision.
Proof. reflexivity. Qed.

Theorem matching_struct_serialization_rejects_before_identity_facts :
  forall representationMatches subjectMatches,
    decideBoundarySerializationByFacts
      MatchingCStructShape representationMatches subjectMatches =
      MatchingCStructShapeRejectedDecision.
Proof. reflexivity. Qed.

Theorem checked_wire_representation_mismatch_has_precedence :
  forall subjectMatches,
    decideBoundarySerializationByFacts
      CheckedWireCorrespondence false subjectMatches =
      SerializationRepresentationMismatchDecision.
Proof. reflexivity. Qed.

Theorem checked_wire_subject_mismatch_is_last :
  decideBoundarySerializationByFacts
    CheckedWireCorrespondence true false =
    SerializationSubjectMismatchDecision.
Proof. reflexivity. Qed.

Theorem exact_checked_wire_facts_accept :
  decideBoundarySerializationByFacts
    CheckedWireCorrespondence true true =
    BoundarySerializationDecisionAccepted.
Proof. reflexivity. Qed.

Theorem serialization_acceptance_requires_exact_checked_wire_facts :
  forall basis representationMatches subjectMatches,
    decideBoundarySerializationByFacts
      basis representationMatches subjectMatches =
      BoundarySerializationDecisionAccepted ->
    basis = CheckedWireCorrespondence /\
    representationMatches = true /\
    subjectMatches = true.
Proof.
  intros basis representationMatches subjectMatches Haccepted.
  destruct basis; simpl in Haccepted; try discriminate.
  destruct representationMatches; simpl in Haccepted; try discriminate.
  destruct subjectMatches; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem serialization_decision_sound_complete :
  forall expectedRepresentation expectedSubject correspondence
         representationMatches subjectMatches,
    (representationMatches = true <->
      serializationRepresentation correspondence = expectedRepresentation) ->
    (subjectMatches = true <->
      serializationSubject correspondence = expectedSubject) ->
    (decideBoundarySerializationByFacts
      (serializationBasis correspondence)
      representationMatches subjectMatches =
      BoundarySerializationDecisionAccepted <->
     serializationBasis correspondence = CheckedWireCorrespondence /\
     serializationRepresentation correspondence = expectedRepresentation /\
     serializationSubject correspondence = expectedSubject).
Proof.
  intros expectedRepresentation expectedSubject
    [actualRepresentation actualSubject basis]
    representationMatches subjectMatches Hrepresentation Hsubject.
  simpl in *.
  split.
  - intro Haccepted.
    apply serialization_acceptance_requires_exact_checked_wire_facts in Haccepted.
    destruct Haccepted as [Hbasis [HrepresentationFact HsubjectFact]].
    repeat split.
    + exact Hbasis.
    + apply (proj1 Hrepresentation). exact HrepresentationFact.
    + apply (proj1 Hsubject). exact HsubjectFact.
  - intros [Hbasis [HrepresentationEq HsubjectEq]].
    subst basis.
    assert (HrepresentationFact : representationMatches = true).
    { apply (proj2 Hrepresentation). exact HrepresentationEq. }
    assert (HsubjectFact : subjectMatches = true).
    { apply (proj2 Hsubject). exact HsubjectEq. }
    rewrite HrepresentationFact, HsubjectFact.
    reflexivity.
Qed.
