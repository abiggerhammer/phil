From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-BND-ENCODE-001 — qualified boundary encoding, explicit canonicality,
  and checked serialization correspondence.

  The proof models the bounded BND-008–010 checker surface.  Encoder admission
  is imported as an already-checked provider/qualification fact.  Successful
  generated evidence is tied to one exact encoder implementation,
  representation revision, and output subject.  Canonicality is a separate
  opt-in contract.  Serialization accepts only checked wire correspondence;
  raw memory layout or matching host-struct shape never suffices.

  Concrete bytes, wire I/O, Text/Name representation, provider correctness,
  and Haskell implementation correspondence remain explicit boundaries.
*)

Inductive EncodingAdmission : Type :=
| EncodingAdmitted
| EncodingNotAdmitted.

Record QualifiedEncoder : Type := mkQualifiedEncoder {
  encoderImplementation : nat;
  encoderRepresentation : nat;
  encoderAdmission : EncodingAdmission
}.

Record GeneratedEncodingEvidence : Type := mkGeneratedEncodingEvidence {
  generatedByImplementation : nat;
  generatedRepresentation : nat;
  generatedOutputOwner : nat
}.

Inductive QualifiedEncodingError : Type :=
| EncoderNotAdmitted : nat -> QualifiedEncodingError
| EncodingRepresentationMismatch : nat -> nat -> QualifiedEncodingError
| EncodingOutputOwnerMismatch : nat -> nat -> QualifiedEncodingError.

Inductive QualifiedEncodingResult : Type :=
| QualifiedEncodingFailure : QualifiedEncodingError -> QualifiedEncodingResult
| QualifiedEncodingSuccess : GeneratedEncodingEvidence -> QualifiedEncodingResult.

Definition establishGeneratedEncoding
  (encoder : QualifiedEncoder)
  (requestedRepresentation expectedOwner actualOwner : nat)
  : QualifiedEncodingResult :=
  match encoderAdmission encoder with
  | EncodingNotAdmitted =>
      QualifiedEncodingFailure (EncoderNotAdmitted (encoderImplementation encoder))
  | EncodingAdmitted =>
      if Nat.eqb (encoderRepresentation encoder) requestedRepresentation then
        if Nat.eqb expectedOwner actualOwner then
          QualifiedEncodingSuccess
            (mkGeneratedEncodingEvidence
              (encoderImplementation encoder)
              requestedRepresentation
              actualOwner)
        else QualifiedEncodingFailure
          (EncodingOutputOwnerMismatch expectedOwner actualOwner)
      else QualifiedEncodingFailure
        (EncodingRepresentationMismatch
          (encoderRepresentation encoder) requestedRepresentation)
  end.

Theorem successful_generated_encoding_is_exact :
  forall encoder requestedRepresentation expectedOwner actualOwner evidence,
    establishGeneratedEncoding
      encoder requestedRepresentation expectedOwner actualOwner =
      QualifiedEncodingSuccess evidence ->
    encoderAdmission encoder = EncodingAdmitted /\
    encoderRepresentation encoder = requestedRepresentation /\
    expectedOwner = actualOwner /\
    generatedByImplementation evidence = encoderImplementation encoder /\
    generatedRepresentation evidence = requestedRepresentation /\
    generatedOutputOwner evidence = actualOwner.
Proof.
  intros [implementation representation admission]
    requestedRepresentation expectedOwner actualOwner evidence Hresult.
  destruct admission.
  - simpl in Hresult.
    destruct (Nat.eqb representation requestedRepresentation) eqn:Hrepresentation.
    + simpl in Hresult.
      destruct (Nat.eqb expectedOwner actualOwner) eqn:Howner.
      * simpl in Hresult.
        injection Hresult as Hevidence.
        subst evidence.
        pose proof
          ((proj1 (Nat.eqb_eq representation requestedRepresentation)) Hrepresentation)
          as Erepresentation.
        pose proof
          ((proj1 (Nat.eqb_eq expectedOwner actualOwner)) Howner)
          as Eowner.
        repeat split; try assumption; reflexivity.
      * simpl in Hresult.
        discriminate.
    + simpl in Hresult.
      discriminate.
  - simpl in Hresult.
    discriminate.
Qed.

Theorem unadmitted_encoder_rejects_exactly :
  forall implementation representation requestedRepresentation expectedOwner actualOwner,
    establishGeneratedEncoding
      (mkQualifiedEncoder implementation representation EncodingNotAdmitted)
      requestedRepresentation expectedOwner actualOwner =
    QualifiedEncodingFailure (EncoderNotAdmitted implementation).
Proof.
  reflexivity.
Qed.

Theorem encoding_representation_mismatch_rejects_exactly :
  forall implementation representation requestedRepresentation expectedOwner actualOwner,
    representation <> requestedRepresentation ->
    establishGeneratedEncoding
      (mkQualifiedEncoder implementation representation EncodingAdmitted)
      requestedRepresentation expectedOwner actualOwner =
    QualifiedEncodingFailure
      (EncodingRepresentationMismatch representation requestedRepresentation).
Proof.
  intros implementation representation requestedRepresentation expectedOwner actualOwner Hneq.
  simpl.
  assert (Hrepresentation : Nat.eqb representation requestedRepresentation = false).
  { exact ((proj2 (Nat.eqb_neq representation requestedRepresentation)) Hneq). }
  rewrite Hrepresentation.
  reflexivity.
Qed.

Theorem encoding_output_owner_mismatch_rejects_exactly :
  forall implementation representation expectedOwner actualOwner,
    expectedOwner <> actualOwner ->
    establishGeneratedEncoding
      (mkQualifiedEncoder implementation representation EncodingAdmitted)
      representation expectedOwner actualOwner =
    QualifiedEncodingFailure
      (EncodingOutputOwnerMismatch expectedOwner actualOwner).
Proof.
  intros implementation representation expectedOwner actualOwner Hneq.
  simpl.
  rewrite Nat.eqb_refl.
  assert (Howner : Nat.eqb expectedOwner actualOwner = false).
  { exact ((proj2 (Nat.eqb_neq expectedOwner actualOwner)) Hneq). }
  rewrite Howner.
  reflexivity.
Qed.

Inductive EncodingCanonicality : Type :=
| CanonicalityNotRequired
| CanonicalEncodingRequired.

Inductive EncodingForm : Type :=
| CanonicalGrammarMember
| NonCanonicalLegalGrammarMember.

Inductive CanonicalityError : Type :=
| NonCanonicalEncodingRejected : nat -> nat -> CanonicalityError.

Inductive CanonicalityResult : Type :=
| CanonicalityFailure : CanonicalityError -> CanonicalityResult
| CanonicalitySuccess : GeneratedEncodingEvidence -> CanonicalityResult.

Definition checkEncodingCanonicality
  (requirement : EncodingCanonicality)
  (encodingForm : EncodingForm)
  (evidence : GeneratedEncodingEvidence) : CanonicalityResult :=
  match requirement, encodingForm with
  | CanonicalEncodingRequired, NonCanonicalLegalGrammarMember =>
      CanonicalityFailure
        (NonCanonicalEncodingRejected
          (generatedRepresentation evidence)
          (generatedOutputOwner evidence))
  | _, _ => CanonicalitySuccess evidence
  end.

Theorem valid_encoding_does_not_imply_canonicality :
  forall evidence,
    checkEncodingCanonicality
      CanonicalityNotRequired NonCanonicalLegalGrammarMember evidence =
    CanonicalitySuccess evidence.
Proof.
  reflexivity.
Qed.

Theorem declared_canonicality_rejects_noncanonical_member_exactly :
  forall implementation representation outputOwner,
    checkEncodingCanonicality
      CanonicalEncodingRequired
      NonCanonicalLegalGrammarMember
      (mkGeneratedEncodingEvidence implementation representation outputOwner) =
    CanonicalityFailure
      (NonCanonicalEncodingRejected representation outputOwner).
Proof.
  reflexivity.
Qed.

Theorem declared_canonicality_accepts_canonical_member_unchanged :
  forall evidence,
    checkEncodingCanonicality
      CanonicalEncodingRequired CanonicalGrammarMember evidence =
    CanonicalitySuccess evidence.
Proof.
  reflexivity.
Qed.

Inductive SerializationBasis : Type :=
| CheckedWireCorrespondence
| RawMemoryLayout
| MatchingCStructShape.

Record SerializationCorrespondence : Type := mkSerializationCorrespondence {
  serializationRepresentation : nat;
  serializationSubject : nat;
  serializationBasis : SerializationBasis
}.

Inductive BoundarySerializationError : Type :=
| UncheckedSerializationBasis : SerializationBasis -> BoundarySerializationError
| SerializationRepresentationMismatch : nat -> nat -> BoundarySerializationError
| SerializationSubjectMismatch : nat -> nat -> BoundarySerializationError.

Inductive BoundarySerializationResult : Type :=
| BoundarySerializationFailure : BoundarySerializationError -> BoundarySerializationResult
| BoundarySerializationSuccess : BoundarySerializationResult.

Definition checkBoundarySerialization
  (expectedRepresentation expectedSubject : nat)
  (correspondence : SerializationCorrespondence)
  : BoundarySerializationResult :=
  match serializationBasis correspondence with
  | RawMemoryLayout =>
      BoundarySerializationFailure (UncheckedSerializationBasis RawMemoryLayout)
  | MatchingCStructShape =>
      BoundarySerializationFailure (UncheckedSerializationBasis MatchingCStructShape)
  | CheckedWireCorrespondence =>
      if Nat.eqb (serializationRepresentation correspondence) expectedRepresentation then
        if Nat.eqb (serializationSubject correspondence) expectedSubject then
          BoundarySerializationSuccess
        else BoundarySerializationFailure
          (SerializationSubjectMismatch
            expectedSubject (serializationSubject correspondence))
      else BoundarySerializationFailure
        (SerializationRepresentationMismatch
          expectedRepresentation (serializationRepresentation correspondence))
  end.

Theorem raw_memory_layout_never_establishes_wire_correspondence :
  forall expectedRepresentation expectedSubject actualRepresentation actualSubject,
    checkBoundarySerialization
      expectedRepresentation expectedSubject
      (mkSerializationCorrespondence
        actualRepresentation actualSubject RawMemoryLayout) =
    BoundarySerializationFailure (UncheckedSerializationBasis RawMemoryLayout).
Proof.
  reflexivity.
Qed.

Theorem matching_struct_shape_never_establishes_wire_correspondence :
  forall expectedRepresentation expectedSubject actualRepresentation actualSubject,
    checkBoundarySerialization
      expectedRepresentation expectedSubject
      (mkSerializationCorrespondence
        actualRepresentation actualSubject MatchingCStructShape) =
    BoundarySerializationFailure (UncheckedSerializationBasis MatchingCStructShape).
Proof.
  reflexivity.
Qed.

Theorem checked_wire_representation_mismatch_rejects_exactly :
  forall expectedRepresentation expectedSubject actualRepresentation actualSubject,
    actualRepresentation <> expectedRepresentation ->
    checkBoundarySerialization
      expectedRepresentation expectedSubject
      (mkSerializationCorrespondence
        actualRepresentation actualSubject CheckedWireCorrespondence) =
    BoundarySerializationFailure
      (SerializationRepresentationMismatch expectedRepresentation actualRepresentation).
Proof.
  intros expectedRepresentation expectedSubject actualRepresentation actualSubject Hneq.
  simpl.
  assert (Hrepresentation : Nat.eqb actualRepresentation expectedRepresentation = false).
  { exact ((proj2 (Nat.eqb_neq actualRepresentation expectedRepresentation)) Hneq). }
  rewrite Hrepresentation.
  reflexivity.
Qed.

Theorem checked_wire_subject_mismatch_rejects_exactly :
  forall expectedRepresentation expectedSubject actualSubject,
    actualSubject <> expectedSubject ->
    checkBoundarySerialization
      expectedRepresentation expectedSubject
      (mkSerializationCorrespondence
        expectedRepresentation actualSubject CheckedWireCorrespondence) =
    BoundarySerializationFailure
      (SerializationSubjectMismatch expectedSubject actualSubject).
Proof.
  intros expectedRepresentation expectedSubject actualSubject Hneq.
  simpl.
  rewrite Nat.eqb_refl.
  assert (Hsubject : Nat.eqb actualSubject expectedSubject = false).
  { exact ((proj2 (Nat.eqb_neq actualSubject expectedSubject)) Hneq). }
  rewrite Hsubject.
  reflexivity.
Qed.

Theorem exact_checked_wire_correspondence_accepts :
  forall representation subject,
    checkBoundarySerialization
      representation subject
      (mkSerializationCorrespondence
        representation subject CheckedWireCorrespondence) =
    BoundarySerializationSuccess.
Proof.
  intros representation subject.
  simpl.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

Theorem successful_checked_wire_correspondence_is_exact :
  forall expectedRepresentation expectedSubject correspondence,
    checkBoundarySerialization
      expectedRepresentation expectedSubject correspondence =
      BoundarySerializationSuccess ->
    serializationBasis correspondence = CheckedWireCorrespondence /\
    serializationRepresentation correspondence = expectedRepresentation /\
    serializationSubject correspondence = expectedSubject.
Proof.
  intros expectedRepresentation expectedSubject
    [actualRepresentation actualSubject basis] Hresult.
  destruct basis.
  - simpl in Hresult.
    destruct (Nat.eqb actualRepresentation expectedRepresentation) eqn:Hrepresentation;
      try discriminate.
    destruct (Nat.eqb actualSubject expectedSubject) eqn:Hsubject;
      try discriminate.
    pose proof
      ((proj1 (Nat.eqb_eq actualRepresentation expectedRepresentation)) Hrepresentation)
      as Erepresentation.
    pose proof
      ((proj1 (Nat.eqb_eq actualSubject expectedSubject)) Hsubject)
      as Esubject.
    repeat split; try assumption; reflexivity.
  - simpl in Hresult. discriminate.
  - simpl in Hresult. discriminate.
Qed.
