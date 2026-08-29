From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-BND-REP-001 — exact boundary representation correspondence and direction.

  This proof models the bounded BND-004–007 checker surface.  A successful
  correspondence is admitted only after exact representation, grammar,
  semantic-type, recognized-grammar, and recognized-source-value agreement.
  Mapping disposition remains a separate competence boundary, transformed
  semantic values do not retarget the recognized source identity, and receive /
  send direction is enforced independently.

  Concrete Text/Name/GrammarId representation and Haskell implementation
  correspondence remain explicit boundaries.
*)

Record BoundaryRepresentation : Type := mkBoundaryRepresentation {
  representationId : nat;
  representationGrammar : nat;
  representationValueType : nat
}.

Record ParsedWitness : Type := mkParsedWitness {
  parsedGrammarId : nat;
  parsedValueName : nat
}.

Record BoundaryMappingRequest : Type := mkBoundaryMappingRequest {
  requestedRepresentation : nat;
  requestedGrammar : nat;
  requestedValueType : nat;
  requestedGrammarValue : nat;
  requestedSemanticValue : nat
}.

Record CorrespondenceEvidence : Type := mkCorrespondenceEvidence {
  correspondenceRepresentation : nat;
  correspondenceGrammar : nat;
  correspondenceValueType : nat;
  correspondenceGrammarValue : nat;
  correspondenceSemanticValue : nat
}.

Inductive BoundaryMappingDisposition : Type :=
| MappingAccepted
| MappingRejected : nat -> BoundaryMappingDisposition.

Inductive BoundaryMappingError : Type :=
| BoundaryRepresentationMismatch : nat -> nat -> BoundaryMappingError
| BoundaryGrammarMismatch : nat -> nat -> BoundaryMappingError
| BoundaryValueTypeMismatch : nat -> nat -> BoundaryMappingError
| RecognizedGrammarMismatch : nat -> nat -> BoundaryMappingError
| RecognizedValueMismatch : nat -> nat -> BoundaryMappingError
| BoundaryMappingFailure : nat -> nat -> nat -> BoundaryMappingError.

Inductive BoundaryMappingResult : Type :=
| MappingError : BoundaryMappingError -> BoundaryMappingResult
| MappingEvidence : CorrespondenceEvidence -> BoundaryMappingResult.

Definition mapRecognizedBoundaryWithDisposition
  (representation : BoundaryRepresentation)
  (parsed : ParsedWitness)
  (request : BoundaryMappingRequest)
  (disposition : BoundaryMappingDisposition) : BoundaryMappingResult :=
  if Nat.eqb (requestedRepresentation request) (representationId representation) then
    if Nat.eqb (requestedGrammar request) (representationGrammar representation) then
      if Nat.eqb (requestedValueType request) (representationValueType representation) then
        if Nat.eqb (parsedGrammarId parsed) (representationGrammar representation) then
          if Nat.eqb (parsedValueName parsed) (requestedGrammarValue request) then
            match disposition with
            | MappingRejected detail =>
                MappingError
                  (BoundaryMappingFailure
                    (representationId representation)
                    (requestedGrammarValue request)
                    detail)
            | MappingAccepted =>
                MappingEvidence
                  (mkCorrespondenceEvidence
                    (representationId representation)
                    (representationGrammar representation)
                    (representationValueType representation)
                    (requestedGrammarValue request)
                    (requestedSemanticValue request))
            end
          else MappingError
            (RecognizedValueMismatch
              (parsedValueName parsed) (requestedGrammarValue request))
        else MappingError
          (RecognizedGrammarMismatch
            (representationGrammar representation) (parsedGrammarId parsed))
      else MappingError
        (BoundaryValueTypeMismatch
          (representationValueType representation) (requestedValueType request))
    else MappingError
      (BoundaryGrammarMismatch
        (representationGrammar representation) (requestedGrammar request))
  else MappingError
    (BoundaryRepresentationMismatch
      (representationId representation) (requestedRepresentation request)).

Definition mapRecognizedBoundary
  (representation : BoundaryRepresentation)
  (parsed : ParsedWitness)
  (request : BoundaryMappingRequest) : BoundaryMappingResult :=
  mapRecognizedBoundaryWithDisposition representation parsed request MappingAccepted.

(* Successful BND-004/006 correspondence is tied to every exact checked identity. *)
Theorem successful_mapping_has_exact_checks_and_evidence :
  forall representation parsed request evidence,
    mapRecognizedBoundary representation parsed request = MappingEvidence evidence ->
    requestedRepresentation request = representationId representation /\
    requestedGrammar request = representationGrammar representation /\
    requestedValueType request = representationValueType representation /\
    parsedGrammarId parsed = representationGrammar representation /\
    parsedValueName parsed = requestedGrammarValue request /\
    correspondenceRepresentation evidence = representationId representation /\
    correspondenceGrammar evidence = representationGrammar representation /\
    correspondenceValueType evidence = representationValueType representation /\
    correspondenceGrammarValue evidence = requestedGrammarValue request /\
    correspondenceSemanticValue evidence = requestedSemanticValue request.
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    evidence Hmap.
  unfold mapRecognizedBoundary, mapRecognizedBoundaryWithDisposition in Hmap.
  simpl in Hmap.
  destruct (Nat.eqb requestRep repId) eqn:Hrep; try discriminate.
  destruct (Nat.eqb requestGrammar repGrammar) eqn:Hgrammar; try discriminate.
  destruct (Nat.eqb requestType repType) eqn:Htype; try discriminate.
  destruct (Nat.eqb parsedGrammar repGrammar) eqn:HparsedGrammar; try discriminate.
  destruct (Nat.eqb parsedValue grammarValue) eqn:HparsedValue; try discriminate.
  inversion Hmap; subst evidence; clear Hmap.
  pose proof ((proj1 (Nat.eqb_eq requestRep repId)) Hrep) as Erep.
  pose proof ((proj1 (Nat.eqb_eq requestGrammar repGrammar)) Hgrammar) as Egrammar.
  pose proof ((proj1 (Nat.eqb_eq requestType repType)) Htype) as Etype.
  pose proof ((proj1 (Nat.eqb_eq parsedGrammar repGrammar)) HparsedGrammar) as EparsedGrammar.
  pose proof ((proj1 (Nat.eqb_eq parsedValue grammarValue)) HparsedValue) as EparsedValue.
  repeat split; try assumption; reflexivity.
Qed.

(* Each exact mismatch fails closed at its corresponding ordered gate. *)
Theorem representation_mismatch_rejects_exactly :
  forall representation parsed request disposition,
    requestedRepresentation request <> representationId representation ->
    mapRecognizedBoundaryWithDisposition representation parsed request disposition =
      MappingError
        (BoundaryRepresentationMismatch
          (representationId representation) (requestedRepresentation request)).
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    disposition Hneq.
  unfold mapRecognizedBoundaryWithDisposition.
  simpl in *.
  assert (Hrep : Nat.eqb requestRep repId = false).
  { exact ((proj2 (Nat.eqb_neq requestRep repId)) Hneq). }
  rewrite Hrep.
  reflexivity.
Qed.

Theorem grammar_mismatch_rejects_exactly :
  forall representation parsed request disposition,
    requestedRepresentation request = representationId representation ->
    requestedGrammar request <> representationGrammar representation ->
    mapRecognizedBoundaryWithDisposition representation parsed request disposition =
      MappingError
        (BoundaryGrammarMismatch
          (representationGrammar representation) (requestedGrammar request)).
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    disposition HrepEq Hneq.
  unfold mapRecognizedBoundaryWithDisposition.
  simpl in *.
  assert (Hrep : Nat.eqb requestRep repId = true).
  { exact ((proj2 (Nat.eqb_eq requestRep repId)) HrepEq). }
  assert (Hgrammar : Nat.eqb requestGrammar repGrammar = false).
  { exact ((proj2 (Nat.eqb_neq requestGrammar repGrammar)) Hneq). }
  rewrite Hrep, Hgrammar.
  reflexivity.
Qed.

Theorem value_type_mismatch_rejects_exactly :
  forall representation parsed request disposition,
    requestedRepresentation request = representationId representation ->
    requestedGrammar request = representationGrammar representation ->
    requestedValueType request <> representationValueType representation ->
    mapRecognizedBoundaryWithDisposition representation parsed request disposition =
      MappingError
        (BoundaryValueTypeMismatch
          (representationValueType representation) (requestedValueType request)).
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    disposition HrepEq HgrammarEq Hneq.
  unfold mapRecognizedBoundaryWithDisposition.
  simpl in *.
  assert (Hrep : Nat.eqb requestRep repId = true).
  { exact ((proj2 (Nat.eqb_eq requestRep repId)) HrepEq). }
  assert (Hgrammar : Nat.eqb requestGrammar repGrammar = true).
  { exact ((proj2 (Nat.eqb_eq requestGrammar repGrammar)) HgrammarEq). }
  assert (Htype : Nat.eqb requestType repType = false).
  { exact ((proj2 (Nat.eqb_neq requestType repType)) Hneq). }
  rewrite Hrep, Hgrammar, Htype.
  reflexivity.
Qed.

Theorem recognized_grammar_mismatch_rejects_exactly :
  forall representation parsed request disposition,
    requestedRepresentation request = representationId representation ->
    requestedGrammar request = representationGrammar representation ->
    requestedValueType request = representationValueType representation ->
    parsedGrammarId parsed <> representationGrammar representation ->
    mapRecognizedBoundaryWithDisposition representation parsed request disposition =
      MappingError
        (RecognizedGrammarMismatch
          (representationGrammar representation) (parsedGrammarId parsed)).
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    disposition HrepEq HgrammarEq HtypeEq Hneq.
  unfold mapRecognizedBoundaryWithDisposition.
  simpl in *.
  assert (Hrep : Nat.eqb requestRep repId = true).
  { exact ((proj2 (Nat.eqb_eq requestRep repId)) HrepEq). }
  assert (Hgrammar : Nat.eqb requestGrammar repGrammar = true).
  { exact ((proj2 (Nat.eqb_eq requestGrammar repGrammar)) HgrammarEq). }
  assert (Htype : Nat.eqb requestType repType = true).
  { exact ((proj2 (Nat.eqb_eq requestType repType)) HtypeEq). }
  assert (Hparsed : Nat.eqb parsedGrammar repGrammar = false).
  { exact ((proj2 (Nat.eqb_neq parsedGrammar repGrammar)) Hneq). }
  rewrite Hrep, Hgrammar, Htype, Hparsed.
  reflexivity.
Qed.

Theorem recognized_value_mismatch_rejects_exactly :
  forall representation parsed request disposition,
    requestedRepresentation request = representationId representation ->
    requestedGrammar request = representationGrammar representation ->
    requestedValueType request = representationValueType representation ->
    parsedGrammarId parsed = representationGrammar representation ->
    parsedValueName parsed <> requestedGrammarValue request ->
    mapRecognizedBoundaryWithDisposition representation parsed request disposition =
      MappingError
        (RecognizedValueMismatch
          (parsedValueName parsed) (requestedGrammarValue request)).
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    disposition HrepEq HgrammarEq HtypeEq HparsedGrammarEq Hneq.
  unfold mapRecognizedBoundaryWithDisposition.
  simpl in *.
  assert (Hrep : Nat.eqb requestRep repId = true).
  { exact ((proj2 (Nat.eqb_eq requestRep repId)) HrepEq). }
  assert (Hgrammar : Nat.eqb requestGrammar repGrammar = true).
  { exact ((proj2 (Nat.eqb_eq requestGrammar repGrammar)) HgrammarEq). }
  assert (Htype : Nat.eqb requestType repType = true).
  { exact ((proj2 (Nat.eqb_eq requestType repType)) HtypeEq). }
  assert (HparsedGrammar : Nat.eqb parsedGrammar repGrammar = true).
  { exact ((proj2 (Nat.eqb_eq parsedGrammar repGrammar)) HparsedGrammarEq). }
  assert (HparsedValue : Nat.eqb parsedValue grammarValue = false).
  { exact ((proj2 (Nat.eqb_neq parsedValue grammarValue)) Hneq). }
  rewrite Hrep, Hgrammar, Htype, HparsedGrammar, HparsedValue.
  reflexivity.
Qed.

(* BND-005: mapping competence may reject only after successful recognition/matching. *)
Theorem explicit_mapping_rejection_is_distinct_and_exact :
  forall representation parsed request detail,
    requestedRepresentation request = representationId representation ->
    requestedGrammar request = representationGrammar representation ->
    requestedValueType request = representationValueType representation ->
    parsedGrammarId parsed = representationGrammar representation ->
    parsedValueName parsed = requestedGrammarValue request ->
    mapRecognizedBoundaryWithDisposition
      representation parsed request (MappingRejected detail) =
      MappingError
        (BoundaryMappingFailure
          (representationId representation)
          (requestedGrammarValue request)
          detail).
Proof.
  intros [repId repGrammar repType]
    [parsedGrammar parsedValue]
    [requestRep requestGrammar requestType grammarValue semanticValue]
    detail HrepEq HgrammarEq HtypeEq HparsedGrammarEq HparsedValueEq.
  unfold mapRecognizedBoundaryWithDisposition.
  simpl in *.
  rewrite
    ((proj2 (Nat.eqb_eq requestRep repId)) HrepEq),
    ((proj2 (Nat.eqb_eq requestGrammar repGrammar)) HgrammarEq),
    ((proj2 (Nat.eqb_eq requestType repType)) HtypeEq),
    ((proj2 (Nat.eqb_eq parsedGrammar repGrammar)) HparsedGrammarEq),
    ((proj2 (Nat.eqb_eq parsedValue grammarValue)) HparsedValueEq).
  reflexivity.
Qed.

(* BND-006: transformed target identity is explicit and cannot retarget the source. *)
Theorem successful_mapping_preserves_recognized_source_identity :
  forall representation parsed request evidence,
    mapRecognizedBoundary representation parsed request = MappingEvidence evidence ->
    correspondenceGrammarValue evidence = parsedValueName parsed.
Proof.
  intros representation parsed request evidence Hmap.
  pose proof
    (successful_mapping_has_exact_checks_and_evidence
      representation parsed request evidence Hmap) as H.
  destruct H as
    [Hrep [Hgrammar [Htype [HparsedGrammar [HparsedValue
      [HevidenceRep [HevidenceGrammar [HevidenceType [Hsource Htarget]]]]]]]]].
  rewrite Hsource, HparsedValue.
  reflexivity.
Qed.

Theorem transforming_mapping_keeps_source_and_target_distinct :
  forall representation parsed request evidence,
    mapRecognizedBoundary representation parsed request = MappingEvidence evidence ->
    requestedGrammarValue request <> requestedSemanticValue request ->
    correspondenceGrammarValue evidence <> correspondenceSemanticValue evidence.
Proof.
  intros representation parsed request evidence Hmap Hdistinct Hsame.
  pose proof
    (successful_mapping_has_exact_checks_and_evidence
      representation parsed request evidence Hmap) as H.
  destruct H as
    [Hrep [Hgrammar [Htype [HparsedGrammar [HparsedValue
      [HevidenceRep [HevidenceGrammar [HevidenceType [Hsource Htarget]]]]]]]]].
  rewrite Hsource, Htarget in Hsame.
  exact (Hdistinct Hsame).
Qed.

Inductive BoundaryDirection : Type :=
| ReceiveOnly
| SendOnly
| Bidirectional.

Inductive BoundaryUse : Type :=
| InboundUse
| OutboundUse.

Inductive BoundaryDirectionError : Type :=
| ReceiveOnlyCannotEncode
| SendOnlyCannotAcceptInbound.

Inductive BoundaryDirectionResult : Type :=
| BoundaryUseAccepted
| BoundaryUseRejected : BoundaryDirectionError -> BoundaryDirectionResult.

Definition checkBoundaryUse
  (direction : BoundaryDirection) (use : BoundaryUse) : BoundaryDirectionResult :=
  match direction, use with
  | ReceiveOnly, OutboundUse => BoundaryUseRejected ReceiveOnlyCannotEncode
  | SendOnly, InboundUse => BoundaryUseRejected SendOnlyCannotAcceptInbound
  | _, _ => BoundaryUseAccepted
  end.

Theorem boundary_direction_gate_is_exact :
  checkBoundaryUse ReceiveOnly OutboundUse =
      BoundaryUseRejected ReceiveOnlyCannotEncode /\
  checkBoundaryUse SendOnly InboundUse =
      BoundaryUseRejected SendOnlyCannotAcceptInbound /\
  checkBoundaryUse ReceiveOnly InboundUse = BoundaryUseAccepted /\
  checkBoundaryUse SendOnly OutboundUse = BoundaryUseAccepted /\
  checkBoundaryUse Bidirectional InboundUse = BoundaryUseAccepted /\
  checkBoundaryUse Bidirectional OutboundUse = BoundaryUseAccepted.
Proof.
  repeat split; reflexivity.
Qed.
