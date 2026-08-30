From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-BND-PROGRESS-001 — typed boundary receive/send progression gating.

  This proof starts from evidence objects whose establishment is certified by
  predecessor obligations: ParsedWitness and correspondence evidence on the
  receive side, generated encoding evidence on the send side.  It proves that
  progression is gated by exact identity agreement and, for sends, by a
  complete-emission evidence step.  Concrete transport completion arithmetic,
  provider behavior, and Haskell implementation correspondence remain explicit
  boundaries.
*)

Record ParsedWitness : Type := mkParsedWitness {
  parsedGrammar : nat;
  parsedValue : nat
}.

Record CorrespondenceEvidence : Type := mkCorrespondenceEvidence {
  correspondenceGrammar : nat;
  correspondenceGrammarValue : nat
}.

Inductive UnderlyingProgression : Type :=
| UnderlyingReject
| UnderlyingAdvance.

Inductive ReceiveProgressionError : Type :=
| ReceiveMappingGrammarMismatch
| ReceiveMappingValueMismatch
| UnderlyingReceiveRejected.

Inductive ReceiveProgressionResult : Type :=
| ReceiveProgressionFailure : ReceiveProgressionError -> ReceiveProgressionResult
| ReceiveProgressionAdvance : ReceiveProgressionResult.

Definition commitMappedReceive
  (parsed : ParsedWitness)
  (correspondence : CorrespondenceEvidence)
  (underlying : UnderlyingProgression)
  : ReceiveProgressionResult :=
  if Nat.eqb (parsedGrammar parsed) (correspondenceGrammar correspondence) then
    if Nat.eqb (parsedValue parsed) (correspondenceGrammarValue correspondence) then
      match underlying with
      | UnderlyingReject => ReceiveProgressionFailure UnderlyingReceiveRejected
      | UnderlyingAdvance => ReceiveProgressionAdvance
      end
    else ReceiveProgressionFailure ReceiveMappingValueMismatch
  else ReceiveProgressionFailure ReceiveMappingGrammarMismatch.

Theorem successful_mapped_receive_is_exact :
  forall parsedGrammarId parsedValueId correspondenceGrammarId correspondenceValueId underlying,
    commitMappedReceive
      (mkParsedWitness parsedGrammarId parsedValueId)
      (mkCorrespondenceEvidence correspondenceGrammarId correspondenceValueId)
      underlying = ReceiveProgressionAdvance ->
    parsedGrammarId = correspondenceGrammarId /\
    parsedValueId = correspondenceValueId /\
    underlying = UnderlyingAdvance.
Proof.
  intros parsedGrammarId parsedValueId correspondenceGrammarId correspondenceValueId underlying Hresult.
  unfold commitMappedReceive in Hresult.
  simpl in Hresult.
  destruct (Nat.eqb parsedGrammarId correspondenceGrammarId) eqn:Hgrammar.
  - destruct (Nat.eqb parsedValueId correspondenceValueId) eqn:Hvalue.
    + destruct underlying.
      * discriminate Hresult.
      * split.
        -- exact ((proj1 (Nat.eqb_eq parsedGrammarId correspondenceGrammarId)) Hgrammar).
        -- split.
           ++ exact ((proj1 (Nat.eqb_eq parsedValueId correspondenceValueId)) Hvalue).
           ++ reflexivity.
    + discriminate Hresult.
  - discriminate Hresult.
Qed.

Theorem receive_grammar_mismatch_never_advances :
  forall parsedGrammarId parsedValueId correspondenceGrammarId correspondenceValueId underlying,
    parsedGrammarId <> correspondenceGrammarId ->
    commitMappedReceive
      (mkParsedWitness parsedGrammarId parsedValueId)
      (mkCorrespondenceEvidence correspondenceGrammarId correspondenceValueId)
      underlying = ReceiveProgressionFailure ReceiveMappingGrammarMismatch.
Proof.
  intros parsedGrammarId parsedValueId correspondenceGrammarId correspondenceValueId underlying Hneq.
  unfold commitMappedReceive.
  simpl.
  destruct (Nat.eqb parsedGrammarId correspondenceGrammarId) eqn:Hgrammar.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq parsedGrammarId correspondenceGrammarId)) Hgrammar).
  - reflexivity.
Qed.

Theorem receive_value_mismatch_never_advances :
  forall grammarId parsedValueId correspondenceValueId underlying,
    parsedValueId <> correspondenceValueId ->
    commitMappedReceive
      (mkParsedWitness grammarId parsedValueId)
      (mkCorrespondenceEvidence grammarId correspondenceValueId)
      underlying = ReceiveProgressionFailure ReceiveMappingValueMismatch.
Proof.
  intros grammarId parsedValueId correspondenceValueId underlying Hneq.
  unfold commitMappedReceive.
  simpl.
  destruct (Nat.eqb grammarId grammarId) eqn:Hgrammar.
  - destruct (Nat.eqb parsedValueId correspondenceValueId) eqn:Hvalue.
    + exfalso.
      apply Hneq.
      exact ((proj1 (Nat.eqb_eq parsedValueId correspondenceValueId)) Hvalue).
    + reflexivity.
  - exfalso.
    apply ((proj1 (Nat.eqb_neq grammarId grammarId)) Hgrammar).
    reflexivity.
Qed.

Record GeneratedEncodingEvidence : Type := mkGeneratedEncodingEvidence {
  generatedRepresentation : nat;
  generatedOutputOwner : nat
}.

Record CompleteEmissionEvidence : Type := mkCompleteEmissionEvidence {
  completeEmissionRepresentation : nat;
  completeEmissionOwner : nat
}.

Inductive EmissionDisposition : Type :=
| InvalidEmissionExtent
| PartialEmission
| CompleteEmission
| EmissionPastDeclaredFrame.

Inductive CompleteEmissionError : Type :=
| InvalidEmissionRejected
| PartialTransportEmissionRejected
| PastDeclaredFrameRejected.

Inductive CompleteEmissionResult : Type :=
| CompleteEmissionFailure : CompleteEmissionError -> CompleteEmissionResult
| CompleteEmissionSuccess : CompleteEmissionEvidence -> CompleteEmissionResult.

Definition establishCompleteEmission
  (generated : GeneratedEncodingEvidence)
  (disposition : EmissionDisposition)
  : CompleteEmissionResult :=
  match disposition with
  | InvalidEmissionExtent => CompleteEmissionFailure InvalidEmissionRejected
  | PartialEmission => CompleteEmissionFailure PartialTransportEmissionRejected
  | EmissionPastDeclaredFrame => CompleteEmissionFailure PastDeclaredFrameRejected
  | CompleteEmission => CompleteEmissionSuccess
      (mkCompleteEmissionEvidence
        (generatedRepresentation generated)
        (generatedOutputOwner generated))
  end.

Theorem partial_emission_never_establishes_completion :
  forall generated,
    establishCompleteEmission generated PartialEmission =
    CompleteEmissionFailure PartialTransportEmissionRejected.
Proof.
  reflexivity.
Qed.

Theorem past_frame_emission_never_establishes_completion :
  forall generated,
    establishCompleteEmission generated EmissionPastDeclaredFrame =
    CompleteEmissionFailure PastDeclaredFrameRejected.
Proof.
  reflexivity.
Qed.

Theorem invalid_emission_never_establishes_completion :
  forall generated,
    establishCompleteEmission generated InvalidEmissionExtent =
    CompleteEmissionFailure InvalidEmissionRejected.
Proof.
  reflexivity.
Qed.

Theorem complete_emission_preserves_generated_identity :
  forall representation owner,
    establishCompleteEmission
      (mkGeneratedEncodingEvidence representation owner)
      CompleteEmission =
    CompleteEmissionSuccess (mkCompleteEmissionEvidence representation owner).
Proof.
  reflexivity.
Qed.

Inductive SendProgressionError : Type :=
| SendEmissionRepresentationMismatch
| SendEmissionOwnerMismatch
| UnderlyingSendRejected.

Inductive SendProgressionResult : Type :=
| SendProgressionFailure : SendProgressionError -> SendProgressionResult
| SendProgressionAdvance : SendProgressionResult.

Definition commitQualifiedSend
  (generated : GeneratedEncodingEvidence)
  (emission : CompleteEmissionEvidence)
  (underlying : UnderlyingProgression)
  : SendProgressionResult :=
  if Nat.eqb (generatedRepresentation generated) (completeEmissionRepresentation emission) then
    if Nat.eqb (generatedOutputOwner generated) (completeEmissionOwner emission) then
      match underlying with
      | UnderlyingReject => SendProgressionFailure UnderlyingSendRejected
      | UnderlyingAdvance => SendProgressionAdvance
      end
    else SendProgressionFailure SendEmissionOwnerMismatch
  else SendProgressionFailure SendEmissionRepresentationMismatch.

Theorem successful_qualified_send_is_exact :
  forall generatedRepresentationId generatedOwner emissionRepresentationId emissionOwner underlying,
    commitQualifiedSend
      (mkGeneratedEncodingEvidence generatedRepresentationId generatedOwner)
      (mkCompleteEmissionEvidence emissionRepresentationId emissionOwner)
      underlying = SendProgressionAdvance ->
    generatedRepresentationId = emissionRepresentationId /\
    generatedOwner = emissionOwner /\
    underlying = UnderlyingAdvance.
Proof.
  intros generatedRepresentationId generatedOwner emissionRepresentationId emissionOwner underlying Hresult.
  unfold commitQualifiedSend in Hresult.
  simpl in Hresult.
  destruct (Nat.eqb generatedRepresentationId emissionRepresentationId) eqn:Hrepresentation.
  - destruct (Nat.eqb generatedOwner emissionOwner) eqn:Howner.
    + destruct underlying.
      * discriminate Hresult.
      * split.
        -- exact ((proj1 (Nat.eqb_eq generatedRepresentationId emissionRepresentationId)) Hrepresentation).
        -- split.
           ++ exact ((proj1 (Nat.eqb_eq generatedOwner emissionOwner)) Howner).
           ++ reflexivity.
    + discriminate Hresult.
  - discriminate Hresult.
Qed.

Theorem send_representation_mismatch_never_advances :
  forall generatedRepresentationId generatedOwner emissionRepresentationId emissionOwner underlying,
    generatedRepresentationId <> emissionRepresentationId ->
    commitQualifiedSend
      (mkGeneratedEncodingEvidence generatedRepresentationId generatedOwner)
      (mkCompleteEmissionEvidence emissionRepresentationId emissionOwner)
      underlying = SendProgressionFailure SendEmissionRepresentationMismatch.
Proof.
  intros generatedRepresentationId generatedOwner emissionRepresentationId emissionOwner underlying Hneq.
  unfold commitQualifiedSend.
  simpl.
  destruct (Nat.eqb generatedRepresentationId emissionRepresentationId) eqn:Hrepresentation.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq generatedRepresentationId emissionRepresentationId)) Hrepresentation).
  - reflexivity.
Qed.

Theorem send_owner_mismatch_never_advances :
  forall representation generatedOwner emissionOwner underlying,
    generatedOwner <> emissionOwner ->
    commitQualifiedSend
      (mkGeneratedEncodingEvidence representation generatedOwner)
      (mkCompleteEmissionEvidence representation emissionOwner)
      underlying = SendProgressionFailure SendEmissionOwnerMismatch.
Proof.
  intros representation generatedOwner emissionOwner underlying Hneq.
  unfold commitQualifiedSend.
  simpl.
  destruct (Nat.eqb representation representation) eqn:Hrepresentation.
  - destruct (Nat.eqb generatedOwner emissionOwner) eqn:Howner.
    + exfalso.
      apply Hneq.
      exact ((proj1 (Nat.eqb_eq generatedOwner emissionOwner)) Howner).
    + reflexivity.
  - exfalso.
    apply ((proj1 (Nat.eqb_neq representation representation)) Hrepresentation).
    reflexivity.
Qed.
