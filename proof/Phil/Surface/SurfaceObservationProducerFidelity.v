From Stdlib Require Import
  Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceObservationWire SurfaceBoundedSourceSimulation
  SurfaceBorrowStepErrorBridge SurfaceRepresentedBorrowTrace.

Import ListNotations.
Open Scope string_scope.

(*
  FSEM-01 producer-fidelity tranche (bounded pure projection).

  This module models the PURE artifact projection: eight metadata fields,
  actual observed phase/linear/loan checkpoints, and one classified outcome.
  Unlike the previous SourceBindsArtifact premise, a produced SourceRun and
  produced Artifact are bound by CONSTRUCTION, with no external field-equality
  assumption. The model checks the actual snapshot bits rather than making
  them up from the phase.

  CRITICAL TRUST BOUNDARY: Haskell's real BorrowTraceCheckpoint values are
  not Rocq values. Faithful conversion of actual Haskell source runs and
  Unicode Text/SHA256 data to ProducerInputs and RawCheckpoints is still a
  distinct assumption, checked on admitted specimens by CI. No global
  source-evaluator refinement is claimed.
*)

Record ProducerInputs : Type := mkProducerInputs {
  inputSourceHash : string;
  inputDeclarationRootHex : string;
  inputOwnerNameHex : string;
  inputViewNameHex : string;
  inputOwnerOrdinal : string;
  inputViewOrdinal : string
}.

Record RawCheckpoint : Type := mkRawCheckpoint {
  checkpointPhase : SurfaceRepresentedBorrowTrace.ModeledBorrowPhase;
  checkpointOwnerPresent : bool;
  checkpointLoanActive : bool
}.

Definition canonicalCheckpoint
  (phase : SurfaceRepresentedBorrowTrace.ModeledBorrowPhase)
  : RawCheckpoint :=
  mkRawCheckpoint phase
    (fst (SurfaceBorrowStepErrorBridge.expectedOwnerBits phase))
    (snd (SurfaceBorrowStepErrorBridge.expectedOwnerBits phase)).

Definition checkpointCode
  (phase : SurfaceRepresentedBorrowTrace.ModeledBorrowPhase) : string :=
  match phase with
  | SurfaceRepresentedBorrowTrace.ModelBeforeLoan => "B"
  | SurfaceRepresentedBorrowTrace.ModelLoanStarted => "S"
  | SurfaceRepresentedBorrowTrace.ModelBodyResult false => "N"
  | SurfaceRepresentedBorrowTrace.ModelBodyResult true => "E"
  | SurfaceRepresentedBorrowTrace.ModelLoanClosed => "C"
  | SurfaceRepresentedBorrowTrace.ModelOwnerReturned => "R"
  | SurfaceRepresentedBorrowTrace.ModelEscapeRejected => "X"
  end.

Definition flagCode (flag : bool) : string :=
  if flag then "1" else "0".

Definition renderCheckpoint (cut : RawCheckpoint) : string :=
  checkpointCode (checkpointPhase cut) ++
    (flagCode (checkpointOwnerPresent cut) ++
     flagCode (checkpointLoanActive cut)).

Definition renderCheckpoints (cuts : list RawCheckpoint) : string :=
  String.concat "," (List.map renderCheckpoint cuts).

Definition positiveSourceCheckpoints : list RawCheckpoint :=
  List.map canonicalCheckpoint
    SurfaceRepresentedBorrowTrace.admittedPositivePhases.

Definition rejectedSourceCheckpoints : list RawCheckpoint :=
  List.map canonicalCheckpoint
    SurfaceRepresentedBorrowTrace.admittedEscapePhases.

Theorem positive_projection_uses_exact_source_bits :
  renderCheckpoints positiveSourceCheckpoints =
    "B10,S11,N11,C10,R00".
Proof. reflexivity. Qed.

Theorem rejected_projection_leaves_live_loan :
  renderCheckpoints rejectedSourceCheckpoints =
    "B10,S11,E11,X11".
Proof. reflexivity. Qed.

Definition produceArtifact
  (inputs : ProducerInputs) (cuts : list RawCheckpoint)
  (terminal : SurfaceBoundedSourceSimulation.SourceTerminal)
  : SurfaceObservationWire.Artifact :=
  SurfaceObservationWire.mkArtifact
    (inputSourceHash inputs)
    (inputDeclarationRootHex inputs)
    (inputOwnerNameHex inputs)
    (inputViewNameHex inputs)
    (inputOwnerOrdinal inputs)
    (inputViewOrdinal inputs)
    (renderCheckpoints cuts)
    (SurfaceBoundedSourceSimulation.sourceTerminalCode terminal).

Definition produceRun
  (inputs : ProducerInputs) (cuts : list RawCheckpoint)
  (terminal : SurfaceBoundedSourceSimulation.SourceTerminal)
  : SurfaceBoundedSourceSimulation.SourceRun :=
  SurfaceBoundedSourceSimulation.mkSourceRun
    (inputSourceHash inputs)
    (inputDeclarationRootHex inputs)
    (inputOwnerNameHex inputs)
    (inputViewNameHex inputs)
    (inputOwnerOrdinal inputs)
    (inputViewOrdinal inputs)
    (renderCheckpoints cuts)
    terminal.

Theorem produced_run_binds_every_artifact_field :
  forall inputs cuts terminal,
    SurfaceBoundedSourceSimulation.SourceBindsArtifact
      (produceRun inputs cuts terminal)
      (produceArtifact inputs cuts terminal).
Proof.
  intros [hash root owner view ownerOrd viewOrd] cuts terminal.
  destruct terminal; repeat split; reflexivity.
Qed.

Theorem produced_trace_codes_equal_actual_snapshot_projection :
  forall inputs cuts terminal,
    SurfaceObservationWire.traceCodes
      (produceArtifact inputs cuts terminal) =
    renderCheckpoints cuts.
Proof. reflexivity. Qed.

Theorem produced_terminal_code_matches_source_terminal :
  forall inputs cuts terminal,
    SurfaceObservationWire.terminalCode
      (produceArtifact inputs cuts terminal) =
    SurfaceBoundedSourceSimulation.sourceTerminalCode terminal.
Proof. reflexivity. Qed.

Theorem produced_metadata_is_not_rewritten :
  forall inputs cuts terminal,
    SurfaceObservationWire.sourceHash
      (produceArtifact inputs cuts terminal) =
      inputSourceHash inputs /\
    SurfaceObservationWire.declarationRootHex
      (produceArtifact inputs cuts terminal) =
      inputDeclarationRootHex inputs /\
    SurfaceObservationWire.ownerNameHex
      (produceArtifact inputs cuts terminal) =
      inputOwnerNameHex inputs /\
    SurfaceObservationWire.viewNameHex
      (produceArtifact inputs cuts terminal) =
      inputViewNameHex inputs /\
    SurfaceObservationWire.ownerOrdinal
      (produceArtifact inputs cuts terminal) =
      inputOwnerOrdinal inputs /\
    SurfaceObservationWire.viewOrdinal
      (produceArtifact inputs cuts terminal) =
      inputViewOrdinal inputs.
Proof.
  intros [hash root owner view ownerOrd viewOrd] cuts terminal.
  repeat split; reflexivity.
Qed.

(* There is no free SourceBindsArtifact premise in this theorem: produced
   evidence derives that relation via fieldwise equality. The remaining
   acceptance premise is the explicit v1 decoder's validity condition,
   including hash format and canonical owner/view ordinal representation. *)
Theorem exact_produced_record_simulates :
  forall inputs cuts terminal owner,
    SurfaceObservationWire.validArtifact
      (produceArtifact inputs cuts terminal) = true ->
    SurfaceBoundedSourceSimulation.BoundedSourceSimulation
      (produceRun inputs cuts terminal) owner.
Proof.
  intros inputs cuts terminal owner Hvalid.
  eapply SurfaceBoundedSourceSimulation.decoded_source_run_simulates_bounded_model
    with (wire := SurfaceObservationWire.encodeArtifact
      (produceArtifact inputs cuts terminal))
         (artifact := produceArtifact inputs cuts terminal).
  - apply SurfaceObservationWire.decode_encode_valid_artifact.
    exact Hvalid.
  - apply produced_run_binds_every_artifact_field.
Qed.

Theorem accepted_producer_record_simulates :
  forall inputs owner,
    SurfaceObservationWire.validArtifact
      (produceArtifact inputs positiveSourceCheckpoints
        SurfaceBoundedSourceSimulation.SourceReturnedBytes8) = true ->
    SurfaceBoundedSourceSimulation.BoundedSourceSimulation
      (produceRun inputs positiveSourceCheckpoints
        SurfaceBoundedSourceSimulation.SourceReturnedBytes8) owner.
Proof.
  intros inputs owner Hvalid.
  apply exact_produced_record_simulates.
  exact Hvalid.
Qed.

Theorem rejected_producer_record_simulates :
  forall inputs owner,
    SurfaceObservationWire.validArtifact
      (produceArtifact inputs rejectedSourceCheckpoints
        SurfaceBoundedSourceSimulation.SourceRejectedBorrowEscape) = true ->
    SurfaceBoundedSourceSimulation.BoundedSourceSimulation
      (produceRun inputs rejectedSourceCheckpoints
        SurfaceBoundedSourceSimulation.SourceRejectedBorrowEscape) owner.
Proof.
  intros inputs owner Hvalid.
  apply exact_produced_record_simulates.
  exact Hvalid.
Qed.

Theorem rejected_producer_record_cannot_continue :
  forall inputs owner event suffix,
    SurfaceObservationWire.validArtifact
      (produceArtifact inputs rejectedSourceCheckpoints
        SurfaceBoundedSourceSimulation.SourceRejectedBorrowEscape) = true ->
    SurfaceBorrowStepErrorBridge.replay
      (SurfaceBoundedSourceSimulation.modeledFinal owner
        SurfaceBoundedSourceSimulation.SourceRejectedBorrowEscape)
      (event :: suffix) = None.
Proof.
  intros inputs owner event suffix Hvalid.
  pose proof
    (rejected_producer_record_simulates inputs owner Hvalid)
    as [_ [_ Hterminal]].
  simpl.
  rewrite (Hterminal event).
  reflexivity.
Qed.

(* The producer model does not assert that every Haskell snapshot maps to
   a valid record. The validator is fail-closed; arbitrary, inconsistent
   checkpoint sequences must not gain authority merely by being serialized. *)
