From Stdlib Require Import Strings.String Bool.Bool Lists.List.
From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceObservationWire SurfaceBorrowStepErrorBridge
  SurfaceRepresentedBorrowTrace SurfaceDeclarationIdentityBridge.

Import ListNotations.
Open Scope string_scope.

(*
  FSEM-01: bounded SOURCE-OBSERVATION-to-model simulation.

  A SourceRun is an observation of an ACTUAL production checker run, not a
  Rocq implementation of the Haskell checker. The SourceBindsArtifact
  premise is the explicit trusted producer/serialization contract: digest,
  declaration root, owner/view Core names, ordinals, checkpoints and terminal
  outcome faithfully describe the source run. CI checks this contract for
  four real Haskell-produced specimens, but cannot prove it for all sources.

  The decoder and model replay, in contrast, are certified Rocq functions.
  This theorem does NOT prove general Haskell refinement, SHA256/UTF8
  correctness, or source-level small-step soundness.
*)

Inductive SourceTerminal : Type :=
| SourceReturnedBytes8
| SourceRejectedBorrowEscape.

Record SourceRun : Type := mkSourceRun {
  runSourceDigest : string;
  runDeclarationRootHex : string;
  runOwnerNameHex : string;
  runViewNameHex : string;
  runOwnerOrdinal : string;
  runViewOrdinal : string;
  runTraceCodes : string;
  runTerminal : SourceTerminal
}.

Definition sourceTerminalCode (outcome : SourceTerminal) : string :=
  match outcome with
  | SourceReturnedBytes8 => "OK:Bytes8"
  | SourceRejectedBorrowEscape =>
      "ERR:BorrowEscape:shared view escapes its lexical scope"
  end.

Definition SourceBindsArtifact
  (run : SourceRun) (artifact : SurfaceObservationWire.Artifact) : Prop :=
  runSourceDigest run = SurfaceObservationWire.sourceHash artifact /\
  runDeclarationRootHex run =
    SurfaceObservationWire.declarationRootHex artifact /\
  runOwnerNameHex run = SurfaceObservationWire.ownerNameHex artifact /\
  runViewNameHex run = SurfaceObservationWire.viewNameHex artifact /\
  runOwnerOrdinal run = SurfaceObservationWire.ownerOrdinal artifact /\
  runViewOrdinal run = SurfaceObservationWire.viewOrdinal artifact /\
  runTraceCodes run = SurfaceObservationWire.traceCodes artifact /\
  sourceTerminalCode (runTerminal run) =
    SurfaceObservationWire.terminalCode artifact.

(* Catalog entries are canonical UTF-8-hex declaration-root tokens from
   versioned observations; they are not persistent Phil declaration numbers.
   This deliberately avoids assuming that raw Unicode Text is Rocq String. *)
Definition SourceOwnerCatalog
  (catalog : list string)
  (owner : BindingSemantics.BinderKey)
  (run : SourceRun) : Prop :=
  NoDup catalog /\
  nth_error catalog (fst owner) = Some (runDeclarationRootHex run) /\
  SurfaceObservationWire.canonicalNatural (runOwnerOrdinal run) =
    Some (snd owner).

Theorem catalog_bound_run_has_unique_model_owner :
  forall catalog first second run,
    NoDup catalog ->
    SourceOwnerCatalog catalog first run ->
    SourceOwnerCatalog catalog second run ->
    first = second.
Proof.
  intros catalog [firstDecl firstOrd] [secondDecl secondOrd] run
    Hcatalog [_ [Hroot1 Hordinal1]] [_ [Hroot2 Hordinal2]].
  simpl in *.
  pose proof
    (SurfaceDeclarationIdentityBridge.distinct_catalog_positions_have_distinct_roots
      catalog firstDecl secondDecl (runDeclarationRootHex run)
      Hcatalog Hroot1 Hroot2) as Hdecl.
  rewrite Hordinal1 in Hordinal2.
  injection Hordinal2 as Hordinal.
  subst.
  reflexivity.
Qed.

Definition sourceEventSequence (outcome : SourceTerminal)
  : list SurfaceBorrowStepErrorBridge.LoanEvent :=
  match outcome with
  | SourceReturnedBytes8 =>
      [SurfaceBorrowStepErrorBridge.EventBegin;
       SurfaceBorrowStepErrorBridge.EventBodySafe;
       SurfaceBorrowStepErrorBridge.EventClose;
       SurfaceBorrowStepErrorBridge.EventReturn]
  | SourceRejectedBorrowEscape =>
      [SurfaceBorrowStepErrorBridge.EventBegin;
       SurfaceBorrowStepErrorBridge.EventBodyEscapes;
       SurfaceBorrowStepErrorBridge.EventRejectBorrowEscape]
  end.

Definition sourceFinalPhase (outcome : SourceTerminal)
  : SurfaceRepresentedBorrowTrace.ModeledBorrowPhase :=
  match outcome with
  | SourceReturnedBytes8 => SurfaceRepresentedBorrowTrace.ModelOwnerReturned
  | SourceRejectedBorrowEscape =>
      SurfaceRepresentedBorrowTrace.ModelEscapeRejected
  end.

Definition sourceFinalOutcome (outcome : SourceTerminal)
  : SurfaceBorrowStepErrorBridge.ModeledOutcome :=
  match outcome with
  | SourceReturnedBytes8 =>
      SurfaceBorrowStepErrorBridge.ModeledAcceptTerminal
  | SourceRejectedBorrowEscape =>
      SurfaceBorrowStepErrorBridge.ModeledRejectBorrowEscape
  end.

Definition modeledInitial
  (owner : BindingSemantics.BinderKey)
  : SurfaceBorrowStepErrorBridge.ObservedLoanCut :=
  SurfaceBorrowStepErrorBridge.modeledCut
    owner SurfaceRepresentedBorrowTrace.ModelBeforeLoan.

Definition modeledFinal
  (owner : BindingSemantics.BinderKey)
  (outcome : SourceTerminal)
  : SurfaceBorrowStepErrorBridge.ObservedLoanCut :=
  SurfaceBorrowStepErrorBridge.modeledCut owner (sourceFinalPhase outcome).

Definition BoundedSourceSimulation
  (run : SourceRun) (owner : BindingSemantics.BinderKey) : Prop :=
  SurfaceBorrowStepErrorBridge.replay
    (modeledInitial owner) (sourceEventSequence (runTerminal run)) =
    Some (modeledFinal owner (runTerminal run)) /\
  SurfaceBorrowStepErrorBridge.classifyTerminal
    (sourceFinalPhase (runTerminal run)) =
    Some (sourceFinalOutcome (runTerminal run)) /\
  (forall event,
    SurfaceBorrowStepErrorBridge.checkedAdvance
      (modeledFinal owner (runTerminal run)) event = None).

Lemma replay_preserves_exact_owner :
  forall events initial final,
    SurfaceBorrowStepErrorBridge.replay initial events = Some final ->
    SurfaceBorrowStepErrorBridge.observedOwner final =
      SurfaceBorrowStepErrorBridge.observedOwner initial.
Proof.
  induction events as [|event rest IH]; intros initial final Hreplay.
  - simpl in Hreplay. inversion Hreplay; reflexivity.
  - simpl in Hreplay.
    destruct (SurfaceBorrowStepErrorBridge.checkedAdvance initial event)
      as [next|] eqn:Hstep; try discriminate.
    rewrite (IH next final Hreplay).
    apply SurfaceBorrowStepErrorBridge.checked_advance_preserves_owner
      in Hstep.
    exact Hstep.
Qed.

Theorem decoded_source_run_simulates_bounded_model :
  forall wire artifact run owner,
    SurfaceObservationWire.decodeArtifact wire = Some artifact ->
    SourceBindsArtifact run artifact ->
    BoundedSourceSimulation run owner.
Proof.
  intros wire artifact run owner Hdecoded Hbinding.
  unfold SourceBindsArtifact in Hbinding.
  destruct Hbinding as
    [_ [_ [_ [_ [_ [_ [_ HterminalBinding]]]]]]].
  pose proof
    (SurfaceObservationWire.decoded_wire_replays_one_terminal_model
      wire artifact owner Hdecoded) as Hmodel.
  destruct Hmodel as
    [[_ [Haccept HacceptedReplay]] |
     [_ [Hreject HrejectedReplay]]].
  - destruct (runTerminal run) eqn:Hsource.
    + unfold BoundedSourceSimulation, modeledInitial, modeledFinal.
      rewrite Hsource. simpl.
      split; [exact HacceptedReplay |].
      split; [reflexivity |].
      intro event.
      apply SurfaceBorrowStepErrorBridge.no_continuation_after_terminal_return.
      reflexivity.
    + simpl in HterminalBinding.
      rewrite Haccept in HterminalBinding.
      discriminate.
  - destruct (runTerminal run) eqn:Hsource.
    + simpl in HterminalBinding.
      rewrite Hreject in HterminalBinding.
      discriminate.
    + unfold BoundedSourceSimulation, modeledInitial, modeledFinal.
      rewrite Hsource. simpl.
      split; [exact HrejectedReplay |].
      split; [reflexivity |].
      intro event.
      apply SurfaceBorrowStepErrorBridge.no_continuation_after_borrow_escape.
      reflexivity.
Qed.

Theorem decoded_catalog_bound_source_simulates :
  forall wire artifact run catalog owner,
    SurfaceObservationWire.decodeArtifact wire = Some artifact ->
    SourceBindsArtifact run artifact ->
    SourceOwnerCatalog catalog owner run ->
    BoundedSourceSimulation run owner /\
    SourceOwnerCatalog catalog owner run.
Proof.
  intros wire artifact run catalog owner Hdecoded Hbinding Hcatalog.
  split.
  - eapply decoded_source_run_simulates_bounded_model; eassumption.
  - exact Hcatalog.
Qed.

Theorem decoded_source_run_has_no_post_error_continuation :
  forall wire artifact run owner event suffix,
    SurfaceObservationWire.decodeArtifact wire = Some artifact ->
    SourceBindsArtifact run artifact ->
    runTerminal run = SourceRejectedBorrowEscape ->
    SurfaceBorrowStepErrorBridge.replay
      (modeledFinal owner (runTerminal run))
      (event :: suffix) = None.
Proof.
  intros wire artifact run owner event suffix Hdecoded Hbinding Hrejected.
  pose proof (decoded_source_run_simulates_bounded_model
    wire artifact run owner Hdecoded Hbinding) as Hsimulation.
  destruct Hsimulation as [_ [_ Hterminal]].
  simpl.
  rewrite (Hterminal event).
  reflexivity.
Qed.

Theorem decoded_source_run_has_no_post_return_continuation :
  forall wire artifact run owner event suffix,
    SurfaceObservationWire.decodeArtifact wire = Some artifact ->
    SourceBindsArtifact run artifact ->
    runTerminal run = SourceReturnedBytes8 ->
    SurfaceBorrowStepErrorBridge.replay
      (modeledFinal owner (runTerminal run))
      (event :: suffix) = None.
Proof.
  intros wire artifact run owner event suffix Hdecoded Hbinding Hreturned.
  pose proof (decoded_source_run_simulates_bounded_model
    wire artifact run owner Hdecoded Hbinding) as Hsimulation.
  destruct Hsimulation as [_ [_ Hterminal]].
  simpl.
  rewrite (Hterminal event).
  reflexivity.
Qed.

Theorem decoded_source_run_preserves_owner_to_terminal :
  forall wire artifact run owner,
    SurfaceObservationWire.decodeArtifact wire = Some artifact ->
    SourceBindsArtifact run artifact ->
    SurfaceBorrowStepErrorBridge.observedOwner
      (modeledFinal owner (runTerminal run)) = owner.
Proof.
  intros wire artifact run owner Hdecoded Hbinding.
  pose proof (decoded_source_run_simulates_bounded_model
    wire artifact run owner Hdecoded Hbinding) as [Hreplay _].
  pose proof
    (replay_preserves_exact_owner
      (sourceEventSequence (runTerminal run))
      (modeledInitial owner)
      (modeledFinal owner (runTerminal run))
      Hreplay) as Howner.
  exact Howner.
Qed.

(* The proof is intentionally conditional on SourceBindsArtifact.
   Four CI-generated witnesses discharge that premise for source specimens
   using independent source-file hashes and exact owner/view name checks.
   No claim is made for arbitrary Haskell executions. *)
