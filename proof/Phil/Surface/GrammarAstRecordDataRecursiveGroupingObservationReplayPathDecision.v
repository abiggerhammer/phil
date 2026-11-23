From Stdlib Require Import Lists.List Strings.String Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstStructuralModeSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClosure
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathQuotient
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathSingleStep.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: turn the finite admitted Record/Data
  replay-path observation contract into a constructive decision procedure.
  Compare actual Some observations, never equality of two None results.
  Proof-side only; no new parser, trusted admission, production Haskell
  AST binding, G2/G4 completion or Phase 1 closure. The quotient remains
  intentionally non-injective on exact public keys.
*)

Definition phase1_surface_observed_mode_eq_dec :
  forall left right : Phase1SurfaceStructuralMode,
    {left = right} + {left <> right}.
Proof.
  decide equality.
Defined.

Definition phase1_surface_observed_payload_eq_dec :
  forall left right : Phase1SurfaceRecursiveGroupingObservedPayload,
    {left = right} + {left <> right}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try (apply list_eq_dec; apply string_dec).
Defined.

Definition phase1_surface_observed_variant_eq_dec :
  forall left right : Phase1SurfaceRecursiveGroupingObservedVariant,
    {left = right} + {left <> right}.
Proof.
  decide equality;
    try apply string_dec;
    try apply phase1_surface_observed_payload_eq_dec.
Defined.

Definition phase1_surface_observed_generic_param_eq_dec :
  forall left right : string * nat,
    {left = right} + {left <> right}.
Proof.
  decide equality; try apply string_dec; try apply Nat.eq_dec.
Defined.

Definition phase1_surface_observed_optional_mode_eq_dec :
  forall left right : option Phase1SurfaceStructuralMode,
    {left = right} + {left <> right}.
Proof.
  decide equality.
  apply phase1_surface_observed_mode_eq_dec.
Defined.

Definition phase1_surface_observed_record_data_eq_dec :
  forall left right : Phase1SurfaceRecursiveGroupingObservedRecordData,
    {left = right} + {left <> right}.
Proof.
  decide equality;
    try apply string_dec;
    try apply Nat.eq_dec;
    try apply phase1_surface_observed_mode_eq_dec;
    try apply phase1_surface_observed_payload_eq_dec;
    try apply phase1_surface_observed_variant_eq_dec;
    try apply phase1_surface_observed_generic_param_eq_dec;
    try apply phase1_surface_observed_optional_mode_eq_dec;
    try (apply list_eq_dec; apply string_dec);
    try (apply list_eq_dec; apply Nat.eq_dec);
    try (apply list_eq_dec; apply phase1_surface_observed_generic_param_eq_dec);
    try (apply list_eq_dec; apply phase1_surface_observed_variant_eq_dec).
Defined.

Definition phase1_surface_admitted_replay_path_dec :
  forall left right : Phase1SurfaceDeclarationSpine,
    {phase1_surface_admitted_replay_path left right} +
    {~ phase1_surface_admitted_replay_path left right}.
Proof.
  intros left right.
  destruct (phase1_surface_normalized_observation left)
    as [left_observed |] eqn:Hleft.
  - destruct (phase1_surface_normalized_observation right)
      as [right_observed |] eqn:Hright.
    + destruct (phase1_surface_observed_record_data_eq_dec
        left_observed right_observed) as [Heq | Hneq].
      * left.
        eapply phase1_surface_replay_path_equal_successful_classifiers_connect
          with (observed := left_observed).
        -- exact Hleft.
        -- rewrite Heq. exact Hright.
      * right.
        intro Hpath.
        destruct (phase1_surface_replay_path_classifiers_equal_and_present
          left right Hpath) as [Hequal _].
        rewrite Hleft, Hright in Hequal.
        apply Hneq.
        now injection Hequal.
    + right.
      intro Hpath.
      destruct (proj1
        (phase1_surface_replay_path_iff_same_successful_classifier left right)
        Hpath) as [observed [_ Hsome]].
      rewrite Hright in Hsome.
      discriminate Hsome.
  - right.
    intro Hpath.
    destruct (proj1
      (phase1_surface_replay_path_iff_same_successful_classifier left right)
      Hpath) as [observed [Hsome _]].
    rewrite Hleft in Hsome.
    discriminate Hsome.
Defined.

Definition phase1_surface_replay_path_connectedb
  (left right : Phase1SurfaceDeclarationSpine) : bool :=
  if phase1_surface_admitted_replay_path_dec left right then true else false.

Theorem phase1_surface_replay_path_connectedb_iff :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true <->
    phase1_surface_admitted_replay_path left right.
Proof.
  intros left right.
  unfold phase1_surface_replay_path_connectedb.
  destruct (phase1_surface_admitted_replay_path_dec left right)
    as [Hpath | Hno]; simpl.
  - split; [intro Htrue; exact Hpath | intro Hproved; reflexivity].
  - split; [discriminate | intro Hpath; contradiction].
Qed.

Theorem phase1_surface_replay_path_connectedb_iff_same_success :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true <->
    exists observed,
      phase1_surface_normalized_observation left = Some observed /\
      phase1_surface_normalized_observation right = Some observed.
Proof.
  intros left right.
  transitivity (phase1_surface_admitted_replay_path left right).
  - apply phase1_surface_replay_path_connectedb_iff.
  - apply phase1_surface_replay_path_iff_same_successful_classifier.
Qed.

Theorem phase1_surface_replay_path_connectedb_rejected_left :
  forall left right,
    phase1_surface_normalized_observation left = None ->
    phase1_surface_replay_path_connectedb left right = false.
Proof.
  intros left right Hreject.
  destruct (phase1_surface_replay_path_connectedb left right)
    eqn:Hconnected; [|reflexivity].
  apply phase1_surface_replay_path_connectedb_iff in Hconnected.
  destruct (proj1
    (phase1_surface_replay_path_iff_same_successful_classifier left right)
    Hconnected) as [observed [Hsome _]].
  rewrite Hreject in Hsome.
  discriminate Hsome.
Qed.

Theorem phase1_surface_replay_path_connectedb_rejected_right :
  forall left right,
    phase1_surface_normalized_observation right = None ->
    phase1_surface_replay_path_connectedb left right = false.
Proof.
  intros left right Hreject.
  destruct (phase1_surface_replay_path_connectedb left right)
    eqn:Hconnected; [|reflexivity].
  apply phase1_surface_replay_path_connectedb_iff in Hconnected.
  destruct (proj1
    (phase1_surface_replay_path_iff_same_successful_classifier left right)
    Hconnected) as [observed [_ Hsome]].
  rewrite Hreject in Hsome.
  discriminate Hsome.
Qed.

Theorem phase1_surface_replay_path_connectedb_not_exact_key_equality :
  exists left right,
    phase1_surface_replay_path_connectedb left right = true /\
    left <> right.
Proof.
  destruct phase1_surface_replay_single_step_not_exact_key_equality
    as [left [right [Hstep Hdistinct]]].
  exists left, right.
  split; [|exact Hdistinct].
  apply phase1_surface_replay_path_connectedb_iff.
  apply phase1_surface_replay_single_step_expands_to_path.
  exact Hstep.
Qed.

Example phase1_surface_replay_path_connectedb_malformed_record_rejected :
  forall other,
    phase1_surface_replay_path_connectedb
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      other = false.
Proof.
  intro other.
  apply phase1_surface_replay_path_connectedb_rejected_left.
  apply (proj2 (phase1_surface_normalized_observation_none_iff_rejection _)).
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
