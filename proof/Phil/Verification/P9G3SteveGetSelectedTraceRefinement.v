(* Scratch-first P9 composition.  The source judgements are the admitted
   FSEM-05 selected reference rules; the target and source observations are
   the accepted FSEM-06 typed Core/plan and labelled source rules.
   Concrete native admission/representation is a separate checked gate. *)
From Stdlib Require Import List Arith Lia Bool.Bool Strings.String Extraction.
From Phil.Verification Require Import FSEM05SteveGetSelectedSourceEvents
  FSEM06SteveGetSelectedCorePayloadRefinement.
Import ListNotations SelectedSteveGetEvents.

(* P2: the existing selected source executable model reflects every
   independently derived labelled source trace, not just a test run. *)
Theorem p9_source_trace_replay : forall s labels events final,
  source_trace s labels events final ->
  replay_source s labels = Some (final, events).
Proof.
  intros s labels events final H.
  induction H as [s|s label middle labels observations final Hstep Htail IH].
  - reflexivity.
  - simpl. rewrite (selected_step_coverage _ _ _ Hstep), IH. reflexivity.
Qed.

Theorem p9_source_model_reflection : forall s labels events final,
  replay_source s labels = Some (final, events) <->
  source_trace s labels events final.
Proof.
  intros. split; [apply replay_source_is_labelled | apply p9_source_trace_replay].
Qed.

Lemma p9_step_history_monotone : forall s label final,
  selected_source_step s label final ->
  state_next s <= state_next final /\
  (forall x, In x (state_issued s) -> In x (state_issued final)) /\
  (forall x, In x (state_retired s) -> In x (state_retired final)).
Proof.
  intros s label final H. destruct H; simpl;
    repeat split; try lia; intros x Hx; simpl; auto.
Qed.

Theorem p9_source_history_monotone : forall s labels events final,
  source_trace s labels events final ->
  state_next s <= state_next final /\
  (forall x, In x (state_issued s) -> In x (state_issued final)) /\
  (forall x, In x (state_retired s) -> In x (state_retired final)).
Proof.
  intros s labels events final H.
  induction H as [s|s label middle labels observations final Hstep Htail IH].
  - repeat split; auto.
  - destruct (p9_step_history_monotone _ _ _ Hstep) as [Hn [Hi Hr]].
    destruct IH as [Hn' [Hi' Hr']].
    split; [lia|]. split; intros x Hx; auto.
Qed.

Theorem p9_source_replay_safety : forall labels events final,
  replay_source (Idle 0 [] []) labels = Some (final, events) ->
  canonical_lifecycle final /\
  ~ In (state_next final) (state_issued final).
Proof.
  intros labels events final H.
  apply replay_source_is_labelled in H.
  apply source_trace_forget in H.
  split.
  - apply canonical_lifecycle_reachable; exact H.
  - apply fresh_issued_origin_in_every_reachable_state; exact H.
Qed.

(* P3/P4: concatenate the PARTICULAR source segments accepted by the
   dynamic checker, rather than selecting a different existential source
   execution. Every step threads one exact immutable E suffix. *)
Inductive p9_checked_path (input : NativeSubject) (expected : selected_binding) :
  nat -> target_state -> list qualified_reply ->
  list qualified_reply -> list offered -> list observation -> list observation ->
  target_state -> list qualified_reply -> Prop :=
| P9PathNil : forall c e,
    p9_checked_path input expected 0 c e [] [] [] [] c e
| P9PathCons : forall count c e middle rest final remaining
    used labels target_events source_events
    used_more labels_more target_more source_more,
    check_segment input expected c e middle rest target_events
      used labels source_events = true ->
    p9_checked_path input expected count middle rest used_more labels_more
      target_more source_more final remaining ->
    p9_checked_path input expected (S count) c e
      (used ++ used_more) (labels ++ labels_more)
      (target_events ++ target_more) (source_events ++ source_more)
      final remaining.

Theorem p9_checked_path_sound : forall input expected count c e used labels
    target_events source_events final remaining,
  p9_checked_path input expected count c e used labels target_events
    source_events final remaining ->
  core_trace input expected c e target_events final remaining /\
  e = used ++ remaining /\
  qualified_source_segment input expected (source_projection c)
    (source_projection final) used labels source_events /\
  erase_diagnostic target_events ++ pending_unit final =
    pending_unit c ++ source_events.
Proof.
  intros input expected count c e used labels target_events source_events final remaining H.
  induction H as [c e|count c e middle rest final remaining
    used labels target_events source_events
    used_more labels_more target_more source_more Hcheck Hpath IH].
  - split; [constructor|]. split; [reflexivity|]. split.
    + unfold qualified_source_segment. split; [constructor|].
      split; [reflexivity|constructor].
    + simpl. rewrite app_nil_r. reflexivity.
  - destruct (check_segment_sound _ _ _ _ _ _ _ _ _ _ Hcheck)
      as [_ [Hstep [He [_ [Hseg Hobs]]]]].
    destruct IH as [Hcore [Hrest [Hseg' Hobs']]].
    unfold qualified_source_segment in Hseg, Hseg'.
    destruct Hseg as [Hqual [Hlabels Hsource]].
    destruct Hseg' as [Hqual' [Hlabels' Hsource']].
    split.
    + econstructor; eauto.
    + split.
      * rewrite He, Hrest, app_assoc. reflexivity.
      * split.
        -- unfold qualified_source_segment. split.
           ++ apply Forall_app. split; assumption.
           ++ split.
              ** unfold external_labels in *. rewrite filter_app, map_app,
                   Hlabels, Hlabels'. reflexivity.
              ** eapply source_trace_append; eauto.
        -- unfold erase_diagnostic in *. rewrite filter_app.
           rewrite <- app_assoc, Hobs', app_assoc, Hobs, <- app_assoc.
           reflexivity.
Qed.

Theorem p9_checked_path_safety : forall input expected count c e used labels
    target_events source_events final remaining,
  p9_checked_path input expected count c e used labels target_events
    source_events final remaining ->
  canonical_lifecycle (source_projection c) ->
  canonical_lifecycle (source_projection final) /\
  replay_source (source_projection c) labels =
    Some (source_projection final, source_events) /\
  state_next (source_projection c) <= state_next (source_projection final) /\
  (forall x, In x (state_issued (source_projection c)) ->
    In x (state_issued (source_projection final))) /\
  (forall x, In x (state_retired (source_projection c)) ->
    In x (state_retired (source_projection final))).
Proof.
  intros input expected count c e used labels target_events source_events final remaining H Hl.
  destruct (p9_checked_path_sound _ _ _ _ _ _ _ _ _ _ _ H)
    as [Hcore [_ [Hseg _]]].
  unfold qualified_source_segment in Hseg.
  destruct Hseg as [_ [_ Hsource]].
  split.
  - eapply target_trace_preserves_lifecycle; eauto.
  - split.
    + apply p9_source_trace_replay; exact Hsource.
    + apply p9_source_history_monotone in Hsource. exact Hsource.
Qed.

(* P5: no unbounded administrative stutter in this checked Core path. *)
Theorem p9_checked_path_rank : forall input expected count c e used labels
    target_events source_events final remaining,
  p9_checked_path input expected count c e used labels target_events
    source_events final remaining ->
  count + target_rank final <= target_rank c.
Proof.
  intros input expected count c e used labels target_events source_events final remaining H.
  induction H as [c e|count c e middle rest final remaining
    used labels target_events source_events
    used_more labels_more target_more source_more Hcheck Hpath IH].
  - simpl; lia.
  - destruct (check_segment_sound _ _ _ _ _ _ _ _ _ _ Hcheck)
      as [_ [Hstep _]].
    pose proof (target_step_rank_decreases _ _ _ _ _ _ _ Hstep) as Hrank.
    lia.
Qed.

Theorem p9_completed_checked_path : forall input expected count n issued retired
    e used labels target_events source_events n' issued' retired' branch,
  p9_checked_path input expected count (TRead n issued retired) e used labels
    target_events source_events (TDone n' issued' retired' branch) [] ->
  e = used /\
  qualified_source_segment input expected (AwaitRead n issued retired)
    (Done n' issued' retired' branch) used labels (erase_diagnostic target_events) /\
  count <= 3.
Proof.
  intros input expected count n issued retired e used labels target_events
    source_events n' issued' retired' branch H.
  pose proof (p9_checked_path_rank _ _ _ _ _ _ _ _ _ _ _ H) as Hrank.
  destruct (p9_checked_path_sound _ _ _ _ _ _ _ _ _ _ _ H)
    as [_ [He [Hseg Hobs]]].
  simpl in Hobs, Hseg, Hrank.
  rewrite app_nil_r in Hobs, He.
  split; [exact He|]. split.
  - rewrite Hobs. exact Hseg.
  - lia.
Qed.

(* P0/P6 exact carrier bytes, separately from the span-free semantic
   revision and the full typed Core selector. The literal below is the
   original repository blob 8de9853762201b516d7c05bfd5568e54acbd7dc8,
   not a caller-selected pin. The native scratch harness must invoke
   this extracted gate BEFORE the accepted sealed joint admission. *)
Definition p9_original_bytes : name :=
  [99; 111; 109; 112; 111; 110; 101; 110; 116; 32; 83; 116; 101; 118; 101; 71; 101; 116; 32; 112; 114; 111; 118; 105; 100; 101; 115; 32;
   85; 110; 105; 116; 32; 123; 10; 32; 32; 32; 32; 100; 101; 99; 105; 100; 101; 32; 98; 108; 111; 98; 95; 114; 101; 97; 100; 40;
   99; 111; 110; 116; 101; 110; 116; 73; 100; 41; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 102; 111; 117; 110; 100; 40; 98;
   121; 116; 101; 115; 41; 32; 61; 62; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 108; 101; 116; 32; 100;
   105; 103; 101; 115; 116; 68; 101; 99; 105; 115; 105; 111; 110; 32; 61; 32; 98; 111; 114; 114; 111; 119; 32; 98; 121; 116; 101; 115;
   32; 97; 115; 32; 98; 121; 116; 101; 115; 86; 105; 101; 119; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32;
   32; 32; 32; 32; 100; 105; 103; 101; 115; 116; 95; 99; 104; 101; 99; 107; 40; 99; 111; 110; 116; 101; 110; 116; 73; 100; 44; 32;
   98; 121; 116; 101; 115; 86; 105; 101; 119; 41; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 125; 10; 10; 32; 32;
   32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 100; 101; 99; 105; 100; 101; 32; 100; 105; 103; 101; 115; 116; 68; 101; 99; 105; 115;
   105; 111; 110; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 97; 99; 99; 101; 112; 116;
   101; 100; 32; 61; 62; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32;
   114; 101; 108; 101; 97; 115; 101; 32; 98; 121; 116; 101; 115; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32;
   32; 32; 32; 32; 32; 32; 114; 101; 116; 117; 114; 110; 32; 117; 110; 105; 116; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32;
   32; 32; 32; 32; 32; 32; 125; 10; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 114; 101; 106;
   101; 99; 116; 101; 100; 40; 114; 101; 97; 115; 111; 110; 41; 32; 61; 62; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32;
   32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 114; 101; 108; 101; 97; 115; 101; 32; 98; 121; 116; 101; 115; 10; 32; 32; 32;
   32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 114; 101; 116; 117; 114; 110; 32; 117; 110; 105; 116;
   10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 125; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32;
   32; 32; 32; 125; 10; 32; 32; 32; 32; 32; 32; 32; 32; 125; 10; 10; 32; 32; 32; 32; 32; 32; 32; 32; 110; 111; 116; 45;
   102; 111; 117; 110; 100; 32; 61; 62; 32; 123; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 114; 101; 116; 117; 114;
   110; 32; 117; 110; 105; 116; 10; 32; 32; 32; 32; 32; 32; 32; 32; 125; 10; 10; 32; 32; 32; 32; 32; 32; 32; 32; 115; 116;
   111; 114; 97; 103; 101; 45; 102; 97; 105; 108; 117; 114; 101; 40; 114; 101; 97; 115; 111; 110; 41; 32; 61; 62; 32; 123; 10; 32;
   32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 114; 101; 116; 117; 114; 110; 32; 117; 110; 105; 116; 10; 32; 32; 32; 32; 32;
   32; 32; 32; 125; 10; 32; 32; 32; 32; 125; 10; 125; 10].

Definition p9_raw_accepts (raw : name) : bool :=
  name_eqb raw p9_original_bytes.

Theorem p9_raw_reflection : forall raw,
  p9_raw_accepts raw = true <-> raw = p9_original_bytes.
Proof. intros; unfold p9_raw_accepts; apply name_eqb_sound. Qed.

Definition p9_input_accepts (raw : name) (input : NativeSubject)
    (expected actual : selected_binding) : bool :=
  andb (p9_raw_accepts raw)
    (andb (selected_native_accepts input)
      (native_binding_accepts input expected actual)).

(* This does NOT derive authority for an arbitrary expected binding.
   The independently checked source+invocation producer must supply it. *)
Theorem p9_input_reflection : forall raw input expected actual,
  p9_input_accepts raw input expected actual = true <->
  raw = p9_original_bytes /\ input = expected_native /\
  binding_matches_native input expected actual.
Proof.
  intros. unfold p9_input_accepts.
  rewrite !Bool.andb_true_iff, p9_raw_reflection,
    selected_native_reflection, native_binding_reflection. reflexivity.
Qed.


(* Independently check actual source-only event deltas and snapshots against
   the accepted labelled rules, not against a target-generated source trace. *)
Definition p9_source_segment_accepts (start : state) (labels : list offered)
    (final : state) (events : list observation) : bool :=
  match replay_source start labels with
  | Some (actual, seen) =>
      if source_state_dec actual final then
        if observations_dec seen events then true else false
      else false
  | None => false
  end.

Theorem p9_source_segment_reflection : forall start labels final events,
  p9_source_segment_accepts start labels final events = true <->
  source_trace start labels events final.
Proof.
  intros start labels final events.
  rewrite <- p9_source_model_reflection.
  unfold p9_source_segment_accepts.
  destruct (replay_source start labels) as [[actual seen]|].
  - destruct (source_state_dec actual final);
      destruct (observations_dec seen events);
      split; intro H; try discriminate; congruence.
  - split; discriminate.
Qed.

Theorem p9_source_segment_safety : forall start labels final events,
  p9_source_segment_accepts start labels final events = true ->
  canonical_lifecycle start ->
  canonical_lifecycle final /\
  state_next start <= state_next final /\
  (forall x, In x (state_issued start) -> In x (state_issued final)) /\
  (forall x, In x (state_retired start) -> In x (state_retired final)).
Proof.
  intros start labels final events H Hsafe.
  apply p9_source_segment_reflection in H.
  split.
  - eapply reachable_lifecycle_valid; [eapply source_trace_forget; exact H | exact Hsafe].
  - apply p9_source_history_monotone in H. exact H.
Qed.


(* Countermodel to upgrading equality reflection into original-object
   soundness. The accepted private native producer does not supply this
   binding. This is a proof-kernel boundary witness, not a producer bug. *)
Definition p9_unanchored_binding : selected_binding :=
  Binding [100; 101; 99; 108; 58; 115; 116; 101; 118; 101; 46; 103; 101; 116] [105; 110; 115; 116; 58; 112; 104; 97; 115; 101; 49; 46; 115; 116; 101; 118; 101]
    [] [] [66; 108; 111; 98; 80; 114; 111; 118; 105; 100; 101; 114; 46; 114; 101; 97; 100] [] []
    [68; 105; 103; 101; 115; 116; 80; 114; 111; 118; 105; 100; 101; 114; 46; 99; 104; 101; 99; 107] [] [] [].

Theorem p9_unanchored_binding_witness :
  p9_input_accepts p9_original_bytes expected_native
    p9_unanchored_binding p9_unanchored_binding = true /\
  binding_read_occurrence p9_unanchored_binding = [] /\
  binding_digest_occurrence p9_unanchored_binding = [] /\
  binding_blob_interface p9_unanchored_binding = [] /\
  binding_digest_implementation p9_unanchored_binding = [].
Proof. vm_compute. repeat split. Qed.


(* P0/P6: fixed original checked carrier/metadata and independently supplied
   invocation input. The metadata literals are full checked revision bytes,
   not hashes: observed on the independent ordinary bundle/architecture
   path at exact head 6dc26678, run 45885639415. Ordered fields below are
   interface, definition, read ordinal/route, digest ordinal/route.
   The accepted source selector and native Core admission remain separate. *)
Local Open Scope string_scope.
Local Open Scope list_scope.
Definition p9_original_metadata : list name :=
  map nm ["phil.interface.canonical.v1:record{10:parameters=ordered[],8:provides=record{6:fields=ordered[record{6:fields=ordered[],3:tag=atom(4:Unit)}],3:tag=atom(4:some)}}";
    "phil.definition.canonical.v1:record{10:definition=ordered[record{6:fields=ordered[record{6:fields=ordered[record{6:fields=ordered[atom(9:blob_read),ordered[record{6:fields=ordered[atom(9:contentId)],3:tag=atom(8:variable)}]],3:tag=atom(4:call)},ordered[record{4:body=ordered[record{6:fields=ordered[record{6:fields=ordered[atom(14:digestDecision)],3:tag=atom(4:bind)},record{6:fields=ordered[record{6:fields=ordered[atom(5:bytes)],3:tag=atom(8:variable)},atom(9:bytesView),ordered[record{6:fields=ordered[record{6:fields=ordered[atom(12:digest_check),ordered[record{6:fields=ordered[atom(9:contentId)],3:tag=atom(8:variable)},record{6:fields=ordered[atom(9:bytesView)],3:tag=atom(8:variable)}]],3:tag=atom(4:call)}],3:tag=atom(10:expression)}]],3:tag=atom(6:borrow)}],3:tag=atom(3:let)},record{6:fields=ordered[record{6:fields=ordered[record{6:fields=ordered[atom(14:digestDecision)],3:tag=atom(8:variable)},ordered[record{4:body=ordered[record{6:fields=ordered[record{6:fields=ordered[record{6:fields=ordered[atom(5:bytes)],3:tag=atom(8:variable)}],3:tag=atom(7:release)}],3:tag=atom(10:expression)},record{6:fields=ordered[record{6:fields=ordered[],3:tag=atom(4:unit)}],3:tag=atom(6:return)}],7:pattern=record{7:binders=ordered[],5:label=atom(8:accepted)}},record{4:body=ordered[record{6:fields=ordered[record{6:fields=ordered[record{6:fields=ordered[atom(5:bytes)],3:tag=atom(8:variable)}],3:tag=atom(7:release)}],3:tag=atom(10:expression)},record{6:fields=ordered[record{6:fields=ordered[],3:tag=atom(4:unit)}],3:tag=atom(6:return)}],7:pattern=record{7:binders=ordered[atom(6:reason)],5:label=atom(8:rejected)}}]],3:tag=atom(6:decide)}],3:tag=atom(10:expression)}],7:pattern=record{7:binders=ordered[atom(5:bytes)],5:label=atom(5:found)}},record{4:body=ordered[record{6:fields=ordered[record{6:fields=ordered[],3:tag=atom(4:unit)}],3:tag=atom(6:return)}],7:pattern=record{7:binders=ordered[],5:label=atom(9:not-found)}},record{4:body=ordered[record{6:fields=ordered[record{6:fields=ordered[],3:tag=atom(4:unit)}],3:tag=atom(6:return)}],7:pattern=record{7:binders=ordered[atom(6:reason)],5:label=atom(15:storage-failure)}}]],3:tag=atom(6:decide)}],3:tag=atom(10:expression)}],18:interface_revision=atom(161:phil.interface.canonical.v1:record{10:parameters=ordered[],8:provides=record{6:fields=ordered[record{6:fields=ordered[],3:tag=atom(4:Unit)}],3:tag=atom(4:some)}})}";
    "0";
    "statement:0";
    "decide:scrutinee";
    "1";
    "statement:0";
    "arm:0:found";
    "statement:0";
    "borrow:body";
    "statement:0"].

Definition p9_original_binding (content_id : name) : selected_binding :=
  Binding (nm "decl:steve.get") (nm "inst:phase1.steve")
    (map nm ["unit.steve.get"; "2"; "12"; "46"; "unit.steve.get"; "2"; "33"; "67"])
    (map nm ["unit.steve.get"; "5"; "17"; "172"; "unit.steve.get"; "6"; "13"; "219"])
    (nm "BlobProvider.read") (nm "steve.provider.blob.v1")
    (nm "steve.provider.blob.impl.v1")
    (nm "DigestProvider.check") (nm "steve.provider.digest.sha256.v1")
    (nm "steve.provider.digest.sha256.impl.v1") content_id.

Definition p9_anchored_source_accepts (raw : name) (metadata : list name)
    (content_id : name) (actual : selected_binding) : bool :=
  andb (p9_raw_accepts raw)
    (andb (if names_dec metadata p9_original_metadata then true else false)
      (if binding_dec actual (p9_original_binding content_id) then true else false)).

Theorem p9_anchored_source_reflection : forall raw metadata content_id actual,
  p9_anchored_source_accepts raw metadata content_id actual = true <->
  raw = p9_original_bytes /\ metadata = p9_original_metadata /\
  actual = p9_original_binding content_id.
Proof.
  intros. unfold p9_anchored_source_accepts.
  rewrite !Bool.andb_true_iff, p9_raw_reflection.
  destruct (names_dec metadata p9_original_metadata);
    destruct (binding_dec actual (p9_original_binding content_id));
    intuition discriminate.
Qed.

(* This rejects even a self-paired expected/actual value of the old
   unanchored gate. No offered E reply can choose the static anchor. *)
Theorem p9_anchored_rejects_unanchored : forall content_id,
  p9_anchored_source_accepts p9_original_bytes p9_original_metadata
    content_id p9_unanchored_binding = false.
Proof.
  intro content_id.
  destruct (p9_anchored_source_accepts p9_original_bytes p9_original_metadata
    content_id p9_unanchored_binding) eqn:H; [|reflexivity].
  apply p9_anchored_source_reflection in H.
  destruct H as [_ [_ H]].
  apply (f_equal binding_read_occurrence) in H. discriminate.
Qed.

(* The static gate and actual represented typed selector jointly anchor the
   particular checked dynamic path, including exact qualified E, safety,
   and diagnostic erasure. No new native representation law is assumed. *)
Theorem p9_anchored_checked_path : forall raw metadata content_id actual
    input count c e used labels target_events source_events final remaining,
  p9_anchored_source_accepts raw metadata content_id actual = true ->
  selected_native_accepts input = true ->
  p9_checked_path input actual count c e used labels target_events source_events final remaining ->
  canonical_lifecycle (source_projection c) ->
  input = expected_native /\
  core_trace input (p9_original_binding content_id) c e target_events final remaining /\
  e = used ++ remaining /\
  qualified_source_segment input (p9_original_binding content_id)
    (source_projection c) (source_projection final) used labels source_events /\
  erase_diagnostic target_events ++ pending_unit final = pending_unit c ++ source_events /\
  canonical_lifecycle (source_projection final).
Proof.
  intros raw metadata content_id actual input count c e used labels
    target_events source_events final remaining Ha Hi Hpath Hsafe.
  apply p9_anchored_source_reflection in Ha. destruct Ha as [_ [_ Ha]].
  subst actual.
  apply selected_native_reflection in Hi.
  destruct (p9_checked_path_sound _ _ _ _ _ _ _ _ _ _ _ Hpath)
    as [Hcore [He [Hseg Hobs]]].
  split; [exact Hi|]. split; [exact Hcore|]. split; [exact He|].
  split; [exact Hseg|]. split; [exact Hobs|].
  eapply target_trace_preserves_lifecycle; eauto.
Qed.

Print Assumptions p9_anchored_source_reflection.
Print Assumptions p9_anchored_rejects_unanchored.
Print Assumptions p9_anchored_checked_path.

Print Assumptions p9_unanchored_binding_witness.
Print Assumptions p9_source_segment_reflection.
Print Assumptions p9_source_segment_safety.
Print Assumptions p9_source_trace_replay.
Print Assumptions p9_source_model_reflection.
Print Assumptions p9_step_history_monotone.
Print Assumptions p9_source_history_monotone.
Print Assumptions p9_source_replay_safety.
Print Assumptions p9_checked_path_sound.
Print Assumptions p9_checked_path_safety.
Print Assumptions p9_checked_path_rank.
Print Assumptions p9_completed_checked_path.
Print Assumptions p9_raw_reflection.
Print Assumptions p9_input_reflection.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extraction "P9G3OriginalInputKernel.hs" p9_raw_accepts p9_source_segment_accepts p9_anchored_source_accepts.
