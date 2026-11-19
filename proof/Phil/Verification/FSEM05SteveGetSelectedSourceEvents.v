(*
  FSEM-05: selected original-Surface SteveGet transition *definition*.
  This is an independent declarative mathematical counterpart to the bounded
  Haskell selected-source evaluator. The original parser/checker -> this model
  relation and linked provider E authenticity are NOT theorems of this file.
  No SHA, Blob or StablePtr premise is discharged here.
*)
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Module SelectedSteveGetEvents.

Inductive unit_branch : Type :=
| UnitAccepted | UnitRejected | UnitNotFound | UnitStorageFailure.

(* E supplies outcomes/payloads, never owner IDs or serials. BadSource means
   wrong occurrence/qualification/id/view. NoInput is an actual finite prefix. *)
Inductive offered : Type :=
| NoInput
| ReadFound (payload : nat)
| ReadNotFound
| ReadFailure
| DigestAccepted
| DigestRejected
| BadSource.

(* Persistent H consists of next, issued history and retired history.
   Every new invocation inherits the same H. *)
Inductive state : Type :=
| Idle : nat -> list nat -> list nat -> state
| AwaitRead : nat -> list nat -> list nat -> state
| AwaitBorrow : nat -> list nat -> list nat -> nat -> state
| AwaitDigest : nat -> list nat -> list nat -> nat -> nat -> state
| AwaitClose : nat -> list nat -> list nat -> nat -> nat -> bool -> state
| AwaitRelease : nat -> list nat -> list nat -> nat -> nat -> bool -> state
| Done : nat -> list nat -> list nat -> unit_branch -> state.

Inductive verdict : Type :=
| Advanced : state -> verdict
| Waiting : verdict
| Rejected : verdict.

(* Selected executable step: found allocates from H.next; borrow allocates
   the subsequent distinct loan; close and release retire while retaining
   issued history. Other typed read outcomes return Unit without allocation. *)
Definition selected_step_fn (s : state) (e : offered) : verdict :=
  match s, e with
  | Idle n issued retired, NoInput =>
      Advanced (AwaitRead n issued retired)
  | AwaitRead n issued retired, ReadFound _payload =>
      Advanced (AwaitBorrow (S n) (n :: issued) retired n)
  | AwaitRead n issued retired, ReadNotFound =>
      Advanced (Done n issued retired UnitNotFound)
  | AwaitRead n issued retired, ReadFailure =>
      Advanced (Done n issued retired UnitStorageFailure)
  | AwaitRead _ _ _, NoInput => Waiting
  | AwaitBorrow n issued retired owner, NoInput =>
      Advanced (AwaitDigest (S n) (n :: issued) retired owner n)
  | AwaitDigest n issued retired owner loan, DigestAccepted =>
      Advanced (AwaitClose n issued retired owner loan true)
  | AwaitDigest n issued retired owner loan, DigestRejected =>
      Advanced (AwaitClose n issued retired owner loan false)
  | AwaitDigest _ _ _ _ _, NoInput => Waiting
  | AwaitClose n issued retired owner loan decision, NoInput =>
      Advanced (AwaitRelease n issued (loan :: retired) owner loan decision)
  | AwaitRelease n issued retired owner _loan decision, NoInput =>
      Advanced (Done n issued (owner :: retired)
        (if decision then UnitAccepted else UnitRejected))
  | Done n issued retired _, NoInput =>
      Advanced (Idle n issued retired)
  | _, _ => Rejected
  end.

(* Independent declarative rule cases; no definition by equality to
   selected_step_fn, so agreement is a genuine closed case analysis. *)
Inductive selected_source_step : state -> offered -> state -> Prop :=
| RuleStart : forall n issued retired,
    selected_source_step (Idle n issued retired) NoInput
      (AwaitRead n issued retired)
| RuleFound : forall n issued retired payload,
    selected_source_step (AwaitRead n issued retired) (ReadFound payload)
      (AwaitBorrow (S n) (n :: issued) retired n)
| RuleNotFound : forall n issued retired,
    selected_source_step (AwaitRead n issued retired) ReadNotFound
      (Done n issued retired UnitNotFound)
| RuleStorageFailure : forall n issued retired,
    selected_source_step (AwaitRead n issued retired) ReadFailure
      (Done n issued retired UnitStorageFailure)
| RuleBorrow : forall n issued retired owner,
    selected_source_step (AwaitBorrow n issued retired owner) NoInput
      (AwaitDigest (S n) (n :: issued) retired owner n)
| RuleDigestAccepted : forall n issued retired owner loan,
    selected_source_step (AwaitDigest n issued retired owner loan) DigestAccepted
      (AwaitClose n issued retired owner loan true)
| RuleDigestRejected : forall n issued retired owner loan,
    selected_source_step (AwaitDigest n issued retired owner loan) DigestRejected
      (AwaitClose n issued retired owner loan false)
| RuleClose : forall n issued retired owner loan decision,
    selected_source_step (AwaitClose n issued retired owner loan decision) NoInput
      (AwaitRelease n issued (loan :: retired) owner loan decision)
| RuleRelease : forall n issued retired owner loan decision,
    selected_source_step
      (AwaitRelease n issued retired owner loan decision) NoInput
      (Done n issued (owner :: retired)
        (if decision then UnitAccepted else UnitRejected))
| RuleNextInvocation : forall n issued retired outcome,
    selected_source_step (Done n issued retired outcome) NoInput
      (Idle n issued retired).

Theorem selected_step_sound :
  forall s e next,
    selected_step_fn s e = Advanced next ->
    selected_source_step s e next.
Proof.
  intros s e next H.
  destruct s; destruct e; simpl in H; try discriminate;
    inversion H; subst; constructor.
Qed.

Theorem selected_step_coverage :
  forall s e next,
    selected_source_step s e next ->
    selected_step_fn s e = Advanced next.
Proof.
  intros s e next H; inversion H; subst; reflexivity.
Qed.

Theorem selected_step_deterministic :
  forall s e a b,
    selected_source_step s e a ->
    selected_source_step s e b -> a = b.
Proof.
  intros s e a b Ha Hb.
  apply selected_step_coverage in Ha.
  apply selected_step_coverage in Hb.
  congruence.
Qed.

Theorem no_read_is_waiting :
  forall n issued retired,
    selected_step_fn (AwaitRead n issued retired) NoInput = Waiting.
Proof. reflexivity. Qed.

Theorem no_digest_is_waiting :
  forall n issued retired owner loan,
    selected_step_fn (AwaitDigest n issued retired owner loan) NoInput = Waiting.
Proof. reflexivity. Qed.

Theorem wrong_qualified_event_rejected :
  forall s, selected_step_fn s BadSource = Rejected.
Proof. intros []; reflexivity. Qed.

Theorem nonfound_issues_no_origin :
  forall n issued retired,
    selected_step_fn (AwaitRead n issued retired) ReadNotFound =
      Advanced (Done n issued retired UnitNotFound) /\
    selected_step_fn (AwaitRead n issued retired) ReadFailure =
      Advanced (Done n issued retired UnitStorageFailure).
Proof. intros; split; reflexivity. Qed.

Theorem owner_and_loan_origins_distinct :
  forall n issued retired payload,
    selected_source_step (AwaitRead n issued retired) (ReadFound payload)
      (AwaitBorrow (S n) (n :: issued) retired n) /\
    selected_source_step (AwaitBorrow (S n) (n :: issued) retired n)
      NoInput (AwaitDigest (S (S n)) ((S n) :: n :: issued) retired n (S n))
    /\ n <> S n.
Proof.
  intros; repeat split; try constructor; lia.
Qed.

Lemma fresh_not_in_issued :
  forall n issued,
    Forall (fun k => k < n) issued -> ~ In n issued.
Proof.
  intros n issued H.
  induction H as [|k rest Hlt Hrest IH].
  - simpl; intuition.
  - simpl. intros [Heq | Hin].
    + subst; lia.
    + apply IH; assumption.
Qed.

Lemma issue_preserves_history_bound :
  forall n issued,
    Forall (fun k => k < n) issued ->
    Forall (fun k => k < S n) (n :: issued).
Proof.
  intros n issued H.
  constructor.
  - lia.
  - induction H as [|k rest Hlt Hrest IH].
    + constructor.
    + constructor; [lia|assumption].
Qed.

Lemma issue_preserves_no_duplicates :
  forall n issued,
    Forall (fun k => k < n) issued ->
    NoDup issued -> NoDup (n :: issued).
Proof.
  intros n issued Hbound Hnodup.
  constructor.
  - now apply fresh_not_in_issued.
  - assumption.
Qed.

(* Ledger freshness holds for every reachable selected transition, not
   just the exhibited two-run witness. The cursor is H-owned state and is
   carried unchanged or incremented; issued history is never cleared. *)
Definition state_next (s : state) : nat :=
  match s with
  | Idle n _ _ => n
  | AwaitRead n _ _ => n
  | AwaitBorrow n _ _ _ => n
  | AwaitDigest n _ _ _ _ => n
  | AwaitClose n _ _ _ _ _ => n
  | AwaitRelease n _ _ _ _ _ => n
  | Done n _ _ _ => n
  end.

Definition state_issued (s : state) : list nat :=
  match s with
  | Idle _ issued _ => issued
  | AwaitRead _ issued _ => issued
  | AwaitBorrow _ issued _ _ => issued
  | AwaitDigest _ issued _ _ _ => issued
  | AwaitClose _ issued _ _ _ _ => issued
  | AwaitRelease _ issued _ _ _ _ => issued
  | Done _ issued _ _ => issued
  end.

Definition valid_issue_ledger (s : state) : Prop :=
  Forall (fun k => k < state_next s) (state_issued s)
    /\ NoDup (state_issued s).

Theorem step_counter_monotone :
  forall s event next,
    selected_source_step s event next ->
    state_next s <= state_next next.
Proof.
  intros s event next H.
  inversion H; subst; simpl; lia.
Qed.

Theorem selected_step_preserves_issue_ledger :
  forall s event next,
    valid_issue_ledger s ->
    selected_source_step s event next ->
    valid_issue_ledger next.
Proof.
  intros s event next [Hbound Hnodup] Hstep.
  unfold valid_issue_ledger.
  inversion Hstep; subst; simpl in *;
    try (split; assumption);
    (split;
      [eapply issue_preserves_history_bound; eassumption
      |eapply issue_preserves_no_duplicates; eassumption]).
Qed.

Inductive selected_steps : state -> state -> Prop :=
| StepsRefl : forall s, selected_steps s s
| StepsNext : forall s middle final event,
    selected_source_step s event middle ->
    selected_steps middle final ->
    selected_steps s final.

Theorem reachable_ledger_valid :
  forall s target,
    selected_steps s target ->
    valid_issue_ledger s ->
    valid_issue_ledger target.
Proof.
  intros s target Hsteps; induction Hsteps; intros Hvalid.
  - exact Hvalid.
  - apply IHHsteps.
    eapply selected_step_preserves_issue_ledger; eauto.
Qed.

Theorem fresh_issued_origin_in_every_reachable_state :
  forall target,
    selected_steps (Idle 0 [] []) target ->
    ~ In (state_next target) (state_issued target).
Proof.
  intros target Hsteps.
  apply fresh_not_in_issued.
  assert (Hinitial : valid_issue_ledger (Idle 0 [] [])).
  { unfold valid_issue_ledger; simpl; split; constructor. }
  pose proof (reachable_ledger_valid _ _ Hsteps Hinitial)
    as [Hbound _].
  exact Hbound.
Qed.

Theorem every_reachable_found_chooses_fresh_owner :
  forall n issued retired payload,
    selected_steps (Idle 0 [] []) (AwaitRead n issued retired) ->
    ~ In n issued
      /\ selected_source_step (AwaitRead n issued retired)
          (ReadFound payload)
          (AwaitBorrow (S n) (n :: issued) retired n).
Proof.
  intros n issued retired payload Hsteps; split.
  - apply (fresh_issued_origin_in_every_reachable_state
      (AwaitRead n issued retired)); assumption.
  - constructor.
Qed.

(* A canonical, phase-sensitive RESOURCE invariant. This is strictly
   stronger than issuance freshness: it states which issued origins remain
   live (issued but not retired) at each selected source phase. Unreachable
   malformed states may satisfy valid_issue_ledger without satisfying this. *)
Definition state_retired (s : state) : list nat :=
  match s with
  | Idle _ _ retired => retired
  | AwaitRead _ _ retired => retired
  | AwaitBorrow _ _ retired _ => retired
  | AwaitDigest _ _ retired _ _ => retired
  | AwaitClose _ _ retired _ _ _ => retired
  | AwaitRelease _ _ retired _ _ _ => retired
  | Done _ _ retired _ => retired
  end.

Definition live_issued (issued retired : list nat) (origin : nat) : Prop :=
  In origin issued /\ ~ In origin retired.

Definition phase_lifetime (s : state) : Prop :=
  match s with
  | Idle _ issued retired =>
      forall k, ~ live_issued issued retired k
  | AwaitRead _ issued retired =>
      forall k, ~ live_issued issued retired k
  | AwaitBorrow _ issued retired owner =>
      live_issued issued retired owner /\
      (forall k, live_issued issued retired k -> k = owner)
  | AwaitDigest _ issued retired owner loan =>
      owner <> loan /\ live_issued issued retired owner /\
      live_issued issued retired loan /\
      (forall k, live_issued issued retired k -> k = owner \/ k = loan)
  | AwaitClose _ issued retired owner loan _ =>
      owner <> loan /\ live_issued issued retired owner /\
      live_issued issued retired loan /\
      (forall k, live_issued issued retired k -> k = owner \/ k = loan)
  | AwaitRelease _ issued retired owner loan _ =>
      owner <> loan /\ In loan retired /\
      live_issued issued retired owner /\
      (forall k, live_issued issued retired k -> k = owner)
  | Done _ issued retired _ =>
      forall k, ~ live_issued issued retired k
  end.

Definition canonical_lifecycle (s : state) : Prop :=
  valid_issue_ledger s /\
  NoDup (state_retired s) /\
  (forall k, In k (state_retired s) -> In k (state_issued s)) /\
  phase_lifetime s.

Lemma live_after_issue :
  forall n issued retired k,
    ~ In n retired ->
    (live_issued (n :: issued) retired k
      <-> k = n \/ live_issued issued retired k).
Proof.
  intros n issued retired k Hfresh.
  unfold live_issued; simpl.
  split.
  - intros [[Heq | Hin] Hnot].
    + now left.
    + right; auto.
  - intros [Heq | [Hin Hnot]].
    + subst; split; [now left | exact Hfresh].
    + split; [now right | exact Hnot].
Qed.

Lemma live_after_retire :
  forall issued retired loan k,
    live_issued issued (loan :: retired) k
      <-> live_issued issued retired k /\ k <> loan.
Proof.
  intros issued retired loan k.
  unfold live_issued; simpl.
  split.
  - intros [Hin Hnot].
    split.
    + split; [exact Hin | intro Hr; apply Hnot; right; exact Hr].
    + intro Heq; apply Hnot; left; symmetry; exact Heq.
  - intros [[Hin Hnot] Hneq].
    split; [exact Hin |].
    intros [Heq | Hr].
    + apply Hneq; symmetry; exact Heq.
    + apply Hnot; exact Hr.
Qed.

Lemma fresh_not_retired :
  forall n issued retired,
    Forall (fun k => k < n) issued ->
    (forall k, In k retired -> In k issued) ->
    ~ In n retired.
Proof.
  intros n issued retired Hbound Hsubset Hret.
  apply (fresh_not_in_issued n issued Hbound).
  apply Hsubset; exact Hret.
Qed.

Theorem canonical_lifecycle_step :
  forall s event next,
    canonical_lifecycle s ->
    selected_source_step s event next ->
    canonical_lifecycle next.
Proof.
  intros s event next [Hissued [HnodupR [Hsubset Hphase]]] Hstep.
  assert (HissuedNext : valid_issue_ledger next).
  { eapply selected_step_preserves_issue_ledger; eauto. }
  split; [exact HissuedNext |].
  destruct Hstep; simpl in *.
  - (* Idle -> AwaitRead: same empty live set. *)
    repeat split; assumption.
  - (* Found: the one new owner is the sole live origin. *)
    destruct Hissued as [Hbound _].
    assert (HfreshR : ~ In n retired).
    { eapply fresh_not_retired; eauto. }
    split; [exact HnodupR |].
    split.
    + intros k Hk; right; apply Hsubset; exact Hk.
    + split.
      * apply (proj2 (live_after_issue n issued retired n HfreshR)).
        left; reflexivity.
      * intros k Hlive.
        apply (proj1 (live_after_issue n issued retired k HfreshR))
          in Hlive.
        destruct Hlive as [Heq | Hold].
        -- exact Heq.
        -- exfalso; apply (Hphase k); exact Hold.
  - (* NotFound: no new owner and no live resource. *)
    repeat split; assumption.
  - (* StorageFailure: likewise. *)
    repeat split; assumption.
  - (* Borrow: the new loan differs from owner, both alone live. *)
    destruct Hissued as [Hbound _].
    assert (HfreshI : ~ In n issued).
    { apply fresh_not_in_issued; exact Hbound. }
    assert (HfreshR : ~ In n retired).
    { eapply fresh_not_retired; eauto. }
    destruct Hphase as [Howner Honly].
    assert (Hdistinct : owner <> n).
    { intro Heq; subst; apply HfreshI; exact (proj1 Howner). }
    split; [exact HnodupR |].
    split.
    + intros k Hk; right; apply Hsubset; exact Hk.
    + split; [exact Hdistinct |].
      split.
      * apply (proj2 (live_after_issue n issued retired owner HfreshR)).
        right; exact Howner.
      * split.
        -- apply (proj2 (live_after_issue n issued retired n HfreshR)).
           left; reflexivity.
        -- intros k Hlive.
           apply (proj1 (live_after_issue n issued retired k HfreshR))
             in Hlive.
           destruct Hlive as [Heq | Hold].
           ++ right; exact Heq.
           ++ left; apply Honly; exact Hold.
  - (* Digest accepted: preserve the entire phase lifetime proposition. *)
    split; [exact HnodupR |].
    split; [exact Hsubset | exact Hphase].
  - (* Digest rejected: preserve the same two live identities. *)
    split; [exact HnodupR |].
    split; [exact Hsubset | exact Hphase].
  - (* Close: loan retired once, owner is the only survivor. *)
    destruct Hphase as [Hdistinct [Howner [Hloan Honly]]].
    split.
    + constructor; [exact (proj2 Hloan) | exact HnodupR].
    + split.
      * intros k [Heq | Hk].
        -- subst; exact (proj1 Hloan).
        -- apply Hsubset; exact Hk.
      * split; [exact Hdistinct |].
        split; [now left |].
        split.
        -- apply (proj2 (live_after_retire issued retired loan owner)).
           split; [exact Howner | exact Hdistinct].
        -- intros k Hlive.
           apply (proj1 (live_after_retire issued retired loan k))
             in Hlive.
           destruct Hlive as [Hold Hneq].
           destruct (Honly k Hold) as [Heq | Heq].
           ++ exact Heq.
           ++ exfalso; apply Hneq; exact Heq.
  - (* Release: owner retired exactly once; no live resource at Unit. *)
    destruct Hphase as [Hdistinct [HloanRet [Howner Honly]]].
    split.
    + constructor; [exact (proj2 Howner) | exact HnodupR].
    + split.
      * intros k [Heq | Hk].
        -- subst; exact (proj1 Howner).
        -- apply Hsubset; exact Hk.
      * intros k Hlive.
        apply (proj1 (live_after_retire issued retired owner k))
          in Hlive.
        destruct Hlive as [Hold Hneq].
        apply Hneq; apply Honly; exact Hold.
  - (* Completed Unit -> idle: no live resources are resurrected. *)
    repeat split; assumption.
Qed.

Theorem reachable_lifecycle_valid :
  forall s target,
    selected_steps s target ->
    canonical_lifecycle s ->
    canonical_lifecycle target.
Proof.
  intros s target Hsteps.
  induction Hsteps; intros Hvalid.
  - exact Hvalid.
  - apply IHHsteps.
    eapply canonical_lifecycle_step; eauto.
Qed.

Theorem canonical_lifecycle_reachable :
  forall target,
    selected_steps (Idle 0 [] []) target ->
    canonical_lifecycle target.
Proof.
  intros target Hsteps.
  eapply reachable_lifecycle_valid; [exact Hsteps |].
  unfold canonical_lifecycle, valid_issue_ledger.
  simpl; repeat split; try constructor.
  - intros k H; inversion H.
  - intros k [H _]; inversion H.
Qed.

Theorem reachable_digest_has_live_exact_owner_and_loan :
  forall n issued retired owner loan,
    selected_steps (Idle 0 [] []) (AwaitDigest n issued retired owner loan) ->
    owner <> loan /\ live_issued issued retired owner /\
      live_issued issued retired loan.
Proof.
  intros n issued retired owner loan Hreach.
  pose proof (canonical_lifecycle_reachable _ Hreach)
    as [_ [_ [_ Hphase]]].
  destruct Hphase as [Hdistinct [Howner [Hloan _]]].
  split; [exact Hdistinct |].
  split; [exact Howner | exact Hloan].
Qed.

Theorem reachable_close_has_live_loan :
  forall n issued retired owner loan decision,
    selected_steps (Idle 0 [] [])
      (AwaitClose n issued retired owner loan decision) ->
    selected_source_step
      (AwaitClose n issued retired owner loan decision) NoInput
      (AwaitRelease n issued (loan :: retired) owner loan decision)
    /\ owner <> loan /\ live_issued issued retired owner /\
      live_issued issued retired loan /\ ~ In loan retired.
Proof.
  intros n issued retired owner loan decision Hreach.
  pose proof (canonical_lifecycle_reachable _ Hreach)
    as [_ [_ [_ Hphase]]].
  destruct Hphase as [Hdistinct [Howner [Hloan _]]].
  split; [constructor |].
  split; [exact Hdistinct |].
  split; [exact Howner |].
  split; [exact Hloan | exact (proj2 Hloan)].
Qed.

Theorem reachable_release_is_exactly_once :
  forall n issued retired owner loan decision,
    selected_steps (Idle 0 [] [])
      (AwaitRelease n issued retired owner loan decision) ->
    selected_source_step
      (AwaitRelease n issued retired owner loan decision) NoInput
      (Done n issued (owner :: retired)
        (if decision then UnitAccepted else UnitRejected))
    /\ In loan retired /\ ~ In owner retired
    /\ NoDup (owner :: retired).
Proof.
  intros n issued retired owner loan decision Hreach.
  pose proof (canonical_lifecycle_reachable _ Hreach)
    as [_ [HnodupR [_ Hphase]]].
  destruct Hphase as [_ [Hloan [Howner _]]].
  split.
  - constructor.
  - split; [exact Hloan |].
    split; [exact (proj2 Howner) |].
    constructor; [exact (proj2 Howner) | exact HnodupR].
Qed.

Theorem reachable_unit_has_no_live_resource :
  forall n issued retired outcome,
    selected_steps (Idle 0 [] []) (Done n issued retired outcome) ->
    forall k, ~ live_issued issued retired k.
Proof.
  intros n issued retired outcome Hreach.
  pose proof (canonical_lifecycle_reachable _ Hreach)
    as [_ [_ [_ Hphase]]].
  exact Hphase.
Qed.

(* Selected request semantics are defined at state entry, independent of
   whether the projection has yet recorded a completed provider event.
   NoInput at AwaitRead/AwaitDigest preserves their exact pending state. *)
Theorem waiting_preserves_pending_request :
  forall n issued retired owner loan,
    selected_step_fn (AwaitRead n issued retired) NoInput = Waiting
    /\ selected_step_fn
      (AwaitDigest n issued retired owner loan) NoInput = Waiting.
Proof. intros; split; reflexivity. Qed.

(* A consecutive complete accepted first invocation preserves history
   and the same byte payload cannot cause a second owner-origin alias. *)
Theorem two_identical_found_payloads_fresh :
  forall n payload,
    let first_owner := n in
    let first_loan := S n in
    let second_owner := S (S n) in
      selected_source_step (AwaitRead n [] []) (ReadFound payload)
        (AwaitBorrow (S n) [first_owner] [] first_owner)
      /\ selected_source_step
        (AwaitBorrow (S n) [first_owner] [] first_owner) NoInput
        (AwaitDigest (S (S n)) [first_loan; first_owner] []
          first_owner first_loan)
      /\ selected_source_step
        (AwaitDigest (S (S n)) [first_loan; first_owner] []
          first_owner first_loan) DigestAccepted
        (AwaitClose (S (S n)) [first_loan; first_owner] []
          first_owner first_loan true)
      /\ selected_source_step
        (AwaitClose (S (S n)) [first_loan; first_owner] []
          first_owner first_loan true) NoInput
        (AwaitRelease (S (S n)) [first_loan; first_owner] [first_loan]
          first_owner first_loan true)
      /\ selected_source_step
        (AwaitRelease (S (S n)) [first_loan; first_owner] [first_loan]
          first_owner first_loan true) NoInput
        (Done (S (S n)) [first_loan; first_owner]
          [first_owner; first_loan] UnitAccepted)
      /\ selected_source_step
        (Done (S (S n)) [first_loan; first_owner]
          [first_owner; first_loan] UnitAccepted) NoInput
        (Idle (S (S n)) [first_loan; first_owner]
          [first_owner; first_loan])
      /\ selected_source_step
        (Idle (S (S n)) [first_loan; first_owner]
          [first_owner; first_loan]) NoInput
        (AwaitRead (S (S n)) [first_loan; first_owner]
          [first_owner; first_loan])
      /\ selected_source_step
        (AwaitRead (S (S n)) [first_loan; first_owner]
          [first_owner; first_loan]) (ReadFound payload)
        (AwaitBorrow (S second_owner)
          [second_owner; first_loan; first_owner]
          [first_owner; first_loan] second_owner)
      /\ first_owner <> second_owner
      /\ first_loan <> second_owner.
Proof.
  intros n payload; simpl.
  repeat split; try constructor; lia.
Qed.

(* Fuel represents bounded interpreter execution, not fairness or fatality. *)
Inductive fuel_result : Type :=
| FuelComplete (outcome : unit_branch)
| FuelWaiting (paused : state)
| FuelInputPrefixEnded (paused : state)
| FuelRejected
| FuelExhausted.

Fixpoint run_fuel (fuel : nat) (s : state) (inputs : list offered)
  : fuel_result :=
  match s with
  | Done _ _ _ outcome => FuelComplete outcome
  | _ =>
    match fuel with
    | O => FuelExhausted
    | S rest =>
      match inputs with
      | [] => FuelInputPrefixEnded s
      | next :: tail =>
        match selected_step_fn s next with
        | Advanced nextState => run_fuel rest nextState tail
        | Waiting => FuelWaiting s
        | Rejected => FuelRejected
        end
      end
    end
  end.

Theorem finite_wait_is_not_rejection :
  forall n issued retired fuel,
    run_fuel (S fuel) (AwaitRead n issued retired) [NoInput] =
      FuelWaiting (AwaitRead n issued retired).
Proof. reflexivity. Qed.

Theorem out_of_fuel_is_not_rejection :
  forall n issued retired,
    run_fuel 0 (AwaitRead n issued retired) [ReadNotFound] =
      FuelExhausted.
Proof. reflexivity. Qed.

Theorem empty_scheduler_prefix_is_not_provider_wait :
  forall n issued retired owner,
    run_fuel 1 (AwaitBorrow n issued retired owner) [] =
      FuelInputPrefixEnded (AwaitBorrow n issued retired owner).
Proof. reflexivity. Qed.

Theorem empty_digest_prefix_is_not_provider_wait :
  forall n issued retired owner loan,
    run_fuel 1 (AwaitDigest n issued retired owner loan) [] =
      FuelInputPrefixEnded (AwaitDigest n issued retired owner loan).
Proof. reflexivity. Qed.

End SelectedSteveGetEvents.

Print Assumptions SelectedSteveGetEvents.selected_step_sound.
Print Assumptions SelectedSteveGetEvents.selected_step_coverage.
Print Assumptions SelectedSteveGetEvents.selected_step_deterministic.
Print Assumptions SelectedSteveGetEvents.two_identical_found_payloads_fresh.
Print Assumptions SelectedSteveGetEvents.selected_step_preserves_issue_ledger.
Print Assumptions SelectedSteveGetEvents.fresh_issued_origin_in_every_reachable_state.
Print Assumptions SelectedSteveGetEvents.every_reachable_found_chooses_fresh_owner.
Print Assumptions SelectedSteveGetEvents.issue_preserves_no_duplicates.
Print Assumptions SelectedSteveGetEvents.nonfound_issues_no_origin.
Print Assumptions SelectedSteveGetEvents.finite_wait_is_not_rejection.
Print Assumptions SelectedSteveGetEvents.out_of_fuel_is_not_rejection.
Print Assumptions SelectedSteveGetEvents.canonical_lifecycle_step.
Print Assumptions SelectedSteveGetEvents.canonical_lifecycle_reachable.
Print Assumptions SelectedSteveGetEvents.reachable_digest_has_live_exact_owner_and_loan.
Print Assumptions SelectedSteveGetEvents.reachable_close_has_live_loan.
Print Assumptions SelectedSteveGetEvents.reachable_release_is_exactly_once.
Print Assumptions SelectedSteveGetEvents.reachable_unit_has_no_live_resource.
Print Assumptions SelectedSteveGetEvents.waiting_preserves_pending_request.
Print Assumptions SelectedSteveGetEvents.empty_scheduler_prefix_is_not_provider_wait.
Print Assumptions SelectedSteveGetEvents.empty_digest_prefix_is_not_provider_wait.
