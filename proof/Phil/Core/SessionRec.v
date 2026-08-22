From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.

From Phil.Core Require Import Syntax.

Open Scope string_scope.

(*
  Proof-oriented mirror of Phil.Core.Session.exposeSessionHead.

  Haskell can express the seen-set loop directly. Rocq needs structurally
  evident termination, so we give the mirror explicit fuel derived from the
  finite set of recursion binder names in the initial session. The proof below
  establishes that substitution cannot invent recursion binders, every fresh
  unfolding strictly grows the seen set, and therefore the derived fuel can
  never be exhausted.

  Message Ty values are opaque and ignored here: exposeSessionHead never
  inspects a message type, and substitution inside such types cannot create a
  new top-level session head during this operation.
*)

Fixpoint substituteSessionVar (target : Name) (replacement session : Session) : Session :=
  match session with
  | Send binder messageTy continuation =>
      Send binder messageTy (substituteSessionVar target replacement continuation)
  | Receive binder messageTy continuation =>
      Receive binder messageTy (substituteSessionVar target replacement continuation)
  | Select branches => Select (substituteBranches target replacement branches)
  | Offer branches => Offer (substituteBranches target replacement branches)
  | End outcome => End outcome
  | Rec recursionName body =>
      if String.eqb recursionName target then
        Rec recursionName body
      else
        Rec recursionName (substituteSessionVar target replacement body)
  | SessionVar variable =>
      if String.eqb variable target then replacement else SessionVar variable
  end
with substituteBranches (target : Name) (replacement : Session) (branches : Branches) : Branches :=
  match branches with
  | BNil => BNil
  | BCons label payload continuation rest =>
      BCons label payload
        (substituteSessionVar target replacement continuation)
        (substituteBranches target replacement rest)
  end.

Fixpoint recursionNames (session : Session) : list Name :=
  match session with
  | Send _ _ continuation => recursionNames continuation
  | Receive _ _ continuation => recursionNames continuation
  | Select branches => branchRecursionNames branches
  | Offer branches => branchRecursionNames branches
  | End _ => []
  | Rec recursionName body => recursionName :: recursionNames body
  | SessionVar _ => []
  end
with branchRecursionNames (branches : Branches) : list Name :=
  match branches with
  | BNil => []
  | BCons _ _ continuation rest =>
      recursionNames continuation ++ branchRecursionNames rest
  end.

Lemma substitution_does_not_invent_recursion_names :
  (forall session target replacement name,
    In name (recursionNames (substituteSessionVar target replacement session)) ->
    In name (recursionNames session) \/ In name (recursionNames replacement)) /\
  (forall branches target replacement name,
    In name (branchRecursionNames (substituteBranches target replacement branches)) ->
    In name (branchRecursionNames branches) \/ In name (recursionNames replacement)).
Proof.
  apply Session_Branches_mutind.
  - intros binder messageTy continuation IH target replacement name Hin.
    simpl in *. apply IH in Hin. exact Hin.
  - intros binder messageTy continuation IH target replacement name Hin.
    simpl in *. apply IH in Hin. exact Hin.
  - intros branches IH target replacement name Hin.
    simpl in *. apply IH in Hin. exact Hin.
  - intros branches IH target replacement name Hin.
    simpl in *. apply IH in Hin. exact Hin.
  - intros outcome target replacement name Hin. simpl in Hin. contradiction.
  - intros recursionName body IH target replacement name Hin.
    destruct (String.eqb recursionName target) eqn:Heq.
    + assert (Hsub :
        substituteSessionVar target replacement (Rec recursionName body) =
          Rec recursionName body).
      { cbn [substituteSessionVar]. rewrite Heq. reflexivity. }
      rewrite Hsub in Hin.
      simpl in Hin.
      left. exact Hin.
    + assert (Hsub :
        substituteSessionVar target replacement (Rec recursionName body) =
          Rec recursionName (substituteSessionVar target replacement body)).
      { cbn [substituteSessionVar]. rewrite Heq. reflexivity. }
      rewrite Hsub in Hin.
      simpl in Hin.
      destruct Hin as [Hname | Hbody].
      * left. simpl. left. exact Hname.
      * apply IH in Hbody.
        destruct Hbody as [Hbody | Hreplacement].
        -- left. simpl. right. exact Hbody.
        -- right. exact Hreplacement.
  - intros variable target replacement name Hin.
    destruct (String.eqb variable target) eqn:Heq.
    + assert (Hsub :
        substituteSessionVar target replacement (SessionVar variable) = replacement).
      { cbn [substituteSessionVar]. rewrite Heq. reflexivity. }
      rewrite Hsub in Hin.
      right. exact Hin.
    + assert (Hsub :
        substituteSessionVar target replacement (SessionVar variable) = SessionVar variable).
      { cbn [substituteSessionVar]. rewrite Heq. reflexivity. }
      rewrite Hsub in Hin.
      simpl in Hin. contradiction.
  - intros target replacement name Hin. simpl in Hin. contradiction.
  - intros label payload continuation IHcontinuation rest IHrest target replacement name Hin.
    simpl in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hcontinuation | Hrest].
    + apply IHcontinuation in Hcontinuation.
      destruct Hcontinuation as [Hcontinuation | Hreplacement].
      * left. simpl. apply in_or_app. left. exact Hcontinuation.
      * right. exact Hreplacement.
    + apply IHrest in Hrest.
      destruct Hrest as [Hrest | Hreplacement].
      * left. simpl. apply in_or_app. right. exact Hrest.
      * right. exact Hreplacement.
Qed.

Inductive ExposureStep
  : list Name -> Session -> list Name -> Session -> Prop :=
| Exposure_unfold :
    forall seen recursionName body,
      ~ In recursionName seen ->
      ExposureStep
        seen
        (Rec recursionName body)
        (recursionName :: seen)
        (substituteSessionVar recursionName (Rec recursionName body) body).

Lemma exposure_step_names_subset :
  forall seen session nextSeen nextSession,
    ExposureStep seen session nextSeen nextSession ->
    incl (recursionNames nextSession) (recursionNames session).
Proof.
  intros seen session nextSeen nextSession Hstep.
  inversion Hstep as [seen' recursionName body Hfresh]; subst.
  unfold incl.
  intros name Hin.
  pose proof (proj1 substitution_does_not_invent_recursion_names
    body recursionName (Rec recursionName body) name Hin) as Hnames.
  destruct Hnames as [Hbody | Hreplacement].
  - simpl. right. exact Hbody.
  - exact Hreplacement.
Qed.

Inductive ExposureTrace
  : list Name -> Session -> list Name -> Session -> nat -> Prop :=
| ExposureTrace_refl :
    forall seen session,
      ExposureTrace seen session seen session 0
| ExposureTrace_step :
    forall seen session nextSeen nextSession finalSeen finalSession steps,
      ExposureStep seen session nextSeen nextSession ->
      ExposureTrace nextSeen nextSession finalSeen finalSession steps ->
      ExposureTrace seen session finalSeen finalSession (S steps).

Lemma exposure_trace_invariants :
  forall seen session finalSeen finalSession steps pool,
    ExposureTrace seen session finalSeen finalSession steps ->
    NoDup seen ->
    incl seen pool ->
    incl (recursionNames session) pool ->
    NoDup finalSeen /\
    incl finalSeen pool /\
    incl (recursionNames finalSession) pool /\
    length finalSeen = length seen + steps.
Proof.
  intros seen session finalSeen finalSession steps pool Htrace.
  induction Htrace as
    [ seen session
    | seen session nextSeen nextSession finalSeen finalSession steps Hstep Htrace IH ];
    intros Hnodup HseenPool HnamesPool.
  - repeat split; try assumption.
    lia.
  - inversion Hstep as [seen' recursionName body Hfresh]; subst.
    assert (HnamePool : In recursionName pool).
    { apply HnamesPool. simpl. left. reflexivity. }
    assert (HnextNoDup : NoDup (recursionName :: seen)).
    { constructor; assumption. }
    assert (HnextSeenPool : incl (recursionName :: seen) pool).
    { unfold incl. intros name Hin.
      simpl in Hin. destruct Hin as [Heq | Hin].
      - subst name. exact HnamePool.
      - apply HseenPool. exact Hin. }
    assert (HnextNamesPool :
      incl
        (recursionNames
          (substituteSessionVar recursionName (Rec recursionName body) body))
        pool).
    { unfold incl. intros name Hin.
      apply HnamesPool.
      eapply exposure_step_names_subset.
      - constructor. exact Hfresh.
      - exact Hin. }
    specialize (IH HnextNoDup HnextSeenPool HnextNamesPool).
    destruct IH as [HfinalNoDup [HfinalPool [HfinalNames Hlength]]].
    repeat split; try assumption.
    simpl in Hlength. lia.
Qed.

Definition recursionPool (session : Session) : list Name :=
  nodup string_dec (recursionNames session).

Lemma initial_names_in_pool :
  forall session,
    incl (recursionNames session) (recursionPool session).
Proof.
  intros session.
  unfold recursionPool, incl.
  intros name Hin.
  apply (proj2 (nodup_In string_dec (recursionNames session) name)).
  exact Hin.
Qed.

Lemma exposure_trace_bounded :
  forall session finalSeen finalSession steps,
    ExposureTrace [] session finalSeen finalSession steps ->
    steps <= length (recursionPool session).
Proof.
  intros session finalSeen finalSession steps Htrace.
  pose proof
    (exposure_trace_invariants
      [] session finalSeen finalSession steps (recursionPool session)
      Htrace
      (NoDup_nil Name)
      (fun name Hin => False_rect _ Hin)
      (initial_names_in_pool session))
    as [Hnodup [Hpool [_ Hlength]]].
  pose proof (NoDup_nodup string_dec (recursionNames session)) as HpoolNoDup.
  pose proof (NoDup_incl_length Hnodup Hpool) as Hbound.
  simpl in Hlength.
  lia.
Qed.

Inductive ExposureResult : Type :=
| ExposedHead : Session -> ExposureResult
| UnguardedRecursionResult : Name -> ExposureResult
| UnboundSessionVariableResult : Name -> ExposureResult
| ExposureFuelExhausted : ExposureResult.

Fixpoint exposeWithFuel
  (fuel : nat) (seen : list Name) (session : Session) : ExposureResult :=
  match fuel with
  | 0 => ExposureFuelExhausted
  | S fuel' =>
      match session with
      | Rec recursionName body =>
          if in_dec string_dec recursionName seen then
            UnguardedRecursionResult recursionName
          else
            exposeWithFuel
              fuel'
              (recursionName :: seen)
              (substituteSessionVar recursionName session body)
      | SessionVar variable => UnboundSessionVariableResult variable
      | headSession => ExposedHead headSession
      end
  end.

Definition exposeSessionHeadModel (session : Session) : ExposureResult :=
  exposeWithFuel (S (length (recursionPool session))) [] session.

Lemma fuel_exhaustion_implies_trace :
  forall fuel seen session,
    exposeWithFuel fuel seen session = ExposureFuelExhausted ->
    exists finalSeen finalSession,
      ExposureTrace seen session finalSeen finalSession fuel.
Proof.
  induction fuel as [| fuel IH]; intros seen session Hexhausted.
  - exists seen, session. constructor.
  - simpl in Hexhausted.
    destruct session as
      [binder messageTy continuation
      |binder messageTy continuation
      |branches
      |branches
      |outcome
      |recursionName body
      |variable]; try discriminate.
    destruct (in_dec string_dec recursionName seen) as [Hseen | Hfresh].
    + discriminate.
    + specialize (IH
        (recursionName :: seen)
        (substituteSessionVar recursionName (Rec recursionName body) body)
        Hexhausted).
      destruct IH as [finalSeen [finalSession Htrace]].
      exists finalSeen, finalSession.
      econstructor.
      * constructor. exact Hfresh.
      * exact Htrace.
Qed.

(* PHIL-SESSION-REC-001 *)
Theorem exposeSessionHeadModel_never_exhausts :
  forall session,
    exposeSessionHeadModel session <> ExposureFuelExhausted.
Proof.
  intros session Hexhausted.
  unfold exposeSessionHeadModel in Hexhausted.
  pose proof
    (fuel_exhaustion_implies_trace
      (S (length (recursionPool session))) [] session Hexhausted)
    as [finalSeen [finalSession Htrace]].
  pose proof (exposure_trace_bounded session finalSeen finalSession
    (S (length (recursionPool session))) Htrace) as Hbound.
  lia.
Qed.

Definition NonRecursiveHead (session : Session) : Prop :=
  match session with
  | Rec _ _ => False
  | SessionVar _ => False
  | _ => True
  end.

Lemma exposed_result_is_nonrecursive_head :
  forall fuel seen session head,
    exposeWithFuel fuel seen session = ExposedHead head ->
    NonRecursiveHead head.
Proof.
  induction fuel as [| fuel IH]; intros seen session head Hexposed.
  - discriminate.
  - simpl in Hexposed.
    destruct session as
      [binder messageTy continuation
      |binder messageTy continuation
      |branches
      |branches
      |outcome
      |recursionName body
      |variable].
    + inversion Hexposed; subst. simpl. exact I.
    + inversion Hexposed; subst. simpl. exact I.
    + inversion Hexposed; subst. simpl. exact I.
    + inversion Hexposed; subst. simpl. exact I.
    + inversion Hexposed; subst. simpl. exact I.
    + destruct (in_dec string_dec recursionName seen) as [Hseen | Hfresh].
      * discriminate.
      * eapply IH. exact Hexposed.
    + discriminate.
Qed.

Theorem exposeSessionHeadModel_classifies :
  forall session,
    match exposeSessionHeadModel session with
    | ExposedHead head => NonRecursiveHead head
    | UnguardedRecursionResult _ => True
    | UnboundSessionVariableResult _ => True
    | ExposureFuelExhausted => False
    end.
Proof.
  intro session.
  remember (exposeSessionHeadModel session) as result eqn:Hresult.
  destruct result as [head | recursionName | variable |].
  - eapply exposed_result_is_nonrecursive_head.
    unfold exposeSessionHeadModel.
    symmetry. exact Hresult.
  - exact I.
  - exact I.
  - exfalso.
    eapply exposeSessionHeadModel_never_exhausts.
    symmetry. exact Hresult.
Qed.
