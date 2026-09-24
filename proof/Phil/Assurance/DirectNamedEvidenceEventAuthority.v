From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import DirectNamedEvidenceAuthority.

(*
  Defensive proof-correspondence continuation of D-CERT-SUPPORT-01.

  DirectNamedEvidenceAuthority.v proves that a directly selected named proof
  must preserve proposition, subject, scope, immutable evidence identity, and
  final-consumer use.  Its bounded selector domain is only DirectEvidenceName,
  however.  The concrete Phase 1 handoff now keys direct authority by the exact
  checking event together with the selected Name.  That event component matters:
  the same display name can legitimately occur at more than one checking event,
  and name-only reuse must not substitute one event's immutable proof record for
  another event.

  This model adds the missing event dimension.  It does not model source
  admission, resource ownership, native lowering, LLVM, packaging, or any
  Phase 1 trusted-computing-base component.
*)

Definition DirectEvidenceCheckEventId := nat.

Record DirectNamedEvidenceEventAuthorityModel : Type :=
  mkDirectNamedEvidenceEventAuthorityModel {
    modelEventDirectSelected :
      DirectEvidenceCheckEventId -> DirectEvidenceName -> bool;
    modelEventAuthoritativeProposition :
      DirectEvidenceCheckEventId -> DirectEvidenceName -> option PropositionIdentity;
    modelEventAuthoritativeSubjects :
      DirectEvidenceCheckEventId -> DirectEvidenceName -> option SubjectIdentity;
    modelEventAuthoritativeScope :
      DirectEvidenceCheckEventId -> DirectEvidenceName -> option ScopeIdentity;
    modelEventMappedEvidence :
      DirectEvidenceCheckEventId -> DirectEvidenceName -> option ImmutableEvidenceId;
    modelEventEvidenceProposition :
      ImmutableEvidenceId -> option PropositionIdentity;
    modelEventEvidenceSubjects :
      ImmutableEvidenceId -> option SubjectIdentity;
    modelEventEvidenceScope :
      ImmutableEvidenceId -> option ScopeIdentity;
    modelEventFinalConsumerUses :
      DirectEvidenceCheckEventId -> ImmutableEvidenceId -> bool
  }.

Definition DirectNamedEvidenceEventAuthorityPreserved
  (model : DirectNamedEvidenceEventAuthorityModel) : Prop :=
  forall event evidenceName,
    modelEventDirectSelected model event evidenceName = true ->
    exists evidence proposition subjects scope,
      modelEventAuthoritativeProposition model event evidenceName = Some proposition /\
      modelEventAuthoritativeSubjects model event evidenceName = Some subjects /\
      modelEventAuthoritativeScope model event evidenceName = Some scope /\
      modelEventMappedEvidence model event evidenceName = Some evidence /\
      modelEventEvidenceProposition model evidence = Some proposition /\
      modelEventEvidenceSubjects model evidence = Some subjects /\
      modelEventEvidenceScope model evidence = Some scope /\
      modelEventFinalConsumerUses model event evidence = true.

Definition EventMappedConsumerOnly
  (model : DirectNamedEvidenceEventAuthorityModel) : Prop :=
  forall event evidenceName,
    modelEventDirectSelected model event evidenceName = true ->
    exists evidence,
      modelEventMappedEvidence model event evidenceName = Some evidence /\
      modelEventFinalConsumerUses model event evidence = true.

Theorem selected_event_named_evidence_requires_exact_authority :
  forall model event evidenceName,
    DirectNamedEvidenceEventAuthorityPreserved model ->
    modelEventDirectSelected model event evidenceName = true ->
    exists evidence proposition subjects scope,
      modelEventAuthoritativeProposition model event evidenceName = Some proposition /\
      modelEventAuthoritativeSubjects model event evidenceName = Some subjects /\
      modelEventAuthoritativeScope model event evidenceName = Some scope /\
      modelEventMappedEvidence model event evidenceName = Some evidence /\
      modelEventEvidenceProposition model evidence = Some proposition /\
      modelEventEvidenceSubjects model evidence = Some subjects /\
      modelEventEvidenceScope model evidence = Some scope /\
      modelEventFinalConsumerUses model event evidence = true.
Proof.
  intros model event evidenceName Hpreserved Hselected.
  eapply Hpreserved.
  exact Hselected.
Qed.

Definition selectedTwoEventSameName
  (event : DirectEvidenceCheckEventId)
  (evidenceName : DirectEvidenceName) : bool :=
  Nat.eqb evidenceName 1 && (Nat.eqb event 7 || Nat.eqb event 8).

(*
  Negative witness: both checking events select the same display name.  A
  name-only adapter maps both to evidence 10.  That record is authoritative for
  event 7, but event 8 has a distinct scope.  Merely reaching a consumer with a
  mapped immutable record therefore does not establish event-scoped authority.
*)
Definition reusedNameWrongEventWitness : DirectNamedEvidenceEventAuthorityModel :=
  mkDirectNamedEvidenceEventAuthorityModel
    selectedTwoEventSameName
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 && (Nat.eqb event 7 || Nat.eqb event 8)
      then Some 100 else None)
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 && (Nat.eqb event 7 || Nat.eqb event 8)
      then Some 200 else None)
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 then
        if Nat.eqb event 7 then Some 300
        else if Nat.eqb event 8 then Some 301 else None
      else None)
    (fun _event evidenceName =>
      if Nat.eqb evidenceName 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 100 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 300 else None)
    (fun event evidence =>
      (Nat.eqb event 7 || Nat.eqb event 8) && Nat.eqb evidence 10).

Theorem reused_name_wrong_event_still_reaches_consumers :
  EventMappedConsumerOnly reusedNameWrongEventWitness.
Proof.
  intros event evidenceName Hselected.
  unfold selectedTwoEventSameName in Hselected.
  apply andb_true_iff in Hselected as [Hname Hevent].
  apply Nat.eqb_eq in Hname.
  subst evidenceName.
  exists 10.
  split.
  - reflexivity.
  - cbn.
    rewrite Hevent.
    reflexivity.
Qed.

Theorem reused_name_wrong_event_lacks_event_authority :
  ~ DirectNamedEvidenceEventAuthorityPreserved reusedNameWrongEventWitness.
Proof.
  intro Hpreserved.
  pose proof (Hpreserved 8 1 eq_refl) as Hselected.
  destruct Hselected as
    [evidence [proposition [subjects [scope
      [Hproposition
      [Hsubjects
      [Hscope
      [Hmapped
      [HevidenceProposition
      [HevidenceSubjects
      [HevidenceScope Hconsumer]]]]]]]]]]].
  cbn in Hscope, Hmapped.
  inversion Hscope; subst scope.
  inversion Hmapped; subst evidence.
  cbn in HevidenceScope.
  discriminate.
Qed.

Theorem name_only_reuse_does_not_establish_event_authority :
  EventMappedConsumerOnly reusedNameWrongEventWitness /\
  ~ DirectNamedEvidenceEventAuthorityPreserved reusedNameWrongEventWitness.
Proof.
  split.
  - exact reused_name_wrong_event_still_reaches_consumers.
  - exact reused_name_wrong_event_lacks_event_authority.
Qed.

(* Positive witness: the same display name is selected at both events, but the
   event+name key resolves each event to its own authoritative immutable record. *)
Definition exactEventKeyedDirectEvidenceWitness
  : DirectNamedEvidenceEventAuthorityModel :=
  mkDirectNamedEvidenceEventAuthorityModel
    selectedTwoEventSameName
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 && (Nat.eqb event 7 || Nat.eqb event 8)
      then Some 100 else None)
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 && (Nat.eqb event 7 || Nat.eqb event 8)
      then Some 200 else None)
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 then
        if Nat.eqb event 7 then Some 300
        else if Nat.eqb event 8 then Some 301 else None
      else None)
    (fun event evidenceName =>
      if Nat.eqb evidenceName 1 then
        if Nat.eqb event 7 then Some 10
        else if Nat.eqb event 8 then Some 11 else None
      else None)
    (fun evidence =>
      if Nat.eqb evidence 10 || Nat.eqb evidence 11 then Some 100 else None)
    (fun evidence =>
      if Nat.eqb evidence 10 || Nat.eqb evidence 11 then Some 200 else None)
    (fun evidence =>
      if Nat.eqb evidence 10 then Some 300
      else if Nat.eqb evidence 11 then Some 301 else None)
    (fun event evidence =>
      (Nat.eqb event 7 && Nat.eqb evidence 10) ||
      (Nat.eqb event 8 && Nat.eqb evidence 11)).

Theorem exact_event_keyed_direct_evidence_preserves_authority :
  DirectNamedEvidenceEventAuthorityPreserved
    exactEventKeyedDirectEvidenceWitness.
Proof.
  intros event evidenceName Hselected.
  unfold selectedTwoEventSameName in Hselected.
  apply andb_true_iff in Hselected as [Hname Hevent].
  apply Nat.eqb_eq in Hname.
  subst evidenceName.
  apply orb_true_iff in Hevent as [Hevent7 | Hevent8].
  - apply Nat.eqb_eq in Hevent7.
    subst event.
    exists 10, 100, 200, 300.
    repeat split; reflexivity.
  - apply Nat.eqb_eq in Hevent8.
    subst event.
    exists 11, 100, 200, 301.
    repeat split; reflexivity.
Qed.

Theorem exact_event_keyed_direct_evidence_reaches_consumers :
  EventMappedConsumerOnly exactEventKeyedDirectEvidenceWitness.
Proof.
  intros event evidenceName Hselected.
  pose proof
    (selected_event_named_evidence_requires_exact_authority
      exactEventKeyedDirectEvidenceWitness event evidenceName
      exact_event_keyed_direct_evidence_preserves_authority
      Hselected)
    as Hauthority.
  destruct Hauthority as
    [evidence [proposition [subjects [scope
      [Hproposition
      [Hsubjects
      [Hscope
      [Hmapped
      [HevidenceProposition
      [HevidenceSubjects
      [HevidenceScope Hconsumer]]]]]]]]]]].
  exists evidence.
  split.
  - exact Hmapped.
  - exact Hconsumer.
Qed.
