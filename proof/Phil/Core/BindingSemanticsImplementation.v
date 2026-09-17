From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import BindingSemantics.

(*
  PHIL-EXEC-BIND-001 — finite executable correspondence.

  Production has several separate authorities (lexical binder allocation,
  initialization traces, structural-discard StageContract correspondence, and
  explicit release selection).  This normalized layer certifies the conjunction
  structure of the already-reflected facts without replacing those authorities.
*)

Definition bindingSafetyFactsb
  (binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound : bool) : bool :=
  andb binderIdentityExact
    (andb duplicateFree
      (andb noActiveShadowing
        (andb initializedBeforeUse
          (andb noReinitialization
            (andb storageDisciplineValid
              (andb sourceImmutable
                (andb discardSemanticallyEmpty
                  (andb releaseCompetent releaseAccountBound)))))))).

Inductive BindingSafetyDecision : Type :=
| BindingSafetyAccepted
| BindingSafetyRejected.

Definition decideBindingSafety
  (binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound : bool)
  : BindingSafetyDecision :=
  if bindingSafetyFactsb
      binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty releaseCompetent releaseAccountBound
  then BindingSafetyAccepted
  else BindingSafetyRejected.

Theorem binding_safety_facts_true_iff_all_gates :
  forall binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound,
    bindingSafetyFactsb
      binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty releaseCompetent releaseAccountBound = true <->
    binderIdentityExact = true /\
    duplicateFree = true /\
    noActiveShadowing = true /\
    initializedBeforeUse = true /\
    noReinitialization = true /\
    storageDisciplineValid = true /\
    sourceImmutable = true /\
    discardSemanticallyEmpty = true /\
    releaseCompetent = true /\
    releaseAccountBound = true.
Proof.
  intros.
  unfold bindingSafetyFactsb.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem binding_safety_decision_accept_iff_facts_true :
  forall binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound,
    decideBindingSafety
      binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty releaseCompetent releaseAccountBound =
      BindingSafetyAccepted <->
    bindingSafetyFactsb
      binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty releaseCompetent releaseAccountBound = true.
Proof.
  intros.
  unfold decideBindingSafety.
  destruct (bindingSafetyFactsb
    binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound).
  - split; intros; reflexivity.
  - split; intros H; discriminate H.
Qed.

Theorem duplicate_binder_gate_fails_closed :
  forall binderIdentityExact noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound,
    decideBindingSafety
      binderIdentityExact false noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty releaseCompetent releaseAccountBound =
      BindingSafetyRejected.
Proof.
  intros.
  destruct binderIdentityExact; reflexivity.
Qed.

Theorem uninitialized_observation_gate_fails_closed :
  forall binderIdentityExact duplicateFree noActiveShadowing
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseCompetent releaseAccountBound,
    decideBindingSafety
      binderIdentityExact duplicateFree noActiveShadowing false
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty releaseCompetent releaseAccountBound =
      BindingSafetyRejected.
Proof.
  intros.
  unfold decideBindingSafety, bindingSafetyFactsb.
  repeat rewrite andb_false_r.
  destruct binderIdentityExact, duplicateFree, noActiveShadowing; reflexivity.
Qed.

Theorem hidden_finalizer_gate_fails_closed :
  forall binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    releaseCompetent releaseAccountBound,
    decideBindingSafety
      binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      false releaseCompetent releaseAccountBound = BindingSafetyRejected.
Proof.
  intros.
  unfold decideBindingSafety, bindingSafetyFactsb.
  destruct binderIdentityExact, duplicateFree, noActiveShadowing,
    initializedBeforeUse, noReinitialization, storageDisciplineValid,
    sourceImmutable; reflexivity.
Qed.

Theorem missing_release_competence_gate_fails_closed :
  forall binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
    noReinitialization storageDisciplineValid sourceImmutable
    discardSemanticallyEmpty releaseAccountBound,
    decideBindingSafety
      binderIdentityExact duplicateFree noActiveShadowing initializedBeforeUse
      noReinitialization storageDisciplineValid sourceImmutable
      discardSemanticallyEmpty false releaseAccountBound = BindingSafetyRejected.
Proof.
  intros.
  unfold decideBindingSafety, bindingSafetyFactsb.
  destruct binderIdentityExact, duplicateFree, noActiveShadowing,
    initializedBeforeUse, noReinitialization, storageDisciplineValid,
    sourceImmutable, discardSemanticallyEmpty; reflexivity.
Qed.

Theorem all_exact_binding_gates_accept :
  decideBindingSafety true true true true true true true true true true =
    BindingSafetyAccepted.
Proof.
  reflexivity.
Qed.
