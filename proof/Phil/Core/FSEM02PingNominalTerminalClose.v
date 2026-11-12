From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax Context SessionStep
  FSEM02ProtocolHeadProgression FSEM02PingNominalOriginGates.

(* NON-NORMATIVE: nominal identity is a supplied input, not inferred
   from source syntax or matching local session heads. *)
Open Scope string_scope.

Theorem fsem02PingCloseWrongInstanceRejects :
  forall expected live role outcome endpoint successor context,
    String.eqb expected live = false ->
    fsem02NominalPingGate expected live role role
      (FSEM02Close outcome) (End outcome) endpoint successor context = StepFailed.
Proof.
  intros expected live role outcome endpoint successor context Hwrong.
  now apply fsem02PingWrongInstanceCannotAdvance.
Qed.

Theorem fsem02PingCloseWrongRoleRejects :
  forall instance expected live outcome endpoint successor context,
    String.eqb expected live = false ->
    fsem02NominalPingGate instance instance expected live
      (FSEM02Close outcome) (End outcome) endpoint successor context = StepFailed.
Proof.
  intros instance expected live outcome endpoint successor context Hwrong.
  apply fsem02PingWrongRoleCannotAdvance.
  - apply String.eqb_refl.
  - exact Hwrong.
Qed.

Theorem fsem02PingCloseMatchingConsumesNoSuccessor :
  forall instance role outcome endpoint successor context next,
    fsem02NominalPingGate instance instance role role
      (FSEM02Close outcome) (End outcome)
      endpoint successor context = StepSucceeded next ->
    (exists ty : Ty, linearBindings context endpoint = Some ty) /\
    linearBindings next endpoint = None /\
    (forall other : Name, String.eqb other endpoint = false ->
      linearBindings next other = linearBindings context other) /\
    sharedLoans next = sharedLoans context.
Proof.
  intros instance role outcome endpoint successor context next Hstep.
  rewrite fsem02PingMatchingNominalIdentityDelegates in Hstep.
  unfold fsem02Progression, selectedContinuation in Hstep.
  rewrite String.eqb_refl in Hstep.
  simpl in Hstep.
  exact (closeEndpointResource_success_exact endpoint context next Hstep).
Qed.

Theorem fsem02PingCloseWrongOutcomeRejects :
  forall instance role expected actual endpoint successor context,
    String.eqb expected actual = false ->
    fsem02NominalPingGate instance instance role role
      (FSEM02Close actual) (End expected) endpoint successor context = StepFailed.
Proof.
  intros instance role expected actual endpoint successor context Hwrong.
  rewrite fsem02PingMatchingNominalIdentityDelegates.
  unfold fsem02Progression, selectedContinuation.
  rewrite Hwrong.
  reflexivity.
Qed.
