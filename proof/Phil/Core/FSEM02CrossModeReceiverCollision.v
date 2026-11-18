From Stdlib Require Import Bool.Bool.

(*
  FSEM-02: non-normative cross-mode receiving-name collision model. Actual
  Haskell ResourceContext has disjoint unrestricted/affine/linear maps and
  insertBinding checks name presence across all modes. These booleans are an
  admitted finite abstraction, not a proof of that native Map invariant.
  Source validity, external protocol/activation/head authority and authorized
  binder identity are independent premises, never sourced from spelling.
*)
Record FSEM02CrossModeState : Type := {
  cmSenderPresent : bool;
  cmSenderTyped : bool;
  cmReceiverLinearOccupied : bool;
  cmReceiverAffineOccupied : bool;
  cmReceiverUnrestrictedOccupied : bool;
  cmSpectatorPreserved : bool
}.

Inductive FSEM02CrossModeDecision : Type :=
| CMBadSource
| CMBadExternalAuthority
| CMBadProtocolBinder
| CMMissingSender
| CMWrongSenderType
| CMCollidingReceiverName
| CMAdmitted.

Definition cmReceiverOccupied (s : FSEM02CrossModeState) : bool :=
  orb (cmReceiverLinearOccupied s)
    (orb (cmReceiverAffineOccupied s) (cmReceiverUnrestrictedOccupied s)).

Definition cmDecision (source prior binder : bool)
    (s : FSEM02CrossModeState) : FSEM02CrossModeDecision :=
  if source then
    if prior then
      if binder then
        if cmSenderPresent s then
          if cmSenderTyped s then
            if cmReceiverOccupied s then CMCollidingReceiverName
            else CMAdmitted
          else CMWrongSenderType
        else CMMissingSender
      else CMBadProtocolBinder
    else CMBadExternalAuthority
  else CMBadSource.

Definition cmStep (source prior binder : bool)
    (s : FSEM02CrossModeState) : option FSEM02CrossModeState :=
  match cmDecision source prior binder s with
  | CMAdmitted =>
      Some {| cmSenderPresent := false;
              cmSenderTyped := true;
              cmReceiverLinearOccupied := true;
              cmReceiverAffineOccupied := false;
              cmReceiverUnrestrictedOccupied := false;
              cmSpectatorPreserved := cmSpectatorPreserved s |}
  | _ => None
  end.

Theorem cmSourceRefusalBeforeAllExternalGates :
  forall prior binder s,
    cmDecision false prior binder s = CMBadSource /\
    cmStep false prior binder s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmBinderRefusalBeforeAnyResourceGate :
  forall s,
    cmDecision true true false s = CMBadProtocolBinder /\
    cmStep true true false s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmSenderTypeRefusalBeforeAnyReceiverMode :
  forall linear affine unrestricted spectator,
    let s := {| cmSenderPresent := true;
                cmSenderTyped := false;
                cmReceiverLinearOccupied := linear;
                cmReceiverAffineOccupied := affine;
                cmReceiverUnrestrictedOccupied := unrestricted;
                cmSpectatorPreserved := spectator |} in
    cmDecision true true true s = CMWrongSenderType /\
    cmStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmAffineNameCollisionEvenWhenLinearVacant :
  forall spectator,
    let s := {| cmSenderPresent := true;
                cmSenderTyped := true;
                cmReceiverLinearOccupied := false;
                cmReceiverAffineOccupied := true;
                cmReceiverUnrestrictedOccupied := false;
                cmSpectatorPreserved := spectator |} in
    cmDecision true true true s = CMCollidingReceiverName /\
    cmStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmUnrestrictedNameCollisionEvenWhenLinearVacant :
  forall spectator,
    let s := {| cmSenderPresent := true;
                cmSenderTyped := true;
                cmReceiverLinearOccupied := false;
                cmReceiverAffineOccupied := false;
                cmReceiverUnrestrictedOccupied := true;
                cmSpectatorPreserved := spectator |} in
    cmDecision true true true s = CMCollidingReceiverName /\
    cmStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmAnyReceiverNameCollisionCannotStep :
  forall linear affine unrestricted spectator,
    orb linear (orb affine unrestricted) = true ->
    cmStep true true true
      {| cmSenderPresent := true;
         cmSenderTyped := true;
         cmReceiverLinearOccupied := linear;
         cmReceiverAffineOccupied := affine;
         cmReceiverUnrestrictedOccupied := unrestricted;
         cmSpectatorPreserved := spectator |} = None.
Proof.
  intros linear affine unrestricted spectator H.
  unfold cmStep, cmDecision, cmReceiverOccupied; simpl.
  rewrite H. reflexivity.
Qed.

Theorem cmAllRepairsGiveExactModeTransferAndFrame :
  forall spectator,
    cmStep true true true
      {| cmSenderPresent := true;
         cmSenderTyped := true;
         cmReceiverLinearOccupied := false;
         cmReceiverAffineOccupied := false;
         cmReceiverUnrestrictedOccupied := false;
         cmSpectatorPreserved := spectator |} =
    Some {| cmSenderPresent := false;
            cmSenderTyped := true;
            cmReceiverLinearOccupied := true;
            cmReceiverAffineOccupied := false;
            cmReceiverUnrestrictedOccupied := false;
            cmSpectatorPreserved := spectator |}.
Proof. reflexivity. Qed.

Theorem cmStepRequiresEveryGateAndVacantAllModes :
  forall source prior binder s next,
    cmStep source prior binder s = Some next ->
    source = true /\ prior = true /\ binder = true /\
    cmSenderPresent s = true /\ cmSenderTyped s = true /\
    cmReceiverLinearOccupied s = false /\
    cmReceiverAffineOccupied s = false /\
    cmReceiverUnrestrictedOccupied s = false /\
    cmSenderPresent next = false /\
    cmReceiverLinearOccupied next = true /\
    cmReceiverAffineOccupied next = false /\
    cmReceiverUnrestrictedOccupied next = false /\
    cmSpectatorPreserved next = cmSpectatorPreserved s.
Proof.
  intros source prior binder [sender typed linear affine unrestricted spectator] next H.
  destruct source, prior, binder, sender, typed, linear, affine, unrestricted;
    simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.
