From Stdlib Require Import Bool.Bool.

(*
  FSEM-02 NON-NORMATIVE finite decision model. Real Haskell source/Core
  restricted transfer requires a Linear sender payload for the admitted
  Bytes[8] source. A present same-type Affine or Unrestricted binding at
  that name fails consumeLinear before receiver insertion. These flags
  do not encode the source checker, Map/Set or external nominal authority.
*)
Inductive CMSMode : Type :=
| CMSLinear | CMSAffine | CMSUnrestricted.

Record CMSResources : Type := {
  cmsSenderMode : CMSMode;
  cmsReceiverBusy : bool;
  cmsSpectatorFrame : bool
}.

Inductive CMSDecision : Type :=
| CMSBadSource
| CMSBadAuthority
| CMSWrongStructuralMode
| CMSReceiverDuplicate
| CMSAdmitted.

Definition cmsDecision (source authority : bool)
    (s : CMSResources) : CMSDecision :=
  if source then
    if authority then
      match cmsSenderMode s with
      | CMSLinear =>
          if cmsReceiverBusy s then CMSReceiverDuplicate else CMSAdmitted
      | CMSAffine | CMSUnrestricted => CMSWrongStructuralMode
      end
    else CMSBadAuthority
  else CMSBadSource.

(* Success moves the modeled payload owner from sender to receiver and
   preserves the independently admitted spectator observation. Failure has
   no successor, including no partially advanced endpoint or resource. *)
Definition cmsStep (source authority : bool)
    (s : CMSResources) : option (bool * bool * bool) :=
  match cmsDecision source authority s with
  | CMSAdmitted => Some (false, true, cmsSpectatorFrame s)
  | _ => None
  end.

Theorem cmsBadSourcePreemptsModeAndCollision :
  forall authority s,
    cmsDecision false authority s = CMSBadSource /\
    cmsStep false authority s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsBadAuthorityPreemptsModeAndCollision :
  forall s,
    cmsDecision true false s = CMSBadAuthority /\
    cmsStep true false s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsAffineSenderWrongModeBeforeAnyDestination :
  forall busy spectator,
    let s := {| cmsSenderMode := CMSAffine;
                cmsReceiverBusy := busy;
                cmsSpectatorFrame := spectator |} in
    cmsDecision true true s = CMSWrongStructuralMode /\
    cmsStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsUnrestrictedSenderWrongModeBeforeAnyDestination :
  forall busy spectator,
    let s := {| cmsSenderMode := CMSUnrestricted;
                cmsReceiverBusy := busy;
                cmsSpectatorFrame := spectator |} in
    cmsDecision true true s = CMSWrongStructuralMode /\
    cmsStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsReceiverRepairDoesNotExcuseAffineSender :
  forall spectator,
    let s := {| cmsSenderMode := CMSAffine;
                cmsReceiverBusy := false;
                cmsSpectatorFrame := spectator |} in
    cmsDecision true true s = CMSWrongStructuralMode /\
    cmsStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsReceiverRepairDoesNotExcuseUnrestrictedSender :
  forall spectator,
    let s := {| cmsSenderMode := CMSUnrestricted;
                cmsReceiverBusy := false;
                cmsSpectatorFrame := spectator |} in
    cmsDecision true true s = CMSWrongStructuralMode /\
    cmsStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsSenderRepairExposesReceiverDuplicate :
  forall spectator,
    let s := {| cmsSenderMode := CMSLinear;
                cmsReceiverBusy := true;
                cmsSpectatorFrame := spectator |} in
    cmsDecision true true s = CMSReceiverDuplicate /\
    cmsStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem cmsIndependentRepairsAllowFramedTransfer :
  forall spectator,
    let s := {| cmsSenderMode := CMSLinear;
                cmsReceiverBusy := false;
                cmsSpectatorFrame := spectator |} in
    cmsDecision true true s = CMSAdmitted /\
    cmsStep true true s = Some (false, true, spectator).
Proof. intros; split; reflexivity. Qed.

Theorem cmsWrongModeNoPartialSuccessor :
  forall spectator busy,
    cmsStep true true
      {| cmsSenderMode := CMSAffine;
         cmsReceiverBusy := busy;
         cmsSpectatorFrame := spectator |} = None /\
    cmsStep true true
      {| cmsSenderMode := CMSUnrestricted;
         cmsReceiverBusy := busy;
         cmsSpectatorFrame := spectator |} = None.
Proof. intros; split; reflexivity. Qed.
