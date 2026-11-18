From Stdlib Require Import Bool.Bool.

(*
  FSEM-02 non-normative finite gate model. Actual Haskell source replay
  checks source and externally granted protocol authorization, then consumes
  the sender payload before trying the receiver's Linear insertion. These
  boolean observations are NOT a refinement of Haskell Map/Set, borrowed
  resource representation, source binding identity, or protocol authority.
*)
Record FSEM02LoanedOccupiedReceiver : Type := {
  lorSenderLoan : bool;
  lorReceiverOccupied : bool;
  lorReceiverLoan : bool;
  lorReceiverAffine : bool;
  lorSpectatorFrame : bool
}.

Inductive FSEM02LoanedReceiverDecision : Type :=
| LORBadSource
| LORBadAuthority
| LORSenderBorrowed
| LORReceiverDuplicate
| LORAdmitted.

Definition lorDecision (source authority : bool)
    (s : FSEM02LoanedOccupiedReceiver) : FSEM02LoanedReceiverDecision :=
  if source then
    if authority then
      if lorSenderLoan s then LORSenderBorrowed
      else if lorReceiverOccupied s then LORReceiverDuplicate
      else LORAdmitted
    else LORBadAuthority
  else LORBadSource.

Definition lorStep (source authority : bool)
    (s : FSEM02LoanedOccupiedReceiver) :
    option FSEM02LoanedOccupiedReceiver :=
  match lorDecision source authority s with
  | LORAdmitted =>
      Some {| lorSenderLoan := false;
              lorReceiverOccupied := true;
              lorReceiverLoan := false;
              lorReceiverAffine := false;
              lorSpectatorFrame := lorSpectatorFrame s |}
  | _ => None
  end.

(* Only coherent borrowed contexts are admitted as the model's premises:
   a shared loan cannot refer to a receiver name without a binding. *)
Definition lorCoherent (s : FSEM02LoanedOccupiedReceiver) : Prop :=
  lorReceiverLoan s = true -> lorReceiverOccupied s = true.

Theorem lorBadSourcePrecedesAllResourceGates :
  forall authority s,
    lorDecision false authority s = LORBadSource /\
    lorStep false authority s = None.
Proof. intros; split; reflexivity. Qed.

Theorem lorBadAuthorityPrecedesAllResourceGates :
  forall s,
    lorDecision true false s = LORBadAuthority /\
    lorStep true false s = None.
Proof. intros; split; reflexivity. Qed.

Theorem lorBorrowedSenderPrecedesLoanedOccupiedReceiver :
  forall busy loan affine spectator,
    let s := {| lorSenderLoan := true;
                lorReceiverOccupied := busy;
                lorReceiverLoan := loan;
                lorReceiverAffine := affine;
                lorSpectatorFrame := spectator |} in
    lorDecision true true s = LORSenderBorrowed /\
    lorStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem lorActiveReceiverLoanDoesNotHideLinearOrAffineCollision :
  forall affine spectator,
    let s := {| lorSenderLoan := false;
                lorReceiverOccupied := true;
                lorReceiverLoan := true;
                lorReceiverAffine := affine;
                lorSpectatorFrame := spectator |} in
    lorDecision true true s = LORReceiverDuplicate /\
    lorStep true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem lorEndingReceiverLoanNeverErasesDuplicate :
  forall affine spectator,
    let loaned := {| lorSenderLoan := false;
                    lorReceiverOccupied := true;
                    lorReceiverLoan := true;
                    lorReceiverAffine := affine;
                    lorSpectatorFrame := spectator |} in
    let ended := {| lorSenderLoan := false;
                   lorReceiverOccupied := true;
                   lorReceiverLoan := false;
                   lorReceiverAffine := affine;
                   lorSpectatorFrame := spectator |} in
    lorDecision true true loaned = lorDecision true true ended /\
    lorStep true true loaned = lorStep true true ended /\
    lorStep true true ended = None.
Proof. intros; repeat split; reflexivity. Qed.

Theorem lorRepairedResourcesPermitModeledLinearTransfer :
  forall spectator,
    lorStep true true
      {| lorSenderLoan := false;
         lorReceiverOccupied := false;
         lorReceiverLoan := false;
         lorReceiverAffine := false;
         lorSpectatorFrame := spectator |} =
      Some {| lorSenderLoan := false;
              lorReceiverOccupied := true;
              lorReceiverLoan := false;
              lorReceiverAffine := false;
              lorSpectatorFrame := spectator |}.
Proof. reflexivity. Qed.

Theorem lorBusyDestinationHasNoSuccessor :
  forall source authority senderLoan loan affine spectator,
    lorStep source authority
      {| lorSenderLoan := senderLoan;
         lorReceiverOccupied := true;
         lorReceiverLoan := loan;
         lorReceiverAffine := affine;
         lorSpectatorFrame := spectator |} = None.
Proof. intros; destruct source, authority, senderLoan; reflexivity. Qed.

Theorem lorSuccessPreservesSpectatorAndRequiresCleanGates :
  forall source authority s next,
    lorStep source authority s = Some next ->
    source = true /\ authority = true /\
    lorSenderLoan s = false /\ lorReceiverOccupied s = false /\
    lorReceiverOccupied next = true /\
    lorReceiverLoan next = false /\
    lorReceiverAffine next = false /\
    lorSpectatorFrame next = lorSpectatorFrame s.
Proof.
  intros source authority [sender busy loan affine spectator] next H.
  destruct source, authority, sender, busy;
    simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.

Theorem lorCoherentSuccessHasNoDanglingReceiverLoan :
  forall source authority s next,
    lorCoherent s ->
    lorStep source authority s = Some next ->
    lorReceiverLoan s = false.
Proof.
  intros source authority [sender busy loan affine spectator] next Hcoh Hstep.
  destruct source, authority, sender, busy;
    simpl in Hstep; try discriminate.
  destruct loan; simpl; [exfalso | reflexivity].
  unfold lorCoherent in Hcoh.
  simpl in Hcoh.
  specialize (Hcoh eq_refl).
  discriminate.
Qed.
