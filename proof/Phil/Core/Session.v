From Phil.Core Require Import Syntax.

Fixpoint dualSession (session : Session) : Session :=
  match session with
  | Send binder messageTy continuation =>
      Receive binder messageTy (dualSession continuation)
  | Receive binder messageTy continuation =>
      Send binder messageTy (dualSession continuation)
  | Select branches => Offer (dualBranches branches)
  | Offer branches => Select (dualBranches branches)
  | End outcome => End outcome
  | Rec recursionName body => Rec recursionName (dualSession body)
  | SessionVar variable => SessionVar variable
  end
with dualBranches (branches : Branches) : Branches :=
  match branches with
  | BNil => BNil
  | BCons label payload continuation rest =>
      BCons label payload (dualSession continuation) (dualBranches rest)
  end.

(* PHIL-SESSION-DUAL-001 *)
Theorem dual_involutive :
  (forall session : Session,
      dualSession (dualSession session) = session) /\
  (forall branches : Branches,
      dualBranches (dualBranches branches) = branches).
Proof.
  apply Session_Branches_mutind.
  - intros binder messageTy continuation IH.
    simpl. now rewrite IH.
  - intros binder messageTy continuation IH.
    simpl. now rewrite IH.
  - intros branches IH.
    simpl. now rewrite IH.
  - intros branches IH.
    simpl. now rewrite IH.
  - intros outcome.
    reflexivity.
  - intros recursionName body IH.
    simpl. now rewrite IH.
  - intros variable.
    reflexivity.
  - reflexivity.
  - intros label payload continuation IHcontinuation rest IHrest.
    simpl. now rewrite IHcontinuation, IHrest.
Qed.

Corollary dualSession_involutive :
  forall session : Session,
    dualSession (dualSession session) = session.
Proof.
  exact (proj1 dual_involutive).
Qed.
