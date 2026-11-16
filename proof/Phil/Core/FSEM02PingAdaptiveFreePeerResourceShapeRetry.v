From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import FSEM02PingAdaptiveHalfCloseSuffix.

(* FSEM-02, non-normative: an additional FINITE resource-shape observation
   gate around the already-conditional adaptive Ping phase relation.
   nat keys are not native ProcessKeys; the resource observation, source
   projection, instance/role, activation, partner choice, Close and disposal
   authority are independent inputs, NOT inferred from the source spelling.
   The actual Haskell checker and Map representations are not modeled here. *)

Inductive fsem02AdaptiveResourceShape : Type :=
| FSEM02NoResource
| FSEM02NonEndpointResource
| FSEM02EndpointResource (observedHead : nat).

Inductive fsem02AdaptiveResourceFailure : Type :=
| FSEM02MissingOwner
| FSEM02WrongResourceType
| FSEM02WrongResourceSession.

Definition fsem02AdaptiveResourceShapeCheck
  (expectedHead : nat) (observed : fsem02AdaptiveResourceShape)
  : option fsem02AdaptiveResourceFailure :=
  match observed with
  | FSEM02NoResource => Some FSEM02MissingOwner
  | FSEM02NonEndpointResource => Some FSEM02WrongResourceType
  | FSEM02EndpointResource observedHead =>
      if Nat.eqb expectedHead observedHead
      then None else Some FSEM02WrongResourceSession
  end.

(* The check of the Client resource precedes Server resource checking.
   An inl diagnostic has NO post-state; the model's admitted protocol step
   is consulted only after BOTH independent resource observations pass. *)
Definition fsem02AdaptiveShapeGatedPing
  (client server expectedClientHead expectedServerHead : nat)
  (clientResource serverResource : fsem02AdaptiveResourceShape)
  (before : fsem02MixPhaseMap)
  : (nat * fsem02AdaptiveResourceFailure) + option fsem02MixPhaseMap :=
  match fsem02AdaptiveResourceShapeCheck expectedClientHead clientResource with
  | Some fault => inl (client, fault)
  | None =>
      match fsem02AdaptiveResourceShapeCheck expectedServerHead serverResource with
      | Some fault => inl (server, fault)
      | None => inr (fsem02AdaptivePhaseJointPing client server before)
      end
  end.

Theorem fsem02AdaptiveFreeClientWrongTypeExact :
  forall client server expectedClient expectedServer serverResource before,
    fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
      FSEM02NonEndpointResource serverResource before =
    inl (client, FSEM02WrongResourceType).
Proof.
  reflexivity.
Qed.

Theorem fsem02AdaptiveFreeServerWrongTypeExact :
  forall client server expectedClient expectedServer before,
    fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
      (FSEM02EndpointResource expectedClient) FSEM02NonEndpointResource before =
    inl (server, FSEM02WrongResourceType).
Proof.
  intros.
  unfold fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
  now rewrite Nat.eqb_refl.
Qed.

Theorem fsem02AdaptiveFreeClientWrongSessionExact :
  forall client server expectedClient expectedServer observed serverResource before,
    expectedClient <> observed ->
    fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
      (FSEM02EndpointResource observed) serverResource before =
    inl (client, FSEM02WrongResourceSession).
Proof.
  intros client server expectedClient expectedServer observed serverResource before Hneq.
  unfold fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
  assert (Hbad : Nat.eqb expectedClient observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  now rewrite Hbad.
Qed.

Theorem fsem02AdaptiveFreeServerWrongSessionExact :
  forall client server expectedClient expectedServer observed before,
    expectedServer <> observed ->
    fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
      (FSEM02EndpointResource expectedClient) (FSEM02EndpointResource observed) before =
    inl (server, FSEM02WrongResourceSession).
Proof.
  intros client server expectedClient expectedServer observed before Hneq.
  unfold fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
  assert (Hbad : Nat.eqb expectedServer observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  rewrite Nat.eqb_refl, Hbad.
  reflexivity.
Qed.

Theorem fsem02AdaptiveExactResourceRepairRestoresStep :
  forall client server expectedClient expectedServer before after,
    fsem02AdaptivePhaseJointPing client server before = Some after ->
    fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
      (FSEM02EndpointResource expectedClient)
      (FSEM02EndpointResource expectedServer) before = inr (Some after).
Proof.
  intros client server expectedClient expectedServer before after Hstep.
  unfold fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
  repeat rewrite Nat.eqb_refl.
  now rewrite Hstep.
Qed.

Theorem fsem02AdaptiveDoubleWrongTypeClientPriority :
  forall client server expectedClient expectedServer before,
    fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
      FSEM02NonEndpointResource FSEM02NonEndpointResource before =
    inl (client, FSEM02WrongResourceType).
Proof.
  reflexivity.
Qed.

Theorem fsem02AdaptiveHalfCloseResourceShapeFaultsThenRetry :
  forall priorClient priorServer freeClient freeServer
         priorClientPhase priorServerPhase expectedClient expectedServer before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    let prefix := fsem02MixWrite priorClient priorClientPhase
      (fsem02MixWrite priorServer priorServerPhase before) in
    fsem02AdaptiveShapeGatedPing freeClient freeServer expectedClient expectedServer
      FSEM02NonEndpointResource (FSEM02EndpointResource expectedServer) prefix =
      inl (freeClient, FSEM02WrongResourceType) /\
    fsem02AdaptiveShapeGatedPing freeClient freeServer expectedClient expectedServer
      (FSEM02EndpointResource expectedClient) FSEM02NonEndpointResource prefix =
      inl (freeServer, FSEM02WrongResourceType) /\
    fsem02AdaptiveShapeGatedPing freeClient freeServer expectedClient expectedServer
      (FSEM02EndpointResource expectedClient)
      (FSEM02EndpointResource expectedServer) prefix =
      inr (Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd prefix))).
Proof.
  intros priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase expectedClient expectedServer before
    Hcc Hcs Hsc Hss Hc Hs.
  simpl.
  split.
  - reflexivity.
  - split.
    + unfold fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
      now rewrite Nat.eqb_refl.
    + unfold fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
      repeat rewrite Nat.eqb_refl.
      now rewrite (fsem02AdaptiveHalfClosedFreePairStillEnabled
        priorClient priorServer freeClient freeServer
        priorClientPhase priorServerPhase before Hcc Hcs Hsc Hss Hc Hs).
Qed.
