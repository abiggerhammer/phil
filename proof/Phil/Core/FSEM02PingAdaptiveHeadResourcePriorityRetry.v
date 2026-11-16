From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import FSEM02PingMixedPrefixFault
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingAdaptiveFreePeerResourceShapeRetry.

(* FSEM-02, non-normative. The two observed projected heads and the two
   resource observations are independent EXTERNAL inputs. This finite
   diagnostic-priority model is not a representation/refinement theorem
   about the Haskell ProcessContext, Map or actual source elaboration. *)
Inductive fsem02AdaptiveHeadShapeResult : Type :=
| FSEM02HeadMismatch (process expected actual : nat)
| FSEM02ShapeMismatch (process : nat) (fault : fsem02AdaptiveResourceFailure)
| FSEM02HeadShapeStep (successor : option fsem02MixPhaseMap).

Definition fsem02AdaptiveHeadShapeGate
  (client server expectedClient expectedServer observedClient observedServer : nat)
  (clientResource serverResource : fsem02AdaptiveResourceShape)
  (before : fsem02MixPhaseMap) : fsem02AdaptiveHeadShapeResult :=
  if Nat.eqb expectedClient observedClient then
    if Nat.eqb expectedServer observedServer then
      match fsem02AdaptiveShapeGatedPing client server expectedClient expectedServer
              clientResource serverResource before with
      | inl (site, fault) => FSEM02ShapeMismatch site fault
      | inr successor => FSEM02HeadShapeStep successor
      end
    else FSEM02HeadMismatch server expectedServer observedServer
  else FSEM02HeadMismatch client expectedClient observedClient.

(* A bad projected source head masks that peer's simultaneously bad resource
   observation: rejection yields no successor. *)
Theorem fsem02AdaptiveClientBadHeadMasksResource :
  forall client server ec es observed rc rs before,
    ec <> observed ->
    fsem02AdaptiveHeadShapeGate client server ec es observed es rc rs before =
      FSEM02HeadMismatch client ec observed.
Proof.
  intros client server ec es observed rc rs before Hneq.
  unfold fsem02AdaptiveHeadShapeGate.
  assert (Hbad : Nat.eqb ec observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  now rewrite Hbad.
Qed.

Theorem fsem02AdaptiveServerBadHeadMasksResource :
  forall client server ec es observed rc rs before,
    es <> observed ->
    fsem02AdaptiveHeadShapeGate client server ec es ec observed rc rs before =
      FSEM02HeadMismatch server es observed.
Proof.
  intros client server ec es observed rc rs before Hneq.
  unfold fsem02AdaptiveHeadShapeGate.
  assert (Hbad : Nat.eqb es observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  now rewrite Nat.eqb_refl, Hbad.
Qed.

(* Correcting ONLY a head exposes the uncorrected resource error. *)
Theorem fsem02AdaptiveClientHeadRepairExposesWrongType :
  forall client server ec es before,
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      FSEM02NonEndpointResource (FSEM02EndpointResource es) before =
      FSEM02ShapeMismatch client FSEM02WrongResourceType.
Proof.
  intros.
  unfold fsem02AdaptiveHeadShapeGate,
    fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem fsem02AdaptiveServerHeadRepairExposesWrongSession :
  forall client server ec es observed before,
    es <> observed ->
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource observed) before =
      FSEM02ShapeMismatch server FSEM02WrongResourceSession.
Proof.
  intros client server ec es observed before Hneq.
  unfold fsem02AdaptiveHeadShapeGate,
    fsem02AdaptiveShapeGatedPing, fsem02AdaptiveResourceShapeCheck.
  assert (Hbad : Nat.eqb es observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  repeat rewrite Nat.eqb_refl.
  now rewrite Hbad.
Qed.

(* Both inputs must be restored explicitly before the admitted phase step. *)
Theorem fsem02AdaptiveBothRepairsRestoreExactStep :
  forall client server ec es before after,
    fsem02AdaptivePhaseJointPing client server before = Some after ->
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource es) before =
      FSEM02HeadShapeStep (Some after).
Proof.
  intros client server ec es before after Hstep.
  unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
    fsem02AdaptiveResourceShapeCheck.
  repeat rewrite Nat.eqb_refl.
  now rewrite Hstep.
Qed.

(* The same admitted replay after an externally chosen prior half-Close.
   No theorem derives the partner selection or Close/disposal authority. *)
Theorem fsem02AdaptiveHalfCloseCombinedRepair :
  forall priorClient priorServer freeClient freeServer
         priorClientPhase priorServerPhase ec es before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    let prefix := fsem02MixWrite priorClient priorClientPhase
      (fsem02MixWrite priorServer priorServerPhase before) in
    fsem02AdaptiveHeadShapeGate freeClient freeServer ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource es) prefix =
      FSEM02HeadShapeStep (Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd prefix))).
Proof.
  intros priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before
    Hcc Hcs Hsc Hss Hc Hs.
  simpl.
  unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
    fsem02AdaptiveResourceShapeCheck.
  repeat rewrite Nat.eqb_refl.
  now rewrite (fsem02AdaptiveHalfClosedFreePairStillEnabled
    priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase before Hcc Hcs Hsc Hss Hc Hs).
Qed.
