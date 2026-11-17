From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import
  FSEM02PingAdaptiveDualHeadResourceLadder
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* Non-normative FSEM-02. These are finite nat-carrier diagnostic
   observations, not an implementation representation theorem.
   Source projection fidelity, linear owner representation, nominal
   instance/activation, partner/root selection, Close/disposal authority,
   scheduler choices and assurance are independently supplied premises. *)

(* Four explicit repairs: Client projection; Server projection;
   Client linear resource; Server linear resource. Rejection produces a
   diagnostic constructor, never a phase-map successor. *)
Theorem fsem02FourFaultPreciseDiagnosticOrder :
  forall client server ec es badClient badServer
         clientResource serverResource clientFault serverFault before,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec clientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es serverResource = Some serverFault ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      clientResource serverResource before =
        FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      clientResource serverResource before =
        FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      clientResource serverResource before =
        FSEM02ShapeMismatch client clientFault /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) serverResource before =
        FSEM02ShapeMismatch server serverFault.
Proof.
  intros client server ec es badClient badServer
    clientResource serverResource clientFault serverFault before
    Hc Hs Hrc Hrs.
  repeat split.
  - unfold fsem02AdaptiveHeadShapeGate.
    apply Nat.eqb_neq in Hc.
    now rewrite Hc.
  - apply fsem02AdaptiveServerBadHeadMasksResource; exact Hs.
  - unfold fsem02AdaptiveHeadShapeGate,
      fsem02AdaptiveShapeGatedPing.
    repeat rewrite Nat.eqb_refl.
    now rewrite Hrc.
  - unfold fsem02AdaptiveHeadShapeGate,
      fsem02AdaptiveShapeGatedPing,
      fsem02AdaptiveResourceShapeCheck.
    repeat rewrite Nat.eqb_refl.
    now rewrite Hrs.
Qed.

(* Concrete both-wrong-type instance of the polymorphic four-stage rule. *)
Theorem fsem02FourFaultTwoWrongTypes :
  forall client server ec es badClient badServer before,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      FSEM02NonEndpointResource FSEM02NonEndpointResource before =
        FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      FSEM02NonEndpointResource FSEM02NonEndpointResource before =
        FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      FSEM02NonEndpointResource FSEM02NonEndpointResource before =
        FSEM02ShapeMismatch client FSEM02WrongResourceType /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) FSEM02NonEndpointResource before =
        FSEM02ShapeMismatch server FSEM02WrongResourceType.
Proof.
  intros client server ec es badClient badServer before Hc Hs.
  apply fsem02FourFaultPreciseDiagnosticOrder; try assumption; reflexivity.
Qed.

(* Concrete both-wrong-session instance, requiring independently distinct
   resource heads rather than treating projected repair as resource repair. *)
Theorem fsem02FourFaultTwoWrongSessions :
  forall client server ec es badClient badServer wrongClient wrongServer before,
    ec <> badClient -> es <> badServer ->
    ec <> wrongClient -> es <> wrongServer ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      (FSEM02EndpointResource wrongClient)
      (FSEM02EndpointResource wrongServer) before =
        FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      (FSEM02EndpointResource wrongClient)
      (FSEM02EndpointResource wrongServer) before =
        FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource wrongClient)
      (FSEM02EndpointResource wrongServer) before =
        FSEM02ShapeMismatch client FSEM02WrongResourceSession /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec)
      (FSEM02EndpointResource wrongServer) before =
        FSEM02ShapeMismatch server FSEM02WrongResourceSession.
Proof.
  intros client server ec es badClient badServer
    wrongClient wrongServer before Hc Hs HrC HrS.
  apply fsem02FourFaultPreciseDiagnosticOrder; try assumption.
  - unfold fsem02AdaptiveResourceShapeCheck.
    apply Nat.eqb_neq in HrC.
    now rewrite HrC.
  - unfold fsem02AdaptiveResourceShapeCheck.
    apply Nat.eqb_neq in HrS.
    now rewrite HrS.
Qed.

(* At each rejected intermediate stage the gate cannot equal success. *)
Theorem fsem02FourFaultNoIntermediateSuccessor :
  forall client server ec es badClient badServer
         clientResource serverResource clientFault serverFault before after,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec clientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es serverResource = Some serverFault ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      clientResource serverResource before <> FSEM02HeadShapeStep (Some after) /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      clientResource serverResource before <> FSEM02HeadShapeStep (Some after) /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      clientResource serverResource before <> FSEM02HeadShapeStep (Some after) /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) serverResource before <>
        FSEM02HeadShapeStep (Some after).
Proof.
  intros client server ec es badClient badServer clientResource serverResource
    clientFault serverFault before after Hc Hs Hrc Hrs.
  pose proof (fsem02FourFaultPreciseDiagnosticOrder
    client server ec es badClient badServer clientResource serverResource
    clientFault serverFault before Hc Hs Hrc Hrs) as H.
  destruct H as [H1 [H2 [H3 H4]]].
  repeat split; intro Hstep.
  - rewrite H1 in Hstep; discriminate.
  - rewrite H2 in Hstep; discriminate.
  - rewrite H3 in Hstep; discriminate.
  - rewrite H4 in Hstep; discriminate.
Qed.

(* Full explicit repair permits exactly the already-authorized half-Close
   phase step, assuming the prior committed prefix and independent free pair. *)
Theorem fsem02FourFaultFullyRepairedHalfClose :
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
  exact (fsem02DualHeadResourceFullyRepairedHalfClose
    priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before Hcc Hcs Hsc Hss Hc Hs).
Qed.
