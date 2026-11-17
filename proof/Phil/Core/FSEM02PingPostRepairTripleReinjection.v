From Phil.Core Require Import
  FSEM02PingFourFaultRepairOrderConfluence
  FSEM02PingAdaptiveDualHeadDualResourceLadder
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* Bounded, non-normative. Three observation sites are independently
   recontaminated AFTER full externally authorized repair. The four masks
   describe TEST interventions, not source transitions; nominal roles,
   activation, scheduler and terminal authority remain premises. *)
Theorem fsem02PostRepairTripleReinjectionExactPriority :
  forall client server ec es badClient badServer
         badClientResource badServerResource clientFault serverFault before,
    ec <> badClient ->
    es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec badClientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es badServerResource = Some serverFault ->
    (* Only Client head repaired: Server head is first remaining fault. *)
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource true false false false before =
       FSEM02HeadMismatch server es badServer) /\
    (* The other three triple faults all include the Client head. *)
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource false true false false before =
       FSEM02HeadMismatch client ec badClient) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource false false true false before =
       FSEM02HeadMismatch client ec badClient) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource false false false true before =
       FSEM02HeadMismatch client ec badClient) /\
    (* Six repair orders on each triple subset converge to this admitted
       all-true gate; it may still be blocked by external phase premises. *)
    fsem02FourRepairMaskGate client server ec es badClient badServer
      badClientResource badServerResource true true true true before =
      FSEM02HeadShapeStep (fsem02AdaptivePhaseJointPing client server before).
Proof.
  intros client server ec es badClient badServer
    badClientResource badServerResource clientFault serverFault before
    Hclient Hserver Hrc Hrs.
  repeat split;
    rewrite (fsem02FourRepairMaskExactPriority
      client server ec es badClient badServer
      badClientResource badServerResource clientFault serverFault before
      _ _ _ _ Hclient Hserver Hrc Hrs);
    reflexivity.
Qed.
