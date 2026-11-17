From Phil.Core Require Import
  FSEM02PingFourFaultRepairOrderConfluence
  FSEM02PingAdaptiveDualHeadDualResourceLadder
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* Bounded, non-normative: after an externally authorized full repair,
   two independent observations may be corrupted again. These boolean
   masks describe TEST interventions, not source operational transitions.
   Diagnostic authority remains the admitted four-site gate. *)
Theorem fsem02PostRepairPairedReinjectionExactPriority :
  forall client server ec es badClient badServer
         badClientResource badServerResource clientFault serverFault before,
    ec <> badClient ->
    es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec badClientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es badServerResource = Some serverFault ->
    (* Six unordered pairs of newly corrupted sites, in canonical
       Client-head, Server-head, Client-resource, Server-resource order. *)
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource false false true true before =
       FSEM02HeadMismatch client ec badClient) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource false true false true before =
       FSEM02HeadMismatch client ec badClient) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource false true true false before =
       FSEM02HeadMismatch client ec badClient) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource true false false true before =
       FSEM02HeadMismatch server es badServer) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource true false true false before =
       FSEM02HeadMismatch server es badServer) /\
    (fsem02FourRepairMaskGate client server ec es badClient badServer
       badClientResource badServerResource true true false false before =
       FSEM02ShapeMismatch client clientFault) /\
    (* Both orders of external repair restore the same final mask,
       which exposes only the previously admitted joint phase result. *)
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
