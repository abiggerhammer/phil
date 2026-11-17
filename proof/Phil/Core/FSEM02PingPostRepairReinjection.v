From Phil.Core Require Import
  FSEM02PingFourFaultRepairOrderConfluence
  FSEM02PingAdaptiveDualHeadDualResourceLadder
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* Non-normative FSEM-02: a single externally reintroduced fault after
   all-four-site restoration cannot authorize a successor. Repair is a test
   intervention; the restored joint step remains separately admitted. *)
Theorem fsem02PostRepairOneSiteReinjectionRefusesAndRestores :
  forall client server ec es badClient badServer
         badClientResource badServerResource clientFault serverFault before,
    ec <> badClient ->
    es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec badClientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es badServerResource = Some serverFault ->
    (forall after,
      fsem02FourRepairMaskGate client server ec es badClient badServer
        badClientResource badServerResource false true true true before
        <> FSEM02HeadShapeStep (Some after) /\
      fsem02FourRepairMaskGate client server ec es badClient badServer
        badClientResource badServerResource true false true true before
        <> FSEM02HeadShapeStep (Some after) /\
      fsem02FourRepairMaskGate client server ec es badClient badServer
        badClientResource badServerResource true true false true before
        <> FSEM02HeadShapeStep (Some after) /\
      fsem02FourRepairMaskGate client server ec es badClient badServer
        badClientResource badServerResource true true true false before
        <> FSEM02HeadShapeStep (Some after)) /\
    fsem02FourRepairMaskGate client server ec es badClient badServer
      badClientResource badServerResource true true true true before =
      FSEM02HeadShapeStep (fsem02AdaptivePhaseJointPing client server before).
Proof.
  intros client server ec es badClient badServer
    badClientResource badServerResource clientFault serverFault before
    Hclient Hserver Hrc Hrs.
  split.
  - intros after.
    repeat split;
      eapply fsem02IncompleteRepairMaskCannotStep;
      try eassumption; reflexivity.
  - rewrite (fsem02FourRepairMaskExactPriority
      client server ec es badClient badServer
      badClientResource badServerResource clientFault serverFault before
      true true true true Hclient Hserver Hrc Hrs).
    reflexivity.
Qed.
