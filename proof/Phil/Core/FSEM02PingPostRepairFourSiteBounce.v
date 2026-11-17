From Phil.Core Require Import
  FSEM02PingFourFaultRepairOrderConfluence
  FSEM02PingAdaptiveDualHeadDualResourceLadder
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* Four observation sites are restored and then externally recontaminated.
   After repairing any ONE site, a second external recontamination of that
   site restores the original all-fault mask. These interventions are not
   Phil source steps and do not grant authority. *)
Inductive fsem02BounceSite : Type :=
| FSEM02BounceClientHead
| FSEM02BounceServerHead
| FSEM02BounceClientResource
| FSEM02BounceServerResource.

Definition fsem02FirstSiteRepaired (site : fsem02BounceSite)
  : bool * bool * bool * bool :=
  match site with
  | FSEM02BounceClientHead => (true, false, false, false)
  | FSEM02BounceServerHead => (false, true, false, false)
  | FSEM02BounceClientResource => (false, false, true, false)
  | FSEM02BounceServerResource => (false, false, false, true)
  end.

Definition fsem02RecontaminateOne
  (site : fsem02BounceSite) (mask : bool * bool * bool * bool)
  : bool * bool * bool * bool :=
  let '(ch, sh, cr, sr) := mask in
  match site with
  | FSEM02BounceClientHead => (false, sh, cr, sr)
  | FSEM02BounceServerHead => (ch, false, cr, sr)
  | FSEM02BounceClientResource => (ch, sh, false, sr)
  | FSEM02BounceServerResource => (ch, sh, cr, false)
  end.

Theorem fsem02FirstRepairRecontaminationRestoresFullFaultMask :
  forall site,
    fsem02RecontaminateOne site (fsem02FirstSiteRepaired site) =
    (false, false, false, false).
Proof.
  destruct site; reflexivity.
Qed.

(* Conditional exact first-fault refusal after the bounce, and a separate
   already-authorized result after four complete repairs. The finite mask
   model is NOT universal Haskell-to-Rocq implementation refinement. *)
Theorem fsem02PostRepairFourSiteBounceRefusesAndRestores :
  forall client server ec es badClient badServer
         badClientResource badServerResource clientFault serverFault before
         firstSite,
    ec <> badClient ->
    es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec badClientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es badServerResource = Some serverFault ->
    let '(ch, sh, cr, sr) :=
      fsem02RecontaminateOne firstSite (fsem02FirstSiteRepaired firstSite) in
    fsem02FourRepairMaskGate client server ec es badClient badServer
      badClientResource badServerResource ch sh cr sr before =
      FSEM02HeadMismatch client ec badClient /\
    fsem02FourRepairMaskGate client server ec es badClient badServer
      badClientResource badServerResource true true true true before =
      FSEM02HeadShapeStep (fsem02AdaptivePhaseJointPing client server before).
Proof.
  intros client server ec es badClient badServer
    badClientResource badServerResource clientFault serverFault before
    firstSite Hclient Hserver Hrc Hrs.
  destruct firstSite; simpl; split;
    rewrite (fsem02FourRepairMaskExactPriority
      client server ec es badClient badServer
      badClientResource badServerResource clientFault serverFault before
      _ _ _ _ Hclient Hserver Hrc Hrs);
    reflexivity.
Qed.
