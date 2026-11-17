From Phil.Core Require Import FSEM02PingPostRepairFourSiteBounce.

(* Test-environment observation repair, NOT a Phil source transition.
   Nominal instance, activation, terminal, scheduler and assurance authority
   remain independent external premises. *)
Definition fsem02RepairObservation
  (site : fsem02BounceSite) (mask : bool * bool * bool * bool)
  : bool * bool * bool * bool :=
  let '(ch, sh, cr, sr) := mask in
  match site with
  | FSEM02BounceClientHead => (true, sh, cr, sr)
  | FSEM02BounceServerHead => (ch, true, cr, sr)
  | FSEM02BounceClientResource => (ch, sh, true, sr)
  | FSEM02BounceServerResource => (ch, sh, cr, true)
  end.

(* For every partial four-site mask, same-site repair and corruption absorb
   each other; repeated corruption is idempotent. *)
Theorem fsem02PartialMaskSiteReversibility :
  forall site mask,
    fsem02RepairObservation site (fsem02RecontaminateOne site mask) =
      fsem02RepairObservation site mask /\
    fsem02RecontaminateOne site (fsem02RepairObservation site mask) =
      fsem02RecontaminateOne site mask /\
    fsem02RecontaminateOne site (fsem02RecontaminateOne site mask) =
      fsem02RecontaminateOne site mask.
Proof.
  intros site mask.
  destruct mask as [ch tail].
  destruct tail as [sh tail].
  destruct tail as [cr sr].
  destruct site; simpl; repeat split; reflexivity.
Qed.

(* Different observation sites do not mask each other's faults.
   This finite algebra is not universal native-Haskell/Rocq refinement. *)
Theorem fsem02DisjointObservationRepairCommutesWithReinjection :
  forall repairedSite corruptedSite mask,
    repairedSite <> corruptedSite ->
    fsem02RepairObservation repairedSite
      (fsem02RecontaminateOne corruptedSite mask) =
    fsem02RecontaminateOne corruptedSite
      (fsem02RepairObservation repairedSite mask).
Proof.
  intros repairedSite corruptedSite mask Hneq.
  destruct mask as [ch tail].
  destruct tail as [sh tail].
  destruct tail as [cr sr].
  destruct repairedSite, corruptedSite; try congruence; reflexivity.
Qed.
