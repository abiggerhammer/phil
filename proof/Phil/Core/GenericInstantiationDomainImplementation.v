From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.

Import ListNotations.

From Phil.Core Require Import GenericStructural GenericInstantiation.

(*
  PHIL-GEN-INST-IMPL-001, tranche A — executable exact disposition domain.

  The certified PHIL-GEN-INST-001 model states exactDispositionDomain over
  GenericRequirement identities.  Production identities are richer than the
  normalized proof atoms, so this implementation layer factors the domain
  algorithm over an arbitrary key type plus an equality test.  The generic
  theorem requires only that the supplied equality test reflect actual key
  equality.  A specialization then proves equivalence to the certified
  GenericRequirement exactDispositionDomain relation.
*)

Section ExactKeyDomain.

Context {Key : Type}.
Variable keyEqb : Key -> Key -> bool.

Definition keyIn (needle : Key) (haystack : list Key) : bool :=
  existsb (keyEqb needle) haystack.

Fixpoint keyListNoDupb (keys : list Key) : bool :=
  match keys with
  | [] => true
  | key :: rest =>
      andb (negb (keyIn key rest)) (keyListNoDupb rest)
  end.

Fixpoint allKeysInb (required available : list Key) : bool :=
  match required with
  | [] => true
  | key :: rest =>
      andb (keyIn key available) (allKeysInb rest available)
  end.

Definition exactKeyDomainb
  (requirements dispositionKeys : list Key) : bool :=
  andb
    (keyListNoDupb dispositionKeys)
    (andb
      (allKeysInb requirements dispositionKeys)
      (allKeysInb dispositionKeys requirements)).

Variable keyEqb_spec :
  forall left right, keyEqb left right = true <-> left = right.

Lemma key_in_true_iff :
  forall needle haystack,
    keyIn needle haystack = true <-> In needle haystack.
Proof.
  intros needle haystack.
  induction haystack as [| head rest IH]; cbn.
  - split.
    + intro H. discriminate.
    + intro H. contradiction.
  - rewrite Bool.orb_true_iff.
    split.
    + intros [Hhead | Hrest].
      * apply keyEqb_spec in Hhead.
        subst head.
        left.
        reflexivity.
      * right.
        apply (proj1 IH).
        exact Hrest.
    + intros [Hhead | Hrest].
      * subst head.
        left.
        apply (proj2 (keyEqb_spec needle needle)).
        reflexivity.
      * right.
        apply (proj2 IH).
        exact Hrest.
Qed.

Lemma key_in_false_iff :
  forall needle haystack,
    keyIn needle haystack = false <-> ~ In needle haystack.
Proof.
  intros needle haystack.
  split.
  - intros Hfalse Hin.
    apply (proj2 (key_in_true_iff needle haystack)) in Hin.
    rewrite Hfalse in Hin.
    discriminate.
  - intro Hnotin.
    destruct (keyIn needle haystack) eqn:Hmember.
    + exfalso.
      apply Hnotin.
      apply (proj1 (key_in_true_iff needle haystack)).
      exact Hmember.
    + reflexivity.
Qed.

Lemma key_list_no_dupb_true_iff :
  forall keys,
    keyListNoDupb keys = true <-> NoDup keys.
Proof.
  intros keys.
  induction keys as [| head rest IH]; cbn.
  - split.
    + intro Hempty. constructor.
    + intro Hnodup. reflexivity.
  - rewrite Bool.andb_true_iff.
    rewrite Bool.negb_true_iff.
    rewrite key_in_false_iff.
    rewrite IH.
    split.
    + intros [Hnotin Hnodup].
      constructor; assumption.
    + intro Hnodup.
      inversion Hnodup as [| ? ? Hnotin Htail].
      subst.
      split; assumption.
Qed.

Lemma all_keys_inb_true_iff :
  forall required available,
    allKeysInb required available = true <->
    forall key, In key required -> In key available.
Proof.
  intros required available.
  induction required as [| head rest IH]; cbn.
  - split.
    + intros Hempty key Hin. contradiction.
    + intro Hall. reflexivity.
  - rewrite Bool.andb_true_iff.
    split.
    + intros [Hhead Hrest] key Hin.
      destruct Hin as [Heq | Hin].
      * subst key.
        apply (proj1 (key_in_true_iff head available)).
        exact Hhead.
      * apply (proj1 IH Hrest).
        exact Hin.
    + intro Hall.
      split.
      * apply (proj2 (key_in_true_iff head available)).
        apply Hall.
        left.
        reflexivity.
      * apply (proj2 IH).
        intros key Hin.
        apply Hall.
        right.
        exact Hin.
Qed.

Theorem exact_key_domainb_true_iff :
  forall requirements dispositionKeys,
    exactKeyDomainb requirements dispositionKeys = true <->
    NoDup dispositionKeys /\
    (forall requirement,
      In requirement requirements -> In requirement dispositionKeys) /\
    (forall requirement,
      In requirement dispositionKeys -> In requirement requirements).
Proof.
  intros requirements dispositionKeys.
  unfold exactKeyDomainb.
  rewrite Bool.andb_true_iff.
  rewrite Bool.andb_true_iff.
  rewrite key_list_no_dupb_true_iff.
  rewrite all_keys_inb_true_iff.
  rewrite all_keys_inb_true_iff.
  reflexivity.
Qed.

End ExactKeyDomain.

Inductive GenericDispositionDomainDecision : Type :=
| GenericDispositionDomainAccepted
| GenericDispositionDomainRejected.

Definition decideExactKeyDomain
  {Key : Type}
  (keyEqb : Key -> Key -> bool)
  (requirements dispositionKeys : list Key)
  : GenericDispositionDomainDecision :=
  if exactKeyDomainb keyEqb requirements dispositionKeys
  then GenericDispositionDomainAccepted
  else GenericDispositionDomainRejected.

Definition structuralPermissionEqb
  (left right : StructuralPermission) : bool :=
  match left, right with
  | WeakeningPermission, WeakeningPermission => true
  | ContractionPermission, ContractionPermission => true
  | _, _ => false
  end.

Lemma structural_permission_eqb_true_iff :
  forall left right,
    structuralPermissionEqb left right = true <-> left = right.
Proof.
  intros left right.
  destruct left, right; cbn; split; intro H;
    try reflexivity; try discriminate.
Qed.

Definition genericRequirementEqb
  (left right : GenericRequirement) : bool :=
  match left, right with
  | StructuralRequirement leftPermission,
      StructuralRequirement rightPermission =>
      structuralPermissionEqb leftPermission rightPermission
  | ProviderRequirement leftInterface,
      ProviderRequirement rightInterface =>
      Nat.eqb leftInterface rightInterface
  | PropositionRequirement leftProposition,
      PropositionRequirement rightProposition =>
      Nat.eqb leftProposition rightProposition
  | _, _ => false
  end.

Lemma generic_requirement_eqb_true_iff :
  forall left right,
    genericRequirementEqb left right = true <-> left = right.
Proof.
  intros left right.
  destruct left as [leftPermission | leftInterface | leftProposition];
    destruct right as [rightPermission | rightInterface | rightProposition]; cbn.
  - destruct leftPermission, rightPermission; cbn; split; intro H;
      try reflexivity; discriminate.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split.
    + intro H.
      apply Nat.eqb_eq in H.
      subst rightInterface.
      reflexivity.
    + intro H.
      inversion H.
      apply Nat.eqb_refl.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split.
    + intro H.
      apply Nat.eqb_eq in H.
      subst rightProposition.
      reflexivity.
    + intro H.
      inversion H.
      apply Nat.eqb_refl.
Qed.

Lemma in_disposition_keys_iff :
  forall requirement dispositions,
    In requirement (map fst dispositions) <->
    exists disposition, In (requirement, disposition) dispositions.
Proof.
  intros requirement dispositions.
  induction dispositions as [| [key disposition] rest IH]; cbn.
  - split.
    + intro H. contradiction.
    + intros [found H]. contradiction.
  - split.
    + intro H.
      destruct H as [Hhead | Hrest].
      * subst key.
        exists disposition.
        left.
        reflexivity.
      * apply IH in Hrest.
        destruct Hrest as [found Hfound].
        exists found.
        right.
        exact Hfound.
    + intros [found Hfound].
      destruct Hfound as [Hhead | Hrest].
      * inversion Hhead.
        left.
        reflexivity.
      * right.
        apply IH.
        exists found.
        exact Hrest.
Qed.

Definition exactDispositionDomainb
  (requirements : list GenericRequirement)
  (dispositions : list (GenericRequirement * GenericRequirementDisposition))
  : bool :=
  exactKeyDomainb genericRequirementEqb requirements (map fst dispositions).

Theorem exact_disposition_domainb_true_iff :
  forall requirements dispositions,
    exactDispositionDomainb requirements dispositions = true <->
    exactDispositionDomain requirements dispositions.
Proof.
  intros requirements dispositions.
  unfold exactDispositionDomainb.
  pose proof
    (@exact_key_domainb_true_iff
      GenericRequirement
      genericRequirementEqb
      generic_requirement_eqb_true_iff
      requirements
      (map fst dispositions)) as Hdomain.
  rewrite Hdomain.
  unfold exactDispositionDomain.
  split.
  - intros [Hnodup [Hcomplete Hexposed]].
    split.
    + exact Hnodup.
    + split.
      * intros requirement Hin.
        apply (proj1 (in_disposition_keys_iff requirement dispositions)).
        apply Hcomplete.
        exact Hin.
      * intros requirement disposition Hin.
        apply Hexposed.
        apply (proj2 (in_disposition_keys_iff requirement dispositions)).
        exists disposition.
        exact Hin.
  - intros [Hnodup [Hcomplete Hexposed]].
    split.
    + exact Hnodup.
    + split.
      * intros requirement Hin.
        apply (proj2 (in_disposition_keys_iff requirement dispositions)).
        apply Hcomplete.
        exact Hin.
      * intros requirement Hin.
        apply (proj1 (in_disposition_keys_iff requirement dispositions)) in Hin.
        destruct Hin as [disposition Hdisposition].
        apply (Hexposed requirement disposition).
        exact Hdisposition.
Qed.

Theorem generic_instantiation_domain_decision_accept_iff :
  forall requirements dispositions,
    decideExactKeyDomain
      genericRequirementEqb
      requirements
      (map fst dispositions) = GenericDispositionDomainAccepted <->
    exactDispositionDomain requirements dispositions.
Proof.
  intros requirements dispositions.
  unfold decideExactKeyDomain.
  destruct
    (exactKeyDomainb genericRequirementEqb requirements (map fst dispositions))
    eqn:Hdomain; cbn.
  - split.
    + intro Haccepted.
      apply (proj1 (exact_disposition_domainb_true_iff requirements dispositions)).
      exact Hdomain.
    + intro Hexact.
      reflexivity.
  - split.
    + intro H. discriminate.
    + intro Hexact.
      apply (proj2 (exact_disposition_domainb_true_iff requirements dispositions))
        in Hexact.
      unfold exactDispositionDomainb in Hexact.
      rewrite Hdomain in Hexact.
      discriminate.
Qed.

Theorem generic_instantiation_domain_decision_reject_iff :
  forall requirements dispositions,
    decideExactKeyDomain
      genericRequirementEqb
      requirements
      (map fst dispositions) = GenericDispositionDomainRejected <->
    ~ exactDispositionDomain requirements dispositions.
Proof.
  intros requirements dispositions.
  unfold decideExactKeyDomain.
  destruct
    (exactKeyDomainb genericRequirementEqb requirements (map fst dispositions))
    eqn:Hdomain; cbn.
  - split.
    + intro H. discriminate.
    + intro Hnot.
      exfalso.
      apply Hnot.
      apply (proj1 (exact_disposition_domainb_true_iff requirements dispositions)).
      exact Hdomain.
  - split.
    + intros Hrejected Hexact.
      apply (proj2 (exact_disposition_domainb_true_iff requirements dispositions))
        in Hexact.
      unfold exactDispositionDomainb in Hexact.
      rewrite Hdomain in Hexact.
      discriminate.
    + intro Hnot.
      reflexivity.
Qed.
