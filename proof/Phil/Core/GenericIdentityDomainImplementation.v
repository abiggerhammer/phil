From Stdlib Require Import Lists.List Arith.PeanoNat.

Import ListNotations.

From Phil.Core Require Import
  GenericIdentity
  GenericInstantiationDomainImplementation.

(*
  PHIL-GEN-ID-IMPL-001, tranche A — executable semantic-argument domain.

  GenericIdentity.argumentDomainValid is exactly NoDup over semantic-argument
  keys. Reuse the already-extracted equality-parametric key-domain checker
  proved for generic instantiation rather than introducing a second duplicate
  checker. This theorem specializes that generic executable predicate back to
  the Certified PHIL-GEN-ID-001 model.
*)

Definition genericIdentityArgumentKeys
  (arguments : list SemanticArgument) : list nat :=
  map fst arguments.

Definition genericIdentityArgumentDomainb
  (arguments : list SemanticArgument) : bool :=
  keyListNoDupb Nat.eqb (genericIdentityArgumentKeys arguments).

Theorem generic_identity_argument_domainb_true_iff :
  forall arguments,
    genericIdentityArgumentDomainb arguments = true <->
    argumentDomainValid arguments.
Proof.
  intros arguments.
  unfold genericIdentityArgumentDomainb.
  unfold genericIdentityArgumentKeys.
  unfold argumentDomainValid.
  apply (@key_list_no_dupb_true_iff
    nat
    Nat.eqb
    Nat.eqb_eq
    (map fst arguments)).
Qed.

Theorem duplicate_generic_identity_argument_domain_rejects :
  forall key firstValue secondValue,
    genericIdentityArgumentDomainb
      [(key, firstValue); (key, secondValue)] = false.
Proof.
  intros key firstValue secondValue.
  unfold genericIdentityArgumentDomainb.
  unfold genericIdentityArgumentKeys.
  cbn.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem distinct_two_argument_orders_are_both_domain_valid :
  forall firstKey firstValue secondKey secondValue,
    firstKey <> secondKey ->
    genericIdentityArgumentDomainb
      [(firstKey, firstValue); (secondKey, secondValue)] = true /\
    genericIdentityArgumentDomainb
      [(secondKey, secondValue); (firstKey, firstValue)] = true.
Proof.
  intros firstKey firstValue secondKey secondValue Hdistinct.
  split;
    apply (proj2 (generic_identity_argument_domainb_true_iff _));
    unfold argumentDomainValid;
    cbn;
    constructor.
  - intro Hin.
    destruct Hin as [Heq | Hin].
    + apply Hdistinct.
      symmetry.
      exact Heq.
    + contradiction.
  - constructor.
    + intro Hin. contradiction.
    + constructor.
  - intro Hin.
    destruct Hin as [Heq | Hin].
    + apply Hdistinct.
      exact Heq.
    + contradiction.
  - constructor.
    + intro Hin. contradiction.
    + constructor.
Qed.
