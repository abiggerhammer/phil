From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat.
Import ListNotations.

(*
  PHIL-PROV-QUAL-IMPL-001 — reusable finite association-list bridge.

  Production Map values are projected to canonical finite association lists and
  checked for round-trip equality on the Haskell side.  These extracted helpers
  own exact key-domain comparison, lookup, and universal finite traversal.
*)

Fixpoint sameKeyDomainb {Key A B : Type}
  (eqKey : Key -> Key -> bool)
  (first : list (Key * A))
  (second : list (Key * B)) : bool :=
  match first, second with
  | nil, nil => true
  | (firstKey, _) :: firstRest, (secondKey, _) :: secondRest =>
      eqKey firstKey secondKey && sameKeyDomainb eqKey firstRest secondRest
  | _, _ => false
  end.

Fixpoint lookupAssoc {Key A : Type}
  (eqKey : Key -> Key -> bool)
  (key : Key)
  (entries : list (Key * A)) : option A :=
  match entries with
  | nil => None
  | (entryKey, value) :: rest =>
      if eqKey key entryKey then Some value else lookupAssoc eqKey key rest
  end.

Fixpoint allFiniteb {A : Type}
  (predicate : A -> bool)
  (values : list A) : bool :=
  match values with
  | nil => true
  | value :: rest => predicate value && allFiniteb predicate rest
  end.

Definition keysOf {Key A : Type} (entries : list (Key * A)) : list Key :=
  map fst entries.

Lemma all_finiteb_true_iff :
  forall (A : Type) (predicate : A -> bool) (values : list A),
    allFiniteb predicate values = true <->
    Forall (fun value => predicate value = true) values.
Proof.
  intros A predicate values.
  induction values as [| value rest IH].
  - cbn. split; intro H; constructor.
  - cbn. rewrite andb_true_iff, IH.
    split.
    + intros [Hvalue Hrest]. constructor; assumption.
    + intro Hall. inversion Hall; subst. split; assumption.
Qed.

Theorem same_key_domainb_true_implies_equal_length :
  forall (Key A B : Type)
      (eqKey : Key -> Key -> bool)
      (first : list (Key * A))
      (second : list (Key * B)),
    sameKeyDomainb eqKey first second = true ->
    length first = length second.
Proof.
  intros Key A B eqKey first.
  induction first as [| [firstKey firstValue] firstRest IH]; intros second Hsame.
  - destruct second; cbn in Hsame; try discriminate; reflexivity.
  - destruct second as [| [secondKey secondValue] secondRest]; cbn in Hsame;
      try discriminate.
    apply andb_true_iff in Hsame as [_ Hrest].
    cbn. f_equal. eapply IH. exact Hrest.
Qed.

Theorem same_key_domainb_true_implies_pairwise_keys :
  forall (Key A B : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (first : list (Key * A)) (second : list (Key * B)),
      sameKeyDomainb eqKey first second = true ->
      keysOf first = keysOf second.
Proof.
  intros Key A B eqKey Heq first.
  induction first as [| [firstKey firstValue] firstRest IH]; intros second Hsame.
  - destruct second; cbn in Hsame; try discriminate; reflexivity.
  - destruct second as [| [secondKey secondValue] secondRest]; cbn in Hsame;
      try discriminate.
    apply andb_true_iff in Hsame as [Hkey Hrest].
    apply (proj1 (Heq firstKey secondKey)) in Hkey.
    subst secondKey.
    unfold keysOf in *; cbn.
    f_equal. eapply IH. exact Hrest.
Qed.

Theorem equal_pairwise_keys_imply_same_key_domainb :
  forall (Key A B : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (first : list (Key * A)) (second : list (Key * B)),
      keysOf first = keysOf second ->
      sameKeyDomainb eqKey first second = true.
Proof.
  intros Key A B eqKey Heq first.
  induction first as [| [firstKey firstValue] firstRest IH]; intros second Hkeys.
  - destruct second.
    + reflexivity.
    + discriminate Hkeys.
  - destruct second as [| [secondKey secondValue] secondRest].
    + discriminate Hkeys.
    + unfold keysOf in Hkeys; cbn in Hkeys.
      inversion Hkeys as [Hhead Htail].
      cbn.
      apply andb_true_iff. split.
      * apply (proj2 (Heq firstKey secondKey)). exact Hhead.
      * apply IH. exact Htail.
Qed.

Theorem same_key_domainb_true_iff_keys_equal :
  forall (Key A B : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (first : list (Key * A)) (second : list (Key * B)),
      sameKeyDomainb eqKey first second = true <->
      keysOf first = keysOf second.
Proof.
  intros Key A B eqKey Heq first second.
  split.
  - apply same_key_domainb_true_implies_pairwise_keys. exact Heq.
  - apply equal_pairwise_keys_imply_same_key_domainb. exact Heq.
Qed.

Theorem lookup_assoc_some_is_member :
  forall (Key A : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (key : Key) (entries : list (Key * A)) (value : A),
      lookupAssoc eqKey key entries = Some value ->
      In (key, value) entries.
Proof.
  intros Key A eqKey Heq key entries.
  induction entries as [| [entryKey entryValue] rest IH]; intros value Hlookup.
  - discriminate.
  - cbn in Hlookup.
    destruct (eqKey key entryKey) eqn:Hkey.
    + inversion Hlookup; subst value.
      apply (proj1 (Heq key entryKey)) in Hkey. subst entryKey.
      left. reflexivity.
    + right. apply IH. exact Hlookup.
Qed.

Theorem member_with_unique_key_is_lookup_result :
  forall (Key A : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (key : Key) (value : A) (entries : list (Key * A)),
      NoDup (keysOf entries) ->
      In (key, value) entries ->
      lookupAssoc eqKey key entries = Some value.
Proof.
  intros Key A eqKey Heq key value entries Hunique Hin.
  induction entries as [| [entryKey entryValue] rest IH].
  - contradiction.
  - inversion Hunique as [| head tail Hnotin Htail].
    destruct Hin as [Hhead | Hrest].
    + inversion Hhead; subst entryKey entryValue.
      cbn. rewrite (proj2 (Heq key key) eq_refl). reflexivity.
    + cbn.
      destruct (eqKey key entryKey) eqn:Hkey.
      * apply (proj1 (Heq key entryKey)) in Hkey. subst entryKey.
        exfalso. apply Hnotin.
        unfold keysOf. apply in_map. exact Hrest.
      * apply IH; assumption.
Qed.
