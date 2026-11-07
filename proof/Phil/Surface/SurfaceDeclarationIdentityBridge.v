From Stdlib Require Import
  Lists.List Strings.String Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import SurfaceBinderNameEncoding.

Import ListNotations.
Open Scope string_scope.

(*
  FSEM-01: a BOUNDED declaration-root identity representation bridge.

  The normalized BindingSemantics.DeclarationIdentity is nat, while a
  production Phil.Core.Static.DeclarationKey is Text.  Here a finite,
  explicitly ordered, duplicate-free catalog of Rocq strings gives a
  reversible relation between a catalog position and the root string.
  Catalog position is NOT a global/persisted production identity.

  The mapping is partial: absent roots and out-of-range positions do not
  represent declarations.  Unicode Text -> Rocq String correctness, catalog
  sourcing/immutability, and full declaration revision semantics are outside
  this proof.  No Axiom/Admitted is used.
*)

Fixpoint indexDeclarationRoot
  (root : string) (catalog : list string) : option nat :=
  match catalog with
  | [] => None
  | head :: tail =>
      if String.eqb root head then Some 0
      else option_map S (indexDeclarationRoot root tail)
  end.

Definition representsDeclarationRoot
  (catalog : list string) (normalized : DeclarationIdentity)
  (concreteRoot : string) : Prop :=
  nth_error catalog normalized = Some concreteRoot.

Lemma catalog_index_sound :
  forall catalog root position,
    indexDeclarationRoot root catalog = Some position ->
    representsDeclarationRoot catalog position root.
Proof.
  induction catalog as [|head tail IH]; intros root position H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (String.eqb root head) eqn:Heq.
    + inversion H; subst.
      unfold representsDeclarationRoot; simpl.
      apply String.eqb_eq in Heq; subst.
      reflexivity.
    + destruct (indexDeclarationRoot root tail) eqn:Htail;
        try discriminate.
      inversion H; subst.
      unfold representsDeclarationRoot; simpl.
      apply IH in Htail.
      exact Htail.
Qed.

Lemma catalog_index_complete :
  forall catalog root position,
    NoDup catalog ->
    representsDeclarationRoot catalog position root ->
    indexDeclarationRoot root catalog = Some position.
Proof.
  induction catalog as [|head tail IH]; intros root position Hnod Hnth.
  - unfold representsDeclarationRoot in Hnth.
    destruct position; discriminate.
  - inversion Hnod as [| ? ? Hnot HnodTail]; subst.
    destruct position as [|position].
    + unfold representsDeclarationRoot in Hnth; simpl in Hnth.
      inversion Hnth; subst.
      simpl. rewrite String.eqb_refl. reflexivity.
    + unfold representsDeclarationRoot in Hnth; simpl in Hnth.
      simpl.
      destruct (String.eqb root head) eqn:Heq.
      * apply String.eqb_eq in Heq; subst.
        exfalso.
        apply Hnot.
        eapply nth_error_In; eauto.
      * rewrite (IH root position HnodTail Hnth).
        reflexivity.
Qed.

Theorem catalog_position_roundtrip :
  forall catalog position root,
    NoDup catalog ->
    nth_error catalog position = Some root ->
    indexDeclarationRoot root catalog = Some position.
Proof.
  intros catalog position root Hnod H.
  apply catalog_index_complete; assumption.
Qed.

Theorem catalog_root_roundtrip :
  forall catalog root position,
    indexDeclarationRoot root catalog = Some position ->
    nth_error catalog position = Some root.
Proof.
  intros catalog root position H.
  exact (catalog_index_sound catalog root position H).
Qed.

Theorem distinct_catalog_positions_have_distinct_roots :
  forall catalog first second root,
    NoDup catalog ->
    nth_error catalog first = Some root ->
    nth_error catalog second = Some root ->
    first = second.
Proof.
  intros catalog first second root Hnod Hfirst Hsecond.
  pose proof (catalog_position_roundtrip catalog first root
                Hnod Hfirst) as HindexFirst.
  pose proof (catalog_position_roundtrip catalog second root
                Hnod Hsecond) as HindexSecond.
  rewrite HindexFirst in HindexSecond.
  now inversion HindexSecond.
Qed.

Definition representsBinderKey
  (catalog : list string)
  (normalized : BinderKey)
  (concrete : TextBinderKey) : Prop :=
  nth_error catalog (fst normalized) = Some (fst concrete) /\
  snd normalized = snd concrete.

Theorem represented_binder_encoding_preserves_exact_model_identity :
  forall catalog
    (first second : BinderKey)
    (firstConcrete secondConcrete : TextBinderKey),
    NoDup catalog ->
    representsBinderKey catalog first firstConcrete ->
    representsBinderKey catalog second secondConcrete ->
    encodeTextBinderKey firstConcrete =
      encodeTextBinderKey secondConcrete ->
    first = second.
Proof.
  intros catalog [firstDecl firstOrd] [secondDecl secondOrd]
    [firstRoot firstEncodedOrd] [secondRoot secondEncodedOrd]
    Hnod [HfirstRoot HfirstOrd] [HsecondRoot HsecondOrd] Hname.
  simpl in *.
  apply encode_text_binder_key_injective in Hname.
  inversion Hname; subst.
  pose proof (distinct_catalog_positions_have_distinct_roots
    catalog firstDecl secondDecl secondRoot
    Hnod HfirstRoot HsecondRoot) as Hdeclarations.
  subst.
  f_equal.
  congruence.
Qed.

Theorem represented_binder_root_lookup_is_exact :
  forall catalog normalized concrete,
    representsBinderKey catalog normalized concrete ->
    nth_error catalog (fst normalized) = Some (fst concrete).
Proof.
  intros catalog normalized concrete [Hroot _].
  exact Hroot.
Qed.

Example empty_catalog_has_no_declaration :
  indexDeclarationRoot "decl.A" [] = None.
Proof. reflexivity. Qed.

Example duplicate_roots_are_not_accepted_as_unique_catalog :
  ~ NoDup ["decl.A"; "decl.A"].
Proof.
  intro Hnod.
  inversion Hnod as [| ? ? Hnot _]; subst.
  apply Hnot. simpl. left. reflexivity.
Qed.

Example two_root_catalog_exact_identity :
  indexDeclarationRoot "decl.B" ["decl.A"; "decl.B"] = Some 1.
Proof. reflexivity. Qed.

(*
  What is NOT established:
   * a bijection between all Haskell Text values and all nat identities;
   * independence of catalog ordering or stability across catalog revisions;
   * translation of arbitrary Unicode Text into Rocq's ASCII-string carrier;
   * equality of complete DeclarationIdentity revisions or runtime objects;
   * any Haskell-to-Rocq compiler/resource-transition simulation.
*)
