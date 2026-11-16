From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import
  SurfaceFiniteContextFrame SurfaceFiniteMixedJoinCorr6.

(*
  CORR-6: actual computed two-continuing-predecessor join SUCCESS
  implies the existing extensional Rocq ContextJoinSuccess relation.
  This is a proof about arbitrary finite/model contexts related by the
  canonical four-zone snapshot, NOT a global Haskell Map/Set theorem.
  Abstract Ty equality is supplied with an explicit iff-reflection LAW,
  not an admitted axiom or implicit trusted input.
*)

Module F := SurfaceFiniteContextFrame.
Module M := SurfaceFiniteMixedJoinCorr6.

Lemma corr6_affine_lookup_if_compatible :
  forall typeEq left right name,
    (forall a b, typeEq a b = true <-> a = b) ->
    NoDup (M.keys left) ->
    M.affineCompatible typeEq left right = true ->
    F.lookupFinite (M.affineIntersect typeEq left right) name =
      match F.lookupFinite left name, F.lookupFinite right name with
      | Some ty, Some _ => Some ty
      | _,_ => None
      end.
Proof.
  intros typeEq left right name Hreflect Hunique Hcompat.
  unfold M.affineIntersect.
  rewrite (M.lookup_filter_nodup left
    (M.affineKeep typeEq right) name Hunique).
  destruct (F.lookupFinite left name) as [ty|] eqn:Hleft;
    simpl; try reflexivity.
  destruct (F.lookupFinite right name) as [other|] eqn:Hright.
  - pose proof (M.affine_compatible_types
       typeEq left right Hcompat name ty Hleft) as Hsame.
    try rewrite Hright in Hsame.
    apply Hreflect in Hsame.
    subst other.
    unfold M.affineKeep.
    simpl.
    try rewrite Hright.
    try rewrite (proj2 (Hreflect ty ty) eq_refl).
    reflexivity.
  - unfold M.affineKeep. simpl. try rewrite Hright. reflexivity.
Qed.

Lemma corr6_successful_finite_affine_is_valid_model_fold :
  forall typeEq left right name,
    (forall a b, typeEq a b = true <-> a = b) ->
    NoDup (M.keys (F.finiteAffine left)) ->
    M.affineCompatible typeEq
      (F.finiteAffine left) (F.finiteAffine right) = true ->
    ContextJoin.AffineFoldAt name
      (F.lookupFinite (F.finiteAffine left) name)
      [F.reifyFinite right]
      (F.lookupFinite (M.affineIntersect typeEq
        (F.finiteAffine left) (F.finiteAffine right)) name).
Proof.
  intros typeEq left right name Hreflect Hunique Hcompatible.
  rewrite (corr6_affine_lookup_if_compatible
    typeEq (F.finiteAffine left) (F.finiteAffine right) name
    Hreflect Hunique Hcompatible).
  destruct (F.lookupFinite (F.finiteAffine left) name) as [ty|]
    eqn:Hleft.
  - destruct (F.lookupFinite (F.finiteAffine right) name) as [other|]
      eqn:Hright.
    + pose proof (M.affine_compatible_types
         typeEq (F.finiteAffine left) (F.finiteAffine right)
         Hcompatible name ty Hleft) as Hsame.
      rewrite Hright in Hsame.
      apply Hreflect in Hsame. subst other.
      apply ContextJoin.AffineFold_same.
      * simpl. exact Hright.
      * constructor.
    + apply ContextJoin.AffineFold_missing.
      simpl. exact Hright.
  - apply ContextJoin.AffineFold_dropped.
Qed.

Theorem corr6_computed_join_sound_for_extensional_core :
  forall typeEq left right joined,
    (forall a b, typeEq a b = true <-> a = b) ->
    NoDup (M.keys (F.finiteAffine left)) ->
    M.finiteJoin typeEq left right = M.JoinSuccess joined ->
    ContextJoin.ContextJoinSuccess
      [F.reifyFinite left; F.reifyFinite right]
      (F.reifyFinite joined).
Proof.
  intros typeEq left right joined Hreflect Hunique Hjoined.
  unfold M.finiteJoin in Hjoined.
  destruct (F.finiteLoans left) as [|l ls] eqn:HloansL;
    try discriminate.
  destruct (F.finiteLoans right) as [|r rs] eqn:HloansR;
    try discriminate.
  destruct (M.sameBindings typeEq
    (F.finiteUnrestricted left) (F.finiteUnrestricted right))
    eqn:HsameU; try discriminate.
  destruct (M.sameBindings typeEq
    (F.finiteLinear left) (F.finiteLinear right))
    eqn:HsameL; try discriminate.
  destruct (M.affineCompatible typeEq
    (F.finiteAffine left) (F.finiteAffine right))
    eqn:Haffine; try discriminate.
  inversion Hjoined; subst joined; clear Hjoined.
  cbn [F.reifyFinite F.finiteLoans F.finiteUnrestricted
    F.finiteAffine F.finiteLinear F.loanInFinite].
  apply ContextJoin.ContextJoin_nonempty.
  - constructor.
    + unfold ContextJoin.NoLoans.
      intros name. unfold F.reifyFinite. simpl.
      rewrite HloansL. reflexivity.
    + constructor.
      * unfold ContextJoin.NoLoans.
        intros name. unfold F.reifyFinite. simpl.
        rewrite HloansR. reflexivity.
      * constructor.
  - constructor.
    + unfold ContextJoin.SameUnrestricted, ContextJoin.SameBindingMap.
      intros name.
      eapply M.same_bindings_sound; eauto.
    + constructor.
  - constructor.
    + unfold ContextJoin.SameLinear, ContextJoin.SameBindingMap.
      intros name.
      eapply M.same_bindings_sound; eauto.
    + constructor.
  - intros name.
    apply corr6_successful_finite_affine_is_valid_model_fold;
      assumption.
Qed.

Print Assumptions corr6_affine_lookup_if_compatible.
Print Assumptions corr6_successful_finite_affine_is_valid_model_fold.
Print Assumptions corr6_computed_join_sound_for_extensional_core.
