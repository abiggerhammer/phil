From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  FSEM-01 J-1/J-2: bounded SOURCE-to-SCOPE-PROJECTION model.
  The admitted Haskell source fragment and checker operations supply exact
  before/raw/pruned contexts as independently tested finite evidence.
  These theorems establish conditional properties of the extensional Rocq
  ContextJoin model; no unchecked claim about native Map/Set/Text, nominal
  lifecycle attestations, or all Grammar-v1 source branches follows.
*)

(* The production pruneScopedPath rejects live linear locals. Affine and
   unrestricted locals may be removed. These propositions specify the model
   premises; the source driver checks the concrete production implementation. *)
Definition ScopedLinearPruneSafe
  (locals : list Name) (before : ResourceContext) : Prop :=
  forall owner,
    In owner locals ->
    linearBindings before owner = None.

Definition ScopedAffinePrune
  (locals : list Name)
  (before after : ResourceContext) : Prop :=
  (forall owner, In owner locals -> affineBindings after owner = None) /\
  (forall owner, ~ In owner locals ->
    affineBindings after owner = affineBindings before owner) /\
  (forall owner,
    linearBindings after owner = linearBindings before owner) /\
  (forall owner, sharedLoans after owner = sharedLoans before owner).

Theorem local_linear_owner_blocks_scope_exit :
  forall locals before owner ty,
    In owner locals ->
    linearBindings before owner = Some ty ->
    ~ ScopedLinearPruneSafe locals before.
Proof.
  intros locals before owner ty Hin Howned Hsafe.
  unfold ScopedLinearPruneSafe in Hsafe.
  specialize (Hsafe owner Hin).
  rewrite Howned in Hsafe.
  discriminate.
Qed.

Theorem affine_source_branch_without_owner_cannot_restore_it_at_join :
  forall left right joined owner,
    ContextJoinSuccess [left; right] joined ->
    affineBindings left owner = None ->
    affineBindings joined owner = None.
Proof.
  intros left right joined owner Hjoin Habsent.
  destruct (affineBindings joined owner) as [ty|] eqn:Hjoined.
  - pose proof
      (context_join_affine_retained_is_common
         left [right] joined owner ty left
         Hjoin Hjoined (or_introl eq_refl)) as Hleft.
    rewrite Habsent in Hleft.
    discriminate.
  - reflexivity.
Qed.

Theorem affine_source_other_branch_without_owner_cannot_restore_it_at_join :
  forall left right joined owner,
    ContextJoinSuccess [left; right] joined ->
    affineBindings right owner = None ->
    affineBindings joined owner = None.
Proof.
  intros left right joined owner Hjoin Habsent.
  destruct (affineBindings joined owner) as [ty|] eqn:Hjoined.
  - pose proof
      (context_join_affine_retained_is_common
        left [right] joined owner ty right
        Hjoin Hjoined (or_intror (or_introl eq_refl))) as Hright.
    rewrite Habsent in Hright.
    discriminate.
  - reflexivity.
Qed.

Theorem checked_scoped_local_affine_cannot_appear_in_join :
  forall locals before pruned other joined local,
    In local locals ->
    ScopedAffinePrune locals before pruned ->
    ContextJoinSuccess [pruned; other] joined ->
    affineBindings joined local = None.
Proof.
  intros locals before pruned other joined local Hin Hprune Hjoin.
  destruct Hprune as [Hlocal _].
  eapply affine_source_branch_without_owner_cannot_restore_it_at_join.
  - exact Hjoin.
  - apply Hlocal. exact Hin.
Qed.

Theorem affine_source_owner_kept_by_both_branches_is_retained :
  forall left right joined owner ty,
    ContextJoinSuccess [left; right] joined ->
    affineBindings left owner = Some ty ->
    affineBindings right owner = Some ty ->
    affineBindings joined owner = Some ty.
Proof.
  intros left right joined owner ty Hjoin Hleft Hright.
  apply
    (proj2 (context_join_affine_some_exact
      left [right] joined owner ty Hjoin)).
  split.
  - exact Hleft.
  - constructor.
    + exact Hright.
    + constructor.
Qed.

Theorem scoped_affine_prune_preserves_linear_spectator :
  forall locals before after owner,
    ScopedAffinePrune locals before after ->
    linearBindings after owner = linearBindings before owner.
Proof.
  intros locals before after owner Hprune.
  destruct Hprune as [_ [_ [Hlinear _]]].
  apply Hlinear.
Qed.

Theorem source_scoped_join_preserves_linear_spectator :
  forall left right joined owner,
    ContextJoinSuccess [left; right] joined ->
    linearBindings joined owner = linearBindings left owner /\
    linearBindings joined owner = linearBindings right owner.
Proof.
  intros left right joined owner Hjoin.
  split.
  - pose proof
      (context_join_linear_converges
        [left; right] joined left Hjoin
        (or_introl eq_refl)) as Hlinear.
    unfold SameBindingMap in Hlinear.
    exact (Hlinear owner).
  - pose proof
      (context_join_linear_converges
        [left; right] joined right Hjoin
        (or_intror (or_introl eq_refl))) as Hlinear.
    unfold SameBindingMap in Hlinear.
    exact (Hlinear owner).
Qed.

Theorem source_scoped_join_has_no_escaping_loan :
  forall left right joined,
    ContextJoinSuccess [left; right] joined ->
    NoLoans joined.
Proof.
  intros left right joined Hjoin.
  eapply context_join_output_has_no_loans.
  exact Hjoin.
Qed.

Print Assumptions local_linear_owner_blocks_scope_exit.
Print Assumptions affine_source_branch_without_owner_cannot_restore_it_at_join.
Print Assumptions affine_source_other_branch_without_owner_cannot_restore_it_at_join.
Print Assumptions checked_scoped_local_affine_cannot_appear_in_join.
Print Assumptions affine_source_owner_kept_by_both_branches_is_retained.
Print Assumptions scoped_affine_prune_preserves_linear_spectator.
Print Assumptions source_scoped_join_preserves_linear_spectator.
Print Assumptions source_scoped_join_has_no_escaping_loan.
