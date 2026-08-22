From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context.

(*
  Semantic model of the successful path through Phil.Core.Context.joinContinuing.

  Binding maps and loans retain the extensional representation used by Context.v.
  Unrestricted and linear agreement are pointwise.  Affine intersection is
  modeled name-by-name as the actual left fold: a candidate binding survives
  while every visited branch has exactly the same type; a missing binding drops
  the candidate permanently; a type mismatch has no successful constructor.
  This captures the implementation's important asymmetry: once a name has been
  dropped from the accumulated intersection, later differences at that name no
  longer matter.
*)

Definition EmptyBindingMap : BindingMap := fun _ => None.
Definition EmptyLoanSet : LoanSet := fun _ => false.

Definition emptyResourceContext : ResourceContext :=
  mkResourceContext EmptyBindingMap EmptyBindingMap EmptyBindingMap EmptyLoanSet.

Definition NoLoans (context : ResourceContext) : Prop :=
  forall name : Name, sharedLoans context name = false.

Definition SameBindingMap (left right : BindingMap) : Prop :=
  forall name : Name, left name = right name.

Definition SameUnrestricted (first other : ResourceContext) : Prop :=
  SameBindingMap (unrestrictedBindings first) (unrestrictedBindings other).

Definition SameLinear (first other : ResourceContext) : Prop :=
  SameBindingMap (linearBindings first) (linearBindings other).

Inductive AffineFoldAt (name : Name)
  : option Ty -> list ResourceContext -> option Ty -> Prop :=
| AffineFold_nil :
    forall current,
      AffineFoldAt name current [] current
| AffineFold_dropped :
    forall context rest,
      AffineFoldAt name None (context :: rest) None
| AffineFold_missing :
    forall ty context rest,
      affineBindings context name = None ->
      AffineFoldAt name (Some ty) (context :: rest) None
| AffineFold_same :
    forall ty context rest result,
      affineBindings context name = Some ty ->
      AffineFoldAt name (Some ty) rest result ->
      AffineFoldAt name (Some ty) (context :: rest) result.

Lemma affine_fold_some_implies_all_same :
  forall (name : Name)
         (initial result : option Ty)
         (rest : list ResourceContext),
    AffineFoldAt name initial rest result ->
    forall ty : Ty,
      result = Some ty ->
      initial = Some ty /\
      Forall (fun context => affineBindings context name = Some ty) rest.
Proof.
  intros name initial result rest Hfold.
  induction Hfold as
    [ current
    | context rest
    | currentTy context rest Hmissing
    | currentTy context rest result Hsame Hfold IH ];
    intros ty Hresult.
  - split.
    + exact Hresult.
    + constructor.
  - discriminate.
  - discriminate.
  - destruct (IH ty Hresult) as [Hcurrent Hall].
    inversion Hcurrent; subst.
    split.
    + reflexivity.
    + constructor; assumption.
Qed.

Lemma affine_fold_all_same_forces_result :
  forall (name : Name)
         (initial result : option Ty)
         (rest : list ResourceContext),
    AffineFoldAt name initial rest result ->
    forall ty : Ty,
      initial = Some ty ->
      Forall (fun context => affineBindings context name = Some ty) rest ->
      result = Some ty.
Proof.
  intros name initial result rest Hfold.
  induction Hfold as
    [ current
    | context rest
    | currentTy context rest Hmissing
    | currentTy context rest result Hsame Hfold IH ];
    intros ty Hinitial Hall.
  - exact Hinitial.
  - discriminate.
  - inversion Hinitial; subst currentTy.
    inversion Hall as [| head tail Hhead Htail]; subst.
    rewrite Hmissing in Hhead.
    discriminate.
  - inversion Hinitial; subst currentTy.
    inversion Hall as [| head tail Hhead Htail]; subst.
    apply IH with (ty := ty).
    + reflexivity.
    + exact Htail.
Qed.

Inductive ContextJoinSuccess : list ResourceContext -> ResourceContext -> Prop :=
| ContextJoin_empty :
    ContextJoinSuccess [] emptyResourceContext
| ContextJoin_nonempty :
    forall (first : ResourceContext)
           (rest : list ResourceContext)
           (joinedAffine : BindingMap),
      Forall NoLoans (first :: rest) ->
      Forall (SameUnrestricted first) rest ->
      Forall (SameLinear first) rest ->
      (forall name : Name,
        AffineFoldAt
          name
          (affineBindings first name)
          rest
          (joinedAffine name)) ->
      ContextJoinSuccess
        (first :: rest)
        (mkResourceContext
          (unrestrictedBindings first)
          joinedAffine
          (linearBindings first)
          EmptyLoanSet).

(* PHIL-CTX-JOIN-001: no continuing branch may carry a live loan. *)
Theorem context_join_inputs_have_no_loans :
  forall contexts joined,
    ContextJoinSuccess contexts joined ->
    Forall NoLoans contexts.
Proof.
  intros contexts joined Hjoin.
  destruct Hjoin.
  - constructor.
  - assumption.
Qed.

(* PHIL-CTX-JOIN-001: the joined context itself is loan-free. *)
Theorem context_join_output_has_no_loans :
  forall contexts joined,
    ContextJoinSuccess contexts joined ->
    NoLoans joined.
Proof.
  intros contexts joined Hjoin.
  destruct Hjoin; unfold NoLoans; intros name; reflexivity.
Qed.

(* PHIL-CTX-JOIN-001: every unrestricted branch view equals the joined view. *)
Theorem context_join_unrestricted_converges :
  forall contexts joined context,
    ContextJoinSuccess contexts joined ->
    In context contexts ->
    SameBindingMap
      (unrestrictedBindings joined)
      (unrestrictedBindings context).
Proof.
  intros contexts joined context Hjoin Hin.
  destruct Hjoin as
    [
    | first rest joinedAffine Hloans Hunrestricted Hlinear Haffine ].
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst context. unfold SameBindingMap. intro name. reflexivity.
    + apply Forall_forall with (x := context) in Hunrestricted.
      * exact Hunrestricted.
      * exact Hin.
Qed.

(* PHIL-CTX-JOIN-001: every linear branch view equals the joined view. *)
Theorem context_join_linear_converges :
  forall contexts joined context,
    ContextJoinSuccess contexts joined ->
    In context contexts ->
    SameBindingMap
      (linearBindings joined)
      (linearBindings context).
Proof.
  intros contexts joined context Hjoin Hin.
  destruct Hjoin as
    [
    | first rest joinedAffine Hloans Hunrestricted Hlinear Haffine ].
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst context. unfold SameBindingMap. intro name. reflexivity.
    + apply Forall_forall with (x := context) in Hlinear.
      * exact Hlinear.
      * exact Hin.
Qed.

(*
  PHIL-CTX-JOIN-001: a retained affine binding is exactly a binding retained at
  the same type by the first branch and every remaining branch.
*)
Theorem context_join_affine_some_exact :
  forall first rest joined name ty,
    ContextJoinSuccess (first :: rest) joined ->
    (affineBindings joined name = Some ty <->
      affineBindings first name = Some ty /\
      Forall (fun context => affineBindings context name = Some ty) rest).
Proof.
  intros first rest joined name ty Hjoin.
  inversion Hjoin; subst.
  simpl.
  split.
  - intro Hjoined.
    specialize (H5 name).
    eapply affine_fold_some_implies_all_same.
    + exact H5.
    + exact Hjoined.
  - intros [Hfirst Hall].
    specialize (H5 name).
    eapply affine_fold_all_same_forces_result.
    + exact H5.
    + exact Hfirst.
    + exact Hall.
Qed.

Corollary context_join_affine_retained_is_common :
  forall first rest joined name ty context,
    ContextJoinSuccess (first :: rest) joined ->
    affineBindings joined name = Some ty ->
    In context (first :: rest) ->
    affineBindings context name = Some ty.
Proof.
  intros first rest joined name ty context Hjoin Hjoined Hin.
  pose proof
    (proj1 (context_join_affine_some_exact first rest joined name ty Hjoin) Hjoined)
    as [Hfirst Hall].
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  - subst context. exact Hfirst.
  - apply Forall_forall with (x := context) in Hall.
    + exact Hall.
    + exact Hin.
Qed.
