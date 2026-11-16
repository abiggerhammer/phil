From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import SurfaceFiniteContextFrame.

(*
  FSEM-01 CORR-6: computed two-continuing-predecessor finite U/A/L/loan
  join, preserving the actual Core.Context.joinContinuing order:
  active loan refusal; U disagreement; L disagreement; first-branch
  affine intersection/type conflict. A missing first-branch affine
  owner cannot be resurrected by the second predecessor.

  Syntax.Ty is ABSTRACT. Its equality function must be supplied with a
  proven reflectance law: Haskell Type equality is NOT a new Rocq axiom.
  No source parser, Haskell Map/Set or general compiler correspondence
  is claimed by this model.
*)

Module F := SurfaceFiniteContextFrame.

Definition keys (entries : list (Syntax.Name * Syntax.Ty))
  : list Syntax.Name := map fst entries.

Lemma absent_key_has_no_lookup :
  forall entries key,
    ~ In key (keys entries) -> F.lookupFinite entries key = None.
Proof.
  induction entries as [|[name ty] rest IH]; intros key Hnot.
  - reflexivity.
  - simpl in *.
    assert (Hneq : key <> name).
    { intro Hsame. apply Hnot. left. now symmetry. }
    apply String.eqb_neq in Hneq.
    rewrite Hneq.
    apply IH.
    intro Hin. apply Hnot. now right.
Qed.

Definition optionTyEq (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (left right : option Syntax.Ty) : bool :=
  match left,right with
  | None,None => true
  | Some a,Some b => typeEq a b
  | _,_ => false
  end.

Lemma option_eq_true_is_equal :
  forall typeEq,
    (forall a b, typeEq a b = true <-> a = b) ->
    forall left right,
      optionTyEq typeEq left right = true -> left = right.
Proof.
  intros typeEq Htype [a|] [b|] H; simpl in H;
    try discriminate; try reflexivity.
  apply Htype in H. now subst.
Qed.

Lemma option_eq_equal_is_true :
  forall typeEq,
    (forall a b, typeEq a b = true <-> a = b) ->
    forall value, optionTyEq typeEq value value = true.
Proof.
  intros typeEq Htype [a|]; simpl; try reflexivity.
  now apply Htype.
Qed.

Definition sameBindings (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (left right : list (Syntax.Name * Syntax.Ty)) : bool :=
  forallb
    (fun name => optionTyEq typeEq
      (F.lookupFinite left name) (F.lookupFinite right name))
    (keys left ++ keys right).

Lemma same_bindings_sound :
  forall typeEq left right,
    (forall a b, typeEq a b = true <-> a = b) ->
    sameBindings typeEq left right = true ->
    forall name, F.lookupFinite left name = F.lookupFinite right name.
Proof.
  intros typeEq left right Htype Hsame name.
  unfold sameBindings in Hsame.
  destruct (in_dec string_dec name (keys left ++ keys right)) as [Hin|Hout].
  - apply forallb_forall with (x := name) in Hsame; auto.
    now apply option_eq_true_is_equal with (typeEq := typeEq).
  - assert (Hleft : ~ In name (keys left)).
    { intro H. apply Hout. apply in_or_app. now left. }
    assert (Hright : ~ In name (keys right)).
    { intro H. apply Hout. apply in_or_app. now right. }
    rewrite (absent_key_has_no_lookup left name Hleft).
    rewrite (absent_key_has_no_lookup right name Hright).
    reflexivity.
Qed.

Lemma same_bindings_complete :
  forall typeEq left right,
    (forall a b, typeEq a b = true <-> a = b) ->
    (forall name, F.lookupFinite left name = F.lookupFinite right name) ->
    sameBindings typeEq left right = true.
Proof.
  intros typeEq left right Htype Hlookup.
  unfold sameBindings.
  apply forallb_forall. intros name _.
  rewrite Hlookup.
  apply option_eq_equal_is_true. exact Htype.
Qed.

Definition affineAccept (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (right : list (Syntax.Name * Syntax.Ty))
  (entry : Syntax.Name * Syntax.Ty) : bool :=
  match entry with
  | (name,ty) =>
      match F.lookupFinite right name with
      | None => true
      | Some other => typeEq ty other
      end
  end.

Definition affineKeep (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (right : list (Syntax.Name * Syntax.Ty))
  (entry : Syntax.Name * Syntax.Ty) : bool :=
  match entry with
  | (name,ty) =>
      match F.lookupFinite right name with
      | None => false
      | Some other => typeEq ty other
      end
  end.

Definition affineCompatible (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (left right : list (Syntax.Name * Syntax.Ty)) : bool :=
  forallb (affineAccept typeEq right) left.

Definition affineIntersect (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (left right : list (Syntax.Name * Syntax.Ty))
  : list (Syntax.Name * Syntax.Ty) :=
  filter (affineKeep typeEq right) left.

Lemma affine_compatible_types :
  forall typeEq left right,
    affineCompatible typeEq left right = true ->
    forall name ty,
      F.lookupFinite left name = Some ty ->
      match F.lookupFinite right name with
      | None => True
      | Some other => typeEq ty other = true
      end.
Proof.
  intros typeEq left.
  induction left as [|[head carried] tail IH]; intros right Hvalid name ty Hlookup.
  - discriminate.
  - unfold affineCompatible in Hvalid. simpl in Hvalid.
    apply andb_true_iff in Hvalid as [Hhead Htail].
    simpl in Hlookup.
    destruct (String.eqb name head) eqn:Heq.
    + inversion Hlookup; subst ty.
      apply String.eqb_eq in Heq. subst name.
      unfold affineAccept in Hhead.
      destruct (F.lookupFinite right head) as [other|]; simpl in *.
      * exact Hhead.
      * exact I.
    + apply IH; assumption.
Qed.

Lemma lookup_filter_missing :
  forall entries predicate name,
    F.lookupFinite entries name = None ->
    F.lookupFinite (filter predicate entries) name = None.
Proof.
  induction entries as [|[head ty] tail IH]; intros predicate name Hnone.
  - reflexivity.
  - simpl in Hnone.
    destruct (String.eqb name head) eqn:Heq; try discriminate.
    simpl.
    destruct (predicate (head,ty)); simpl;
      try rewrite Heq; now apply IH.
Qed.

Lemma lookup_filter_nodup :
  forall entries predicate name,
    NoDup (keys entries) ->
    F.lookupFinite (filter predicate entries) name =
      match F.lookupFinite entries name with
      | None => None
      | Some ty => if predicate (name,ty) then Some ty else None
      end.
Proof.
  induction entries as [|[head ty] tail IH]; intros predicate name Hunique.
  - reflexivity.
  - simpl in Hunique.
    assert (Hnot : ~ In head (keys tail)).
    { inversion Hunique. assumption. }
    assert (Hrest : NoDup (keys tail)).
    { inversion Hunique. assumption. }
    simpl.
    destruct (String.eqb name head) eqn:Heq.
    + apply String.eqb_eq in Heq. subst name.
      assert (Htail : F.lookupFinite tail head = None).
      { apply absent_key_has_no_lookup. exact Hnot. }
      assert (Hfiltered :
        F.lookupFinite (filter predicate tail) head = None).
      { apply lookup_filter_missing. exact Htail. }
      destruct (predicate (head,ty)) eqn:Hpred;
        simpl; try rewrite String.eqb_refl; try reflexivity.
      exact Hfiltered.
    + destruct (predicate (head,ty)) eqn:Hpred; simpl;
        try rewrite Heq; apply IH; exact Hrest.
Qed.

Inductive JoinFailure : Type :=
| JoinLoanEscape
| JoinUnrestrictedMismatch
| JoinLinearMismatch
| JoinAffineTypeMismatch.

Inductive JoinDecision : Type :=
| JoinSuccess : F.FiniteSnapshot -> JoinDecision
| JoinRejected : JoinFailure -> JoinDecision.

(* The type comparator is a caller-supplied checked equality decision.
   It is not proof authority by virtue of this function's signature. *)
Definition finiteJoin (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
  (left right : F.FiniteSnapshot) : JoinDecision :=
  match F.finiteLoans left, F.finiteLoans right with
  | [],[] =>
      if sameBindings typeEq
        (F.finiteUnrestricted left) (F.finiteUnrestricted right)
      then if sameBindings typeEq
        (F.finiteLinear left) (F.finiteLinear right)
      then if affineCompatible typeEq
        (F.finiteAffine left) (F.finiteAffine right)
      then JoinSuccess (F.mkFiniteSnapshot
        (F.finiteUnrestricted left)
        (affineIntersect typeEq
          (F.finiteAffine left) (F.finiteAffine right))
        (F.finiteLinear left)
        [])
      else JoinRejected JoinAffineTypeMismatch
      else JoinRejected JoinLinearMismatch
      else JoinRejected JoinUnrestrictedMismatch
  | _,_ => JoinRejected JoinLoanEscape
  end.

Theorem corr6_join_success_produces_exact_finite_regions :
  forall typeEq left right joined,
    finiteJoin typeEq left right = JoinSuccess joined ->
    F.finiteUnrestricted joined = F.finiteUnrestricted left /\
    F.finiteLinear joined = F.finiteLinear left /\
    F.finiteLoans joined = [] /\
    F.finiteAffine joined =
      affineIntersect typeEq (F.finiteAffine left) (F.finiteAffine right).
Proof.
  intros typeEq left right joined H.
  unfold finiteJoin in H.
  destruct (F.finiteLoans left) as [|l ls]; try discriminate.
  destruct (F.finiteLoans right) as [|r rs]; try discriminate.
  destruct (sameBindings typeEq _ _) eqn:Hu; try discriminate.
  destruct (sameBindings typeEq _ _) eqn:Hl; try discriminate.
  destruct (affineCompatible typeEq _ _) eqn:Ha; try discriminate.
  inversion H; subst. repeat split; reflexivity.
Qed.

Theorem corr6_loan_rejection_happens_before_any_join :
  forall typeEq left right,
    F.finiteLoans left <> [] \/ F.finiteLoans right <> [] ->
    finiteJoin typeEq left right = JoinRejected JoinLoanEscape.
Proof.
  intros typeEq left right [Hl|Hr];
    unfold finiteJoin.
  - destruct (F.finiteLoans left); [contradiction|reflexivity].
  - destruct (F.finiteLoans left) as [|n ns]; [|reflexivity].
    destruct (F.finiteLoans right); [contradiction|reflexivity].
Qed.

(* A computed rejection has no fabricated joined successor. It is NOT
   source-validity judgment; independent source tests distinguish scope
   failures that occur before the two continuing branch inputs exist. *)
Definition joinedResult (decision : JoinDecision)
  : option F.FiniteSnapshot :=
  match decision with
  | JoinSuccess after => Some after
  | JoinRejected _ => None
  end.

Theorem corr6_rejection_has_no_joined_successor :
  forall reason,
    joinedResult (JoinRejected reason) = None.
Proof. intros []; reflexivity. Qed.

Print Assumptions same_bindings_sound.
Print Assumptions same_bindings_complete.
Print Assumptions affine_compatible_types.
Print Assumptions lookup_filter_nodup.
Print Assumptions corr6_join_success_produces_exact_finite_regions.
Print Assumptions corr6_loan_rejection_happens_before_any_join.
Print Assumptions corr6_rejection_has_no_joined_successor.
