From Stdlib Require Import Strings.String Bool.Bool Lia.

From Phil.Core Require Import Syntax.

(*
  Proof-oriented model of Phil.Core.Session.selectBranch / ensureUniqueLabels.

  The Haskell implementation uses Data.Set to reject any duplicate label before
  attempting selection, then selects the unique branch whose label matches the
  requested label. Here the set is represented structurally by checking whether
  a head label occurs in the remaining branch spine.
*)

Fixpoint containsLabel (target : string) (branches : Branches) : bool :=
  match branches with
  | BNil => false
  | BCons label _ _ rest =>
      String.eqb target label || containsLabel target rest
  end.

Fixpoint labelCount (target : string) (branches : Branches) : nat :=
  match branches with
  | BNil => 0
  | BCons label _ _ rest =>
      if String.eqb target label
      then S (labelCount target rest)
      else labelCount target rest
  end.

Fixpoint uniqueLabelsb (branches : Branches) : bool :=
  match branches with
  | BNil => true
  | BCons label _ _ rest =>
      negb (containsLabel label rest) && uniqueLabelsb rest
  end.

Fixpoint findBranch
  (target : string)
  (branches : Branches) : option (option (Name * Ty) * Session) :=
  match branches with
  | BNil => None
  | BCons label payload continuation rest =>
      if String.eqb target label
      then Some (payload, continuation)
      else findBranch target rest
  end.

Inductive BranchSelection : Type :=
| Selected : option (Name * Ty) -> Session -> BranchSelection
| UnknownLabel : BranchSelection
| DuplicateLabels : BranchSelection.

Definition selectBranch (target : string) (branches : Branches) : BranchSelection :=
  if uniqueLabelsb branches then
    match findBranch target branches with
    | Some (payload, continuation) => Selected payload continuation
    | None => UnknownLabel
    end
  else
    DuplicateLabels.

Lemma containsLabel_false_count_zero :
  forall (target : string) (branches : Branches),
    containsLabel target branches = false ->
    labelCount target branches = 0.
Proof.
  intros target branches.
  induction branches as [| label payload continuation rest IH].
  - reflexivity.
  - simpl.
    destruct (String.eqb target label) eqn:Heq.
    + intros Hcontains. discriminate.
    + intros Hcontains.
      apply IH.
      exact Hcontains.
Qed.

Lemma uniqueLabelsb_count_at_most_one :
  forall (target : string) (branches : Branches),
    uniqueLabelsb branches = true ->
    labelCount target branches <= 1.
Proof.
  intros target branches.
  induction branches as [| label payload continuation rest IH].
  - simpl. lia.
  - simpl.
    intros Hunique.
    apply andb_true_iff in Hunique as [Hfresh HrestUnique].
    apply negb_true_iff in Hfresh.
    destruct (String.eqb target label) eqn:Heq.
    + apply String.eqb_eq in Heq.
      subst target.
      pose proof (containsLabel_false_count_zero label rest Hfresh) as Hzero.
      rewrite Hzero.
      lia.
    + apply IH.
      exact HrestUnique.
Qed.

Lemma findBranch_some_count_positive :
  forall (target : string) (branches : Branches)
         (payload : option (Name * Ty)) (continuation : Session),
    findBranch target branches = Some (payload, continuation) ->
    1 <= labelCount target branches.
Proof.
  intros target branches.
  induction branches as [| label headPayload headContinuation rest IH].
  - simpl. intros payload continuation Hfind. discriminate.
  - simpl.
    destruct (String.eqb target label) eqn:Heq.
    + intros payload continuation Hfind.
      inversion Hfind; subst.
      lia.
    + intros payload continuation Hfind.
      eapply IH.
      exact Hfind.
Qed.

Lemma labelCount_zero_findBranch_none :
  forall (target : string) (branches : Branches),
    labelCount target branches = 0 ->
    findBranch target branches = None.
Proof.
  intros target branches Hzero.
  destruct (findBranch target branches) as [[payload continuation] |] eqn:Hfind.
  - pose proof
      (findBranch_some_count_positive target branches payload continuation Hfind)
      as Hpositive.
    lia.
  - reflexivity.
Qed.

(*
  PHIL-SESSION-LABEL-001.

  Every successful selection is made only after the entire branch set has passed
  duplicate-label rejection, and the requested label occurs exactly once.
*)
Theorem selectBranch_success_exactly_one :
  forall (target : string) (branches : Branches)
         (payload : option (Name * Ty)) (continuation : Session),
    selectBranch target branches = Selected payload continuation ->
    uniqueLabelsb branches = true /\
    labelCount target branches = 1.
Proof.
  intros target branches payload continuation Hselect.
  unfold selectBranch in Hselect.
  destruct (uniqueLabelsb branches) eqn:Hunique.
  - destruct (findBranch target branches) as [[foundPayload foundContinuation] |]
      eqn:Hfind.
    + inversion Hselect; subst.
      split.
      * exact Hunique.
      * pose proof
          (uniqueLabelsb_count_at_most_one target branches Hunique)
          as HatMostOne.
        pose proof
          (findBranch_some_count_positive
            target branches foundPayload foundContinuation Hfind)
          as Hpositive.
        lia.
    + discriminate.
  - discriminate.
Qed.

Corollary selectBranch_success_returns_requested_lookup :
  forall (target : string) (branches : Branches)
         (payload : option (Name * Ty)) (continuation : Session),
    selectBranch target branches = Selected payload continuation ->
    findBranch target branches = Some (payload, continuation).
Proof.
  intros target branches payload continuation Hselect.
  unfold selectBranch in Hselect.
  destruct (uniqueLabelsb branches) eqn:Hunique.
  - destruct (findBranch target branches) as [[foundPayload foundContinuation] |]
      eqn:Hfind.
    + inversion Hselect; subst.
      exact Hfind.
    + discriminate.
  - discriminate.
Qed.

(* PHIL-SESSION-LABEL-001: any duplicate-label state is rejected before lookup. *)
Theorem selectBranch_duplicate_labels_rejected :
  forall (target : string) (branches : Branches),
    uniqueLabelsb branches = false ->
    selectBranch target branches = DuplicateLabels.
Proof.
  intros target branches Hduplicate.
  unfold selectBranch.
  rewrite Hduplicate.
  reflexivity.
Qed.

(* PHIL-SESSION-LABEL-001: an absent requested label is rejected. *)
Theorem selectBranch_absent_label_rejected :
  forall (target : string) (branches : Branches),
    uniqueLabelsb branches = true ->
    labelCount target branches = 0 ->
    selectBranch target branches = UnknownLabel.
Proof.
  intros target branches Hunique Habsent.
  unfold selectBranch.
  rewrite Hunique.
  rewrite (labelCount_zero_findBranch_none target branches Habsent).
  reflexivity.
Qed.
