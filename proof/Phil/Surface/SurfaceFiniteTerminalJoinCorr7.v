From Stdlib Require Import Lists.List Bool.Bool Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax.
From Phil.Surface Require Import SurfaceFiniteContextFrame SurfaceFiniteMixedJoinCorr6.

(*
  FSEM-01 CORR-7 / J-4: FINITE model of source predecessor classification.
  Source failures are distinguished from a resource-join error.  A list
  containing no continuing predecessor is NOT the empty Core context.
  The computation checks loans across ALL continuing predecessors before
  inspecting any U/Linear maps; only then does it fold Affine intersection.
  This is not a universal native Map/Set/Text or source-to-Rocq refinement.
*)
Module F := SurfaceFiniteContextFrame.
Module J := SurfaceFiniteMixedJoinCorr6.

Inductive Predecessor : Type :=
| Continuing : F.FiniteSnapshot -> Predecessor
| Terminal : Predecessor
| Failed : string -> Predecessor.

Inductive Outcome : Type :=
| NoContinuation
| Joined : F.FiniteSnapshot -> Outcome
| JoinRejected : J.JoinFailure -> Outcome
| SourceRejected : string -> Outcome.

Fixpoint continuingStates (paths : list Predecessor)
  : list F.FiniteSnapshot :=
  match paths with
  | [] => []
  | Continuing state :: rest => state :: continuingStates rest
  | _ :: rest => continuingStates rest
  end.

Fixpoint firstSourceFailure (paths : list Predecessor)
  : option string :=
  match paths with
  | [] => None
  | Failed reason :: _ => Some reason
  | _ :: rest => firstSourceFailure rest
  end.

Definition loanFree (state : F.FiniteSnapshot) : bool :=
  match F.finiteLoans state with
  | [] => true
  | _ => false
  end.

Fixpoint foldAffine
    (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
    (carried : list (Syntax.Name * Syntax.Ty))
    (rest : list F.FiniteSnapshot)
    : option (list (Syntax.Name * Syntax.Ty)) :=
  match rest with
  | [] => Some carried
  | state :: tail =>
      if J.affineCompatible typeEq carried (F.finiteAffine state)
      then foldAffine typeEq
        (J.affineIntersect typeEq carried (F.finiteAffine state)) tail
      else None
  end.

Definition computeContinuing
    (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
    (states : list F.FiniteSnapshot) : Outcome :=
  match states with
  | [] => NoContinuation
  | first :: rest =>
      if forallb loanFree states then
        if forallb (fun state => J.sameBindings typeEq
          (F.finiteUnrestricted first) (F.finiteUnrestricted state)) rest then
          if forallb (fun state => J.sameBindings typeEq
            (F.finiteLinear first) (F.finiteLinear state)) rest then
            match foldAffine typeEq (F.finiteAffine first) rest with
            | None => JoinRejected J.JoinAffineTypeMismatch
            | Some common =>
                Joined (F.mkFiniteSnapshot
                  (F.finiteUnrestricted first) common
                  (F.finiteLinear first) [])
            end
          else JoinRejected J.JoinLinearMismatch
        else JoinRejected J.JoinUnrestrictedMismatch
      else JoinRejected J.JoinLoanEscape
  end.

Definition replay
    (typeEq : Syntax.Ty -> Syntax.Ty -> bool)
    (paths : list Predecessor) : Outcome :=
  match firstSourceFailure paths with
  | Some reason => SourceRejected reason
  | None => computeContinuing typeEq (continuingStates paths)
  end.

(* No source-control continuation is manufactured by an empty Core join. *)
Theorem corr7_all_terminal_has_no_continuation :
  forall typeEq paths,
    Forall (fun path => match path with Terminal => True | _ => False end)
      paths ->
    replay typeEq paths = NoContinuation.
Proof.
  intros typeEq paths Hall.
  induction Hall as [|path paths Hhead Hall IH]; simpl; auto.
  destruct path; try contradiction.
  simpl. exact IH.
Qed.

Theorem corr7_source_failure_preempts_join :
  forall typeEq paths reason,
    firstSourceFailure paths = Some reason ->
    replay typeEq paths = SourceRejected reason.
Proof. intros; unfold replay; now rewrite H. Qed.

Theorem corr7_no_continuing_path_has_no_successor :
  forall typeEq paths,
    firstSourceFailure paths = None ->
    continuingStates paths = [] ->
    replay typeEq paths = NoContinuation.
Proof. intros; unfold replay; now rewrite H, H0. Qed.

Theorem corr7_terminal_prefix_and_suffix_ignored :
  forall typeEq state,
    replay typeEq [Terminal; Continuing state; Terminal] =
    replay typeEq [Continuing state].
Proof. intros; reflexivity. Qed.

Theorem corr7_single_loan_free_survivor :
  forall typeEq state,
    F.finiteLoans state = [] ->
    replay typeEq [Terminal; Continuing state] =
      Joined (F.mkFiniteSnapshot
        (F.finiteUnrestricted state) (F.finiteAffine state)
        (F.finiteLinear state) []).
Proof.
  intros typeEq state Hloan.
  unfold replay, computeContinuing, loanFree.
  simpl. now rewrite Hloan.
Qed.

Theorem corr7_first_source_failure_is_sticky :
  forall typeEq left right rest,
    replay typeEq (Failed left :: Failed right :: rest) = SourceRejected left.
Proof. intros; reflexivity. Qed.

Theorem corr7_loan_precedes_all_resource_mismatches :
  forall typeEq first rest offending,
    In offending (first :: rest) ->
    F.finiteLoans offending <> [] ->
    computeContinuing typeEq (first :: rest) =
      JoinRejected J.JoinLoanEscape.
Proof.
  intros typeEq first rest offending Hin Hloan.
  unfold computeContinuing.
  destruct (forallb loanFree (first :: rest)) eqn:Hfree.
  - apply forallb_forall with (x := offending) in Hfree; auto.
    unfold loanFree in Hfree.
    destruct (F.finiteLoans offending); simpl in Hfree.
    + contradiction.
    + discriminate.
  - reflexivity.
Qed.

Theorem corr7_unrestricted_precedes_linear_and_affine :
  forall typeEq first rest,
    forallb loanFree (first :: rest) = true ->
    forallb (fun state => J.sameBindings typeEq
      (F.finiteUnrestricted first) (F.finiteUnrestricted state)) rest = false ->
    computeContinuing typeEq (first :: rest) =
      JoinRejected J.JoinUnrestrictedMismatch.
Proof.
  intros typeEq first rest Hloans Hu.
  unfold computeContinuing. now rewrite Hloans, Hu.
Qed.

Theorem corr7_linear_precedes_affine :
  forall typeEq first rest,
    forallb loanFree (first :: rest) = true ->
    forallb (fun state => J.sameBindings typeEq
      (F.finiteUnrestricted first) (F.finiteUnrestricted state)) rest = true ->
    forallb (fun state => J.sameBindings typeEq
      (F.finiteLinear first) (F.finiteLinear state)) rest = false ->
    computeContinuing typeEq (first :: rest) =
      JoinRejected J.JoinLinearMismatch.
Proof.
  intros typeEq first rest Hloans Hu Hl.
  unfold computeContinuing. now rewrite Hloans, Hu, Hl.
Qed.

Theorem corr7_success_has_exact_regions :
  forall typeEq first rest result,
    computeContinuing typeEq (first :: rest) = Joined result ->
    F.finiteUnrestricted result = F.finiteUnrestricted first /\
    F.finiteLinear result = F.finiteLinear first /\
    F.finiteLoans result = [].
Proof.
  intros typeEq first rest result H.
  unfold computeContinuing in H.
  destruct (forallb loanFree (first :: rest)); try discriminate.
  destruct (forallb (fun state => J.sameBindings typeEq
    (F.finiteUnrestricted first) (F.finiteUnrestricted state)) rest);
    try discriminate.
  destruct (forallb (fun state => J.sameBindings typeEq
    (F.finiteLinear first) (F.finiteLinear state)) rest);
    try discriminate.
  destruct (foldAffine typeEq (F.finiteAffine first) rest);
    try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.

Lemma corr7_keys_filter_subset :
  forall (entries : list (Syntax.Name * Syntax.Ty)) predicate name,
    In name (J.keys (filter predicate entries)) ->
    In name (J.keys entries).
Proof.
  induction entries as [|[head ty] tail IH]; intros predicate name H; simpl in *.
  - contradiction.
  - destruct (predicate (head, ty)) eqn:Hkeep; simpl in H.
    + destruct H as [H|H].
      * now left.
      * right. now apply IH with (predicate := predicate).
    + right. now apply IH with (predicate := predicate).
Qed.

Theorem corr7_affine_fold_never_resurrects_an_owner :
  forall typeEq carried rest joined name,
    foldAffine typeEq carried rest = Some joined ->
    In name (J.keys joined) ->
    In name (J.keys carried).
Proof.
  intros typeEq carried rest.
  revert carried.
  induction rest as [|state rest IH]; intros carried joined name Hfold Hin.
  - simpl in Hfold. inversion Hfold; subst; exact Hin.
  - simpl in Hfold.
    destruct (J.affineCompatible typeEq carried (F.finiteAffine state))
      eqn:Hcompatible; try discriminate.
    apply corr7_keys_filter_subset
      with (predicate := J.affineKeep typeEq (F.finiteAffine state)).
    apply (IH (J.affineIntersect typeEq carried (F.finiteAffine state))
      joined name Hfold Hin).
Qed.

Print Assumptions corr7_all_terminal_has_no_continuation.
Print Assumptions corr7_source_failure_preempts_join.
Print Assumptions corr7_no_continuing_path_has_no_successor.
Print Assumptions corr7_single_loan_free_survivor.
Print Assumptions corr7_loan_precedes_all_resource_mismatches.
Print Assumptions corr7_unrestricted_precedes_linear_and_affine.
Print Assumptions corr7_linear_precedes_affine.
Print Assumptions corr7_success_has_exact_regions.
Print Assumptions corr7_affine_fold_never_resurrects_an_owner.
