From Stdlib Require Import Bool.Bool Setoids.Setoid.

From Phil.Core Require Import CheckedBindingMode.

(*
  Machine-facing decision surface for PHIL-RES-BIND-MODE-001.

  The concrete Haskell checker performs these checks in diagnostic order:
  checked type equality, checked mode equality, then Context.insertBinding.
  The extracted gate owns only the final success conjunction.  Detailed native
  mismatch/duplicate diagnostics remain an implementation responsibility and
  are preserved by later production binding.
*)

Definition decideCheckedBindingModeByFacts
  (typeMatches modeMatches contextAccepts : bool) : bool :=
  andb typeMatches (andb modeMatches contextAccepts).

Theorem decideCheckedBindingModeByFacts_classifies :
  forall origin checked suppliedMode name suppliedType context next
    typeMatches modeMatches contextAccepts,
    (typeMatches = true <-> suppliedType = checkedBindingType checked) ->
    (modeMatches = true <-> suppliedMode = checkedBindingMode checked) ->
    (contextAccepts = true <->
      insertBinding
        (checkedBindingMode checked)
        name
        suppliedType
        context = Inserted next) ->
    decideCheckedBindingModeByFacts
      typeMatches modeMatches contextAccepts = true <->
    CertifiedCheckedBindingInsertion
      origin checked suppliedMode name suppliedType context next.
Proof.
  intros origin checked suppliedMode name suppliedType context next
    typeMatches modeMatches contextAccepts
    Htype Hmode Hcontext.
  unfold decideCheckedBindingModeByFacts.
  repeat rewrite andb_true_iff.
  rewrite Htype, Hmode, Hcontext.
  split.
  - intros [HtypeExact [HmodeExact Hinsert]].
    constructor; assumption.
  - intros Hcert.
    destruct Hcert as [HtypeExact HmodeExact Hinsert].
    repeat split; assumption.
Qed.
