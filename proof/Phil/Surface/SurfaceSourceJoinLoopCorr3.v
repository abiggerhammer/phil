From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import
  SurfaceFiniteContextFrame SurfaceSourceScopedBorrowJoin
  SurfaceSourceLinearLoopTransfer SurfaceSourceJoinLoopCorr2.

(*
  FSEM-01 CORR-3: independently supplied finite U/A/L/loan source cuts
  are related extensionally to the already-proved conditional Context
  transition and join model. A native test must check ExactFiniteRelation
  against its ACTUAL source-checker Map/Set states for each admitted specimen.

  This is not a theorem that Haskell's serializer or its source checker is
  implemented by Rocq. Source-to-finite representation correctness remains
  an independently tested, finite premise. No general source semantics,
  parser completeness, runtime iteration or compiler refinement is claimed.
*)

Definition SourceCutRel
  (snap : SurfaceFiniteContextFrame.FiniteSnapshot)
  (ctx : Context.ResourceContext) : Prop :=
  SurfaceFiniteContextFrame.ExactFiniteRelation snap ctx.

Lemma corr3_finite_linear_is_exact :
  forall snap ctx query,
    SourceCutRel snap ctx ->
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear snap) query =
    Context.linearBindings ctx query.
Proof.
  intros snap ctx query Hsnap.
  destruct (Hsnap query) as [_ [_ [Hlinear _]]].
  symmetry. exact Hlinear.
Qed.

Lemma corr3_finite_loan_is_exact :
  forall snap ctx query,
    SourceCutRel snap ctx ->
    SurfaceFiniteContextFrame.loanInFinite
      (SurfaceFiniteContextFrame.finiteLoans snap) query =
    Context.sharedLoans ctx query.
Proof.
  intros snap ctx query Hsnap.
  destruct (Hsnap query) as [_ [_ [_ Hloan]]].
  symmetry. exact Hloan.
Qed.

Theorem corr3_two_source_join_cuts_preserve_exact_owner_and_closed_loans :
  forall left right joined sourceLeft sourceRight sourceJoined owner ty,
    SourceCutRel sourceLeft left ->
    SourceCutRel sourceRight right ->
    SourceCutRel sourceJoined joined ->
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear sourceLeft) owner = Some ty ->
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear sourceJoined) owner = Some ty /\
    SurfaceFiniteContextFrame.loanInFinite
      (SurfaceFiniteContextFrame.finiteLoans sourceLeft) owner = false /\
    SurfaceFiniteContextFrame.loanInFinite
      (SurfaceFiniteContextFrame.finiteLoans sourceRight) owner = false /\
    SurfaceFiniteContextFrame.loanInFinite
      (SurfaceFiniteContextFrame.finiteLoans sourceJoined) owner = false.
Proof.
  intros left right joined sl sr sj owner ty Hsl Hsr Hsj Hjoin HsourceOwner.
  rewrite (corr3_finite_linear_is_exact sl left owner Hsl)
    in HsourceOwner.
  pose proof
    (SurfaceSourceJoinLoopCorr2.corr2_join_preserves_linear_and_closes_all_loan_cuts
      left right joined owner ty Hjoin HsourceOwner)
    as [Hjoined [HleftClosed [HrightClosed HjoinedClosed]]].
  repeat split.
  - rewrite (corr3_finite_linear_is_exact sj joined owner Hsj).
    exact Hjoined.
  - rewrite (corr3_finite_loan_is_exact sl left owner Hsl).
    exact HleftClosed.
  - rewrite (corr3_finite_loan_is_exact sr right owner Hsr).
    exact HrightClosed.
  - rewrite (corr3_finite_loan_is_exact sj joined owner Hsj).
    exact HjoinedClosed.
Qed.

Theorem corr3_join_preserves_the_whole_finite_linear_domain :
  forall left right joined sourceLeft sourceJoined,
    SourceCutRel sourceLeft left ->
    SourceCutRel sourceJoined joined ->
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    forall query,
      SurfaceFiniteContextFrame.lookupFinite
        (SurfaceFiniteContextFrame.finiteLinear sourceJoined) query =
      SurfaceFiniteContextFrame.lookupFinite
        (SurfaceFiniteContextFrame.finiteLinear sourceLeft) query.
Proof.
  intros left right joined sl sj Hsl Hsj Hjoin query.
  rewrite (corr3_finite_linear_is_exact sj joined query Hsj).
  rewrite (corr3_finite_linear_is_exact sl left query Hsl).
  pose proof (ContextJoin.context_join_linear_converges
    [left;right] joined left Hjoin (or_introl eq_refl)) as Hsame.
  unfold ContextJoin.SameBindingMap in Hsame.
  exact (Hsame query).
Qed.

Theorem corr3_loop_source_cuts_preserve_header_and_refuse_old_owner :
  forall initial spent header backSpent rebound joined
         sourceHeader sourceRebound sourceJoined old slot ty,
    SourceCutRel sourceHeader header ->
    SourceCutRel sourceRebound rebound ->
    SourceCutRel sourceJoined joined ->
    Context.consumeLinear old initial = Context.Consumed ty spent ->
    Context.insertBinding Syntax.Linear slot ty spent =
      Context.Inserted header ->
    Context.consumeLinear slot header = Context.Consumed ty backSpent ->
    Context.insertBinding Syntax.Linear slot ty backSpent =
      Context.Inserted rebound ->
    String.eqb old slot = false ->
    ContextJoin.ContextJoinSuccess [header;rebound] joined ->
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear sourceHeader) slot = Some ty /\
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear sourceRebound) slot = Some ty /\
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear sourceJoined) old = None /\
    SurfaceFiniteContextFrame.lookupFinite
      (SurfaceFiniteContextFrame.finiteLinear sourceJoined) slot = Some ty /\
    SurfaceFiniteContextFrame.loanInFinite
      (SurfaceFiniteContextFrame.finiteLoans sourceJoined) slot = false /\
    Context.insertBinding Syntax.Linear slot ty header =
      Context.InsertError (Context.DuplicateBinding slot).
Proof.
  intros initial spent header backSpent rebound joined
    sh sr sj old slot ty Hsh Hsr Hsj Hentry Hheader Hback Hrebound
    Hdistinct Hjoin.
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_entry_consumes_old_owner_and_installs_header
      initial spent header old slot ty Hentry Hheader)
    as [_ [_ HheaderSlot]].
  pose proof
    (Context.insertBinding_success_exact
      Syntax.Linear slot ty backSpent rebound Hrebound)
    as [_ [_ [_ [HreboundMode _]]]].
  simpl in HreboundMode.
  destruct HreboundMode as [_ [_ HreboundSlot]].
  pose proof
    (SurfaceSourceJoinLoopCorr2.corr2_loop_entry_backedge_and_join_preserve_exact_owner
      initial spent header backSpent rebound joined old slot ty
      Hentry Hheader Hback Hrebound Hdistinct Hjoin)
    as [Hold [Hslot [HnoLoans Hduplicate]]].
  unfold ContextJoin.NoLoans in HnoLoans.
  repeat split.
  - rewrite (corr3_finite_linear_is_exact sh header slot Hsh).
    exact HheaderSlot.
  - rewrite (corr3_finite_linear_is_exact sr rebound slot Hsr).
    exact HreboundSlot.
  - rewrite (corr3_finite_linear_is_exact sj joined old Hsj).
    exact Hold.
  - rewrite (corr3_finite_linear_is_exact sj joined slot Hsj).
    exact Hslot.
  - rewrite (corr3_finite_loan_is_exact sj joined slot Hsj).
    exact (HnoLoans slot).
  - exact Hduplicate.
Qed.

Theorem corr3_live_loan_in_real_cut_cannot_gain_join_success :
  forall left right joined sourceRight owner,
    SourceCutRel sourceRight right ->
    SurfaceFiniteContextFrame.loanInFinite
      (SurfaceFiniteContextFrame.finiteLoans sourceRight) owner = true ->
    ~ ContextJoin.ContextJoinSuccess [left;right] joined.
Proof.
  intros left right joined sr owner Hsr Hloan.
  rewrite (corr3_finite_loan_is_exact sr right owner Hsr) in Hloan.
  exact
    (SurfaceSourceJoinLoopCorr2.corr2_live_loan_cannot_cross_two_predecessor_reentry
      left right joined owner Hloan).
Qed.

Print Assumptions corr3_two_source_join_cuts_preserve_exact_owner_and_closed_loans.
Print Assumptions corr3_join_preserves_the_whole_finite_linear_domain.
Print Assumptions corr3_loop_source_cuts_preserve_header_and_refuse_old_owner.
Print Assumptions corr3_live_loan_in_real_cut_cannot_gain_join_success.
