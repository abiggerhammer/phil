From Stdlib Require Import Arith.PeanoNat Bool.Bool.

From Phil.Assurance Require Import EvidenceUse.

(*
  PHIL-ASSURE-LEDGER-EXT-001 — append-only ledger extension composes.

  EvidenceUse.v already models Phil.Assurance.Verify.verifyLedgerExtension as
  preservation of every existing node in each of the five ledger maps and proves
  that one verified extension preserves old nodes and forbids in-place rewrite.

  This file proves the algebra needed for durable histories:

  - map preservation is reflexive and transitive;
  - ledger extension is therefore reflexive and transitive (a preorder);
  - any finite chain of verified adjacent extensions collapses to a verified
    ancestor-to-descendant extension and preserves every ancestor node;
  - checking only an ancient root against a tip is not enough to protect nodes
    first introduced at an intermediate stage. Pairwise chain verification is
    what freezes each stage as it becomes history.

  The normalized theorem is about immutable node preservation. Concrete Haskell
  Map key/value equality, map enumeration, serialization, storage durability,
  and concurrency remain implementation/trust boundaries.
*)

Theorem preserves_map_reflexive :
  forall nodes,
    PreservesMap nodes nodes.
Proof.
  intros nodes key value Hold.
  exact Hold.
Qed.

Theorem preserves_map_transitive :
  forall first middle last,
    PreservesMap first middle ->
    PreservesMap middle last ->
    PreservesMap first last.
Proof.
  intros first middle last Hfirst Hlast key value Hold.
  apply Hlast.
  apply Hfirst.
  exact Hold.
Qed.

Theorem ledger_extension_reflexive :
  forall ledger,
    LedgerExtension ledger ledger.
Proof.
  intros ledger.
  constructor; apply preserves_map_reflexive.
Qed.

Theorem ledger_extension_transitive :
  forall first middle last,
    LedgerExtension first middle ->
    LedgerExtension middle last ->
    LedgerExtension first last.
Proof.
  intros first middle last Hfirst Hlast.
  destruct Hfirst as
    [HfirstRevisions HfirstEvidence HfirstAssumptions HfirstExports HfirstUses].
  destruct Hlast as
    [HlastRevisions HlastEvidence HlastAssumptions HlastExports HlastUses].
  constructor.
  - eapply preserves_map_transitive; eauto.
  - eapply preserves_map_transitive; eauto.
  - eapply preserves_map_transitive; eauto.
  - eapply preserves_map_transitive; eauto.
  - eapply preserves_map_transitive; eauto.
Qed.

Theorem ledger_extension_is_preorder :
  (forall ledger, LedgerExtension ledger ledger) /\
  (forall first middle last,
    LedgerExtension first middle ->
    LedgerExtension middle last ->
    LedgerExtension first last).
Proof.
  split.
  - exact ledger_extension_reflexive.
  - exact ledger_extension_transitive.
Qed.

Inductive LedgerExtensionChain : LedgerView -> LedgerView -> Prop :=
| LedgerChainRefl : forall ledger,
    LedgerExtensionChain ledger ledger
| LedgerChainStep : forall first middle last,
    LedgerExtension first middle ->
    LedgerExtensionChain middle last ->
    LedgerExtensionChain first last.

Theorem ledger_extension_chain_collapses :
  forall first last,
    LedgerExtensionChain first last ->
    LedgerExtension first last.
Proof.
  intros first last Hchain.
  induction Hchain as
    [ledger
    | first middle last Hstep Hrest IH].
  - apply ledger_extension_reflexive.
  - eapply ledger_extension_transitive.
    + exact Hstep.
    + exact IH.
Qed.

Theorem verified_extension_chain_preserves_every_ancestor_node :
  forall first last class key value,
    LedgerExtensionChain first last ->
    nodesOf class first key = Some value ->
    nodesOf class last key = Some value.
Proof.
  intros first last class key value Hchain Hold.
  pose proof
    (ledger_extension_chain_collapses first last Hchain)
    as Hextension.
  eapply verified_ledger_extension_preserves_every_existing_node.
  - exact Hextension.
  - exact Hold.
Qed.

(* -------------------------------------------------------------------------- *)
(* Root-to-tip verification alone does not freeze an intermediate addition.   *)
(* -------------------------------------------------------------------------- *)

Definition EmptyNodeMap : NodeMap := fun _ => None.

Definition SingletonNodeMap : NodeMap :=
  fun key => if Nat.eqb key 0 then Some 1 else None.

Definition EmptyLedgerView : LedgerView :=
  mkLedgerView
    EmptyNodeMap
    EmptyNodeMap
    EmptyNodeMap
    EmptyNodeMap
    EmptyNodeMap.

Definition IntermediateLedgerView : LedgerView :=
  mkLedgerView
    EmptyNodeMap
    EmptyNodeMap
    SingletonNodeMap
    EmptyNodeMap
    EmptyNodeMap.

Lemma empty_to_intermediate_is_extension :
  LedgerExtension EmptyLedgerView IntermediateLedgerView.
Proof.
  constructor; intros key value Hold; simpl in Hold; discriminate.
Qed.

Lemma empty_to_empty_is_extension :
  LedgerExtension EmptyLedgerView EmptyLedgerView.
Proof.
  apply ledger_extension_reflexive.
Qed.

Lemma intermediate_to_empty_is_not_extension :
  ~ LedgerExtension IntermediateLedgerView EmptyLedgerView.
Proof.
  intros Hextension.
  destruct Hextension as [_ _ Hassumptions _ _].
  assert (Hmiddle : assumptionNodes IntermediateLedgerView 0 = Some 1).
  {
    reflexivity.
  }
  pose proof (Hassumptions 0 1 Hmiddle) as Hpreserved.
  simpl in Hpreserved.
  discriminate.
Qed.

Theorem root_to_tip_extension_does_not_imply_intermediate_preservation :
  exists root intermediate tip,
    LedgerExtension root intermediate /\
    LedgerExtension root tip /\
    ~ LedgerExtension intermediate tip.
Proof.
  exists EmptyLedgerView, IntermediateLedgerView, EmptyLedgerView.
  split.
  - exact empty_to_intermediate_is_extension.
  - split.
    + exact empty_to_empty_is_extension.
    + exact intermediate_to_empty_is_not_extension.
Qed.
