From Stdlib Require Import Bool.Bool.

From Phil.Surface Require Import ImportNoninterference.

Set Implicit Arguments.

(*
  PHIL-ARCH-IMPORT-001 — representation-neutral implementation correspondence.

  Production owns concrete module-table lookup, Text equality, and Map
  traversal.  Once lookup has selected an already-checked declaration identity,
  this layer owns the semantic fail-closed order for one imported binding:
  selected export first, then local-name freshness.  The module locator is
  intentionally absent from the decision surface.  Successful construction
  preserves the exact local spelling and declaration identity.
*)

Inductive ImportResolutionDecision : Type :=
| ImportResolutionDecisionAccepted
| UnknownSelectedExportDecision
| DuplicateResolutionNameDecision.

Definition decideImportResolutionByFacts
  (selectedExportPresent localNameFresh : bool)
  : ImportResolutionDecision :=
  if selectedExportPresent then
    if localNameFresh then
      ImportResolutionDecisionAccepted
    else DuplicateResolutionNameDecision
  else UnknownSelectedExportDecision.

Record ImportedBindingPlan
  (localName identity : Type) : Type :=
  mkImportedBindingPlan {
    plannedImportLocalName : localName;
    plannedImportIdentity : identity
  }.

Definition planImportedBinding
  {localName identity : Type}
  (name : localName)
  (declarationIdentity : identity)
  : ImportedBindingPlan localName identity :=
  {| plannedImportLocalName := name;
     plannedImportIdentity := declarationIdentity |}.

Arguments plannedImportLocalName {localName identity} _.
Arguments plannedImportIdentity {localName identity} _.

Theorem exact_import_facts_accept :
  decideImportResolutionByFacts true true =
    ImportResolutionDecisionAccepted.
Proof. reflexivity. Qed.

Theorem unknown_selected_export_has_precedence :
  forall localNameFresh,
    decideImportResolutionByFacts false localNameFresh =
      UnknownSelectedExportDecision.
Proof. reflexivity. Qed.

Theorem duplicate_local_name_rejects_after_selection :
  decideImportResolutionByFacts true false =
    DuplicateResolutionNameDecision.
Proof. reflexivity. Qed.

Theorem accepted_import_requires_both_reflected_facts :
  forall selectedExportPresent localNameFresh,
    decideImportResolutionByFacts selectedExportPresent localNameFresh =
      ImportResolutionDecisionAccepted ->
    selectedExportPresent = true /\ localNameFresh = true.
Proof.
  intros selectedExportPresent localNameFresh Haccepted.
  destruct selectedExportPresent; simpl in Haccepted; try discriminate.
  destruct localNameFresh; simpl in Haccepted; try discriminate.
  split; reflexivity.
Qed.

Theorem imported_binding_plan_is_exact :
  forall localName identity
         (name : localName)
         (declarationIdentity : identity),
    plannedImportLocalName
      (planImportedBinding name declarationIdentity) = name /\
    plannedImportIdentity
      (planImportedBinding name declarationIdentity) = declarationIdentity.
Proof.
  intros.
  split; reflexivity.
Qed.

(* The module locator is deliberately not an argument to either executable
   function.  This mirrors the Certified theorem that, after selection of the
   same checked DeclarationIdentity, moving the exporting module cannot alter
   the semantic identity imported into the local scope. *)

Theorem reflected_import_decision_matches_certified_gate_order :
  forall state localName selectedExportPresent localNameFresh,
    selectedExportPresent = true ->
    (localNameFresh = true <->
      lookupBinding localName (resolutionBindings state) = None) ->
    decideImportResolutionByFacts
      selectedExportPresent localNameFresh = ImportResolutionDecisionAccepted ->
    lookupBinding localName (resolutionBindings state) = None.
Proof.
  intros state localName selectedExportPresent localNameFresh
    _ Hfresh Haccepted.
  apply accepted_import_requires_both_reflected_facts in Haccepted.
  destruct Haccepted as [_ HfreshFact].
  apply (proj1 Hfresh).
  exact HfreshFact.
Qed.
