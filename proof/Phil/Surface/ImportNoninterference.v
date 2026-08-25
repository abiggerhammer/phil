From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.

Import ListNotations.

(*
  PHIL-ARCH-IMPORT-001 — Phase 1 import authority noninterference.

  This is a normalized proof model of the pure resolver boundary implemented by
  Phil.Surface.Check.  A successful import can add one local spelling for an
  already checked DeclarationIdentity.  All authority-bearing, assurance-
  bearing, architecture-occurrence, realization, and runtime-effect state is
  carried beside that name-resolution map and is preserved exactly.

  Module locators are intentionally nonsemantic once they have selected the
  same checked declaration identity.  Unknown exports and duplicate local names
  fail closed and produce no successor state.

  Concrete Haskell Map/fold traversal, Text equality, module-table lookup, and
  correspondence from the implementation to this normalized model remain an
  explicit checked trust boundary.  Final Phil source syntax, package/version
  solving, and repository provenance are outside this theorem family.
*)

Definition LocalName := nat.
Definition ModuleLocator := nat.
Definition DeclarationIdentity := nat.
Definition Binding := (LocalName * DeclarationIdentity)%type.
Definition BindingMap := list Binding.

Fixpoint lookupBinding
  (name : LocalName)
  (bindings : BindingMap) : option DeclarationIdentity :=
  match bindings with
  | [] => None
  | (key, value) :: rest =>
      if Nat.eqb name key then Some value else lookupBinding name rest
  end.

Definition insertBinding
  (name : LocalName)
  (identity : DeclarationIdentity)
  (bindings : BindingMap) : option BindingMap :=
  match lookupBinding name bindings with
  | Some _ => None
  | None => Some ((name, identity) :: bindings)
  end.

Record ResolverState : Type := mkResolverState {
  resolutionBindings : BindingMap;
  capabilityAuthority : list nat;
  satisfiedProviderRequirements : list nat;
  acceptedAssumptions : list nat;
  dischargedObligations : list nat;
  architectureOccurrences : list nat;
  realizationChoices : list nat;
  runtimeEffects : list nat
}.

Definition importIdentity
  (localName : LocalName)
  (identity : DeclarationIdentity)
  (state : ResolverState) : option ResolverState :=
  match insertBinding localName identity (resolutionBindings state) with
  | None => None
  | Some bindings =>
      Some (mkResolverState
        bindings
        (capabilityAuthority state)
        (satisfiedProviderRequirements state)
        (acceptedAssumptions state)
        (dischargedObligations state)
        (architectureOccurrences state)
        (realizationChoices state)
        (runtimeEffects state))
  end.

(* Module lookup is outside the semantic identity itself.  This model receives
   the already selected checked identity, or None when lookup failed. *)
Definition resolveSelectedExport
  (_module : ModuleLocator)
  (selected : option DeclarationIdentity)
  (localName : LocalName)
  (state : ResolverState) : option ResolverState :=
  match selected with
  | None => None
  | Some identity => importIdentity localName identity state
  end.

Lemma successful_insert_is_exact :
  forall name identity bindings updated,
    insertBinding name identity bindings = Some updated ->
    lookupBinding name updated = Some identity.
Proof.
  intros name identity bindings updated Hinsert.
  unfold insertBinding in Hinsert.
  destruct (lookupBinding name bindings) eqn:Hlookup;
    [ discriminate | ].
  inversion Hinsert; subst updated.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem successful_import_preserves_exact_declaration_identity :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    lookupBinding localName (resolutionBindings state') = Some identity.
Proof.
  intros state localName identity state' Himport.
  unfold importIdentity in Himport.
  destruct (insertBinding localName identity (resolutionBindings state))
    eqn:Hinsert;
    [ | discriminate ].
  inversion Himport; subst state'.
  simpl.
  eapply successful_insert_is_exact.
  exact Hinsert.
Qed.

Theorem successful_import_changes_name_availability_only :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    capabilityAuthority state' = capabilityAuthority state /\
    satisfiedProviderRequirements state' = satisfiedProviderRequirements state /\
    acceptedAssumptions state' = acceptedAssumptions state /\
    dischargedObligations state' = dischargedObligations state /\
    architectureOccurrences state' = architectureOccurrences state /\
    realizationChoices state' = realizationChoices state /\
    runtimeEffects state' = runtimeEffects state.
Proof.
  intros state localName identity state' Himport.
  unfold importIdentity in Himport.
  destruct (insertBinding localName identity (resolutionBindings state));
    [ | discriminate ].
  inversion Himport; subst state'.
  simpl.
  repeat split; reflexivity.
Qed.

Corollary successful_import_grants_no_capability_authority :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    capabilityAuthority state' = capabilityAuthority state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [Hcap _].
  exact Hcap.
Qed.

Corollary successful_import_satisfies_no_provider_requirement :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    satisfiedProviderRequirements state' = satisfiedProviderRequirements state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [_ [Hprovider _]].
  exact Hprovider.
Qed.

Corollary successful_import_accepts_no_assumption :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    acceptedAssumptions state' = acceptedAssumptions state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [_ [_ [Hassumption _]]].
  exact Hassumption.
Qed.

Corollary successful_import_discharges_no_obligation :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    dischargedObligations state' = dischargedObligations state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [_ [_ [_ [Hobligation _]]]].
  exact Hobligation.
Qed.

Corollary successful_import_instantiates_no_architecture_occurrence :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    architectureOccurrences state' = architectureOccurrences state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [_ [_ [_ [_ [Hinstance _]]]]].
  exact Hinstance.
Qed.

Corollary successful_import_creates_no_realization :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    realizationChoices state' = realizationChoices state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [_ [_ [_ [_ [_ [Hrealization _]]]]]].
  exact Hrealization.
Qed.

Corollary successful_import_creates_no_runtime_effect :
  forall state localName identity state',
    importIdentity localName identity state = Some state' ->
    runtimeEffects state' = runtimeEffects state.
Proof.
  intros state localName identity state' Himport.
  pose proof
    (successful_import_changes_name_availability_only
      state localName identity state' Himport) as H.
  destruct H as [_ [_ [_ [_ [_ [_ Hruntime]]]]]].
  exact Hruntime.
Qed.

Theorem module_locator_does_not_define_resolved_identity :
  forall moduleA moduleB identity localName state,
    resolveSelectedExport moduleA (Some identity) localName state =
    resolveSelectedExport moduleB (Some identity) localName state.
Proof.
  reflexivity.
Qed.

Theorem duplicate_resolution_name_fails_closed :
  forall state localName identity existing,
    lookupBinding localName (resolutionBindings state) = Some existing ->
    importIdentity localName identity state = None.
Proof.
  intros state localName identity existing Hlookup.
  unfold importIdentity, insertBinding.
  rewrite Hlookup.
  reflexivity.
Qed.

Theorem unknown_export_fails_closed :
  forall moduleName localName state,
    resolveSelectedExport moduleName None localName state = None.
Proof.
  reflexivity.
Qed.
