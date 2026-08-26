From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import CallableRefinement CallableRecursion.

(* PHIL-CALL-REC-IMPL-001 — executable production correspondence for CALL-013. *)

Fixpoint keyOccursb {D Key : Type}
  (eqKey : Key -> Key -> bool)
  (keyOf : D -> Key)
  (key : Key)
  (definitions : list D) : bool :=
  match definitions with
  | nil => false
  | definition :: rest =>
      eqKey key (keyOf definition) || keyOccursb eqKey keyOf key rest
  end.

Definition publicProjection {D Key Surface : Type}
  (keyOf : D -> Key)
  (surfaceOf : D -> Surface)
  (definitions : list D) : list (Key * Surface) :=
  map (fun definition => (keyOf definition, surfaceOf definition)) definitions.

Fixpoint stabilizePublic {D Key Surface : Type}
  (eqKey : Key -> Key -> bool)
  (keyOf : D -> Key)
  (surfaceOf : D -> Surface)
  (definitions : list D) : option (list (Key * Surface)) :=
  match definitions with
  | nil => Some nil
  | definition :: rest =>
      if keyOccursb eqKey keyOf (keyOf definition) rest then None
      else
        match stabilizePublic eqKey keyOf surfaceOf rest with
        | None => None
        | Some environment =>
            Some ((keyOf definition, surfaceOf definition) :: environment)
        end
  end.

Lemma key_occursb_true_iff_in :
  forall (D Key : Type)
      (eqKey : Key -> Key -> bool)
      (keyOf : D -> Key),
    (forall first second, eqKey first second = true <-> first = second) ->
    forall key definitions,
      keyOccursb eqKey keyOf key definitions = true <->
      In key (map keyOf definitions).
Proof.
  intros D Key eqKey keyOf Heq key definitions.
  induction definitions as [| definition rest IH].
  - cbn. split; intro H; [discriminate | contradiction].
  - cbn. rewrite orb_true_iff, Heq, IH.
    split; intros [Hhead | Hrest].
    + left. symmetry. exact Hhead.
    + right. exact Hrest.
    + left. symmetry. exact Hhead.
    + right. exact Hrest.
Qed.

Theorem stabilize_public_output_is_exact_projection :
  forall (D Key Surface : Type)
      (eqKey : Key -> Key -> bool)
      (keyOf : D -> Key)
      (surfaceOf : D -> Surface)
      definitions environment,
    stabilizePublic eqKey keyOf surfaceOf definitions = Some environment ->
    environment = publicProjection keyOf surfaceOf definitions.
Proof.
  intros D Key Surface eqKey keyOf surfaceOf definitions.
  induction definitions as [| definition rest IH]; intros environment Hstable.
  - cbn in Hstable. inversion Hstable. reflexivity.
  - cbn in Hstable.
    destruct (keyOccursb eqKey keyOf (keyOf definition) rest) eqn:Hoccurs;
      try discriminate.
    destruct (stabilizePublic eqKey keyOf surfaceOf rest) as [tailEnvironment|]
      eqn:Htail; try discriminate.
    inversion Hstable; subst environment.
    unfold publicProjection in *; cbn.
    f_equal.
    eapply IH. reflexivity.
Qed.

Theorem stabilize_public_success_implies_unique_keys :
  forall (D Key Surface : Type)
      (eqKey : Key -> Key -> bool)
      (keyOf : D -> Key)
      (surfaceOf : D -> Surface),
    (forall first second, eqKey first second = true <-> first = second) ->
    forall definitions environment,
      stabilizePublic eqKey keyOf surfaceOf definitions = Some environment ->
      NoDup (map keyOf definitions).
Proof.
  intros D Key Surface eqKey keyOf surfaceOf Heq definitions.
  induction definitions as [| definition rest IH]; intros environment Hstable.
  - constructor.
  - cbn in Hstable.
    destruct (keyOccursb eqKey keyOf (keyOf definition) rest) eqn:Hoccurs;
      try discriminate.
    destruct (stabilizePublic eqKey keyOf surfaceOf rest) as [tailEnvironment|]
      eqn:Htail; try discriminate.
    constructor.
    + intro Hin.
      pose proof (proj2
        (key_occursb_true_iff_in D Key eqKey keyOf Heq
          (keyOf definition) rest) Hin) as Htrue.
      rewrite Hoccurs in Htrue. discriminate.
    + eapply IH. reflexivity.
Qed.

Theorem unique_keys_imply_stabilize_public_success :
  forall (D Key Surface : Type)
      (eqKey : Key -> Key -> bool)
      (keyOf : D -> Key)
      (surfaceOf : D -> Surface),
    (forall first second, eqKey first second = true <-> first = second) ->
    forall definitions,
      NoDup (map keyOf definitions) ->
      exists environment,
        stabilizePublic eqKey keyOf surfaceOf definitions = Some environment.
Proof.
  intros D Key Surface eqKey keyOf surfaceOf Heq definitions Hunique.
  induction definitions as [| definition rest IH].
  - exists nil. reflexivity.
  - inversion Hunique as [| head tail Hnotin Htail].
    assert (Hoccurs : keyOccursb eqKey keyOf (keyOf definition) rest = false).
    {
      destruct (keyOccursb eqKey keyOf (keyOf definition) rest) eqn:Hvalue.
      - exfalso. apply Hnotin.
        apply (proj1
          (key_occursb_true_iff_in D Key eqKey keyOf Heq
            (keyOf definition) rest)). exact Hvalue.
      - reflexivity.
    }
    destruct (IH Htail) as [tailEnvironment Hstable].
    cbn. rewrite Hoccurs, Hstable.
    eexists. reflexivity.
Qed.

Theorem stabilize_public_success_iff_unique_keys :
  forall (D Key Surface : Type)
      (eqKey : Key -> Key -> bool)
      (keyOf : D -> Key)
      (surfaceOf : D -> Surface),
    (forall first second, eqKey first second = true <-> first = second) ->
    forall definitions,
      (exists environment,
        stabilizePublic eqKey keyOf surfaceOf definitions = Some environment) <->
      NoDup (map keyOf definitions).
Proof.
  intros D Key Surface eqKey keyOf surfaceOf Heq definitions.
  split.
  - intros [environment Hstable].
    eapply stabilize_public_success_implies_unique_keys; eauto.
  - intro Hunique.
    eapply unique_keys_imply_stabilize_public_success; eauto.
Qed.

Fixpoint lookupPublic {Key Surface : Type}
  (eqKey : Key -> Key -> bool)
  (key : Key)
  (environment : list (Key * Surface)) : option Surface :=
  match environment with
  | nil => None
  | (entryKey, surface) :: rest =>
      if eqKey key entryKey then Some surface else lookupPublic eqKey key rest
  end.

Inductive RecursiveLookupDecision (Surface : Type) : Type :=
| RecursiveLookupAccepted (surface : Surface)
| RecursiveLookupUnknown
| RecursiveLookupRevisionMismatch (surface : Surface).

Arguments RecursiveLookupAccepted {Surface} _.
Arguments RecursiveLookupUnknown {Surface}.
Arguments RecursiveLookupRevisionMismatch {Surface} _.

Definition decideRecursiveLookup {Key Surface : Type}
  (eqKey : Key -> Key -> bool)
  (key : Key)
  (revisionMatches : Surface -> bool)
  (environment : list (Key * Surface)) : RecursiveLookupDecision Surface :=
  match lookupPublic eqKey key environment with
  | None => RecursiveLookupUnknown
  | Some surface =>
      if revisionMatches surface
      then RecursiveLookupAccepted surface
      else RecursiveLookupRevisionMismatch surface
  end.

Lemma lookup_public_some_is_member :
  forall (Key Surface : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (key : Key)
        (environment : list (Key * Surface))
        (surface : Surface),
      lookupPublic eqKey key environment = Some surface ->
      In (key, surface) environment.
Proof.
  intros Key Surface eqKey Heq key environment.
  induction environment as [| [entryKey entrySurface] rest IH];
    intros surface Hlookup.
  - discriminate.
  - cbn in Hlookup.
    destruct (eqKey key entryKey) eqn:Hkey.
    + inversion Hlookup; subst surface.
      left. apply (proj1 (Heq key entryKey)) in Hkey.
      subst entryKey. reflexivity.
    + right. apply IH. exact Hlookup.
Qed.

Theorem accepted_recursive_lookup_has_exact_public_member :
  forall (Key Surface : Type)
      (eqKey : Key -> Key -> bool),
    (forall first second : Key, eqKey first second = true <-> first = second) ->
    forall (key : Key)
        (revisionMatches : Surface -> bool)
        (environment : list (Key * Surface))
        (surface : Surface),
      decideRecursiveLookup eqKey key revisionMatches environment =
        RecursiveLookupAccepted surface ->
      In (key, surface) environment /\ revisionMatches surface = true.
Proof.
  intros Key Surface eqKey Heq key revisionMatches environment surface Hdecision.
  unfold decideRecursiveLookup in Hdecision.
  destruct (lookupPublic eqKey key environment) as [found|] eqn:Hlookup;
    try discriminate.
  destruct (revisionMatches found) eqn:Hrevision; try discriminate.
  inversion Hdecision; subst found.
  split.
  - eapply lookup_public_some_is_member; eauto.
  - exact Hrevision.
Qed.

Theorem successful_production_stabilization_refines_call013 :
  forall (eqKey : NamedCallableKey -> NamedCallableKey -> bool),
    (forall first second, eqKey first second = true <-> first = second) ->
    forall definitions environment,
      stabilizePublic eqKey definitionKey definitionPublicSurface definitions = Some environment ->
      StabilizationAccepted definitions.
Proof.
  intros eqKey Heq definitions environment Hstable.
  unfold StabilizationAccepted.
  eapply stabilize_public_success_implies_unique_keys; eauto.
Qed.

Theorem accepted_production_lookup_refines_call013 :
  forall (eqKey : NamedCallableKey -> NamedCallableKey -> bool),
    (forall first second, eqKey first second = true <-> first = second) ->
    forall definitions environment key expectedRevision revisionMatches surface,
      stabilizePublic eqKey definitionKey definitionPublicSurface definitions = Some environment ->
      (forall candidate,
        revisionMatches candidate = true ->
        surfaceInterfaceRevision candidate = expectedRevision) ->
      decideRecursiveLookup eqKey key revisionMatches environment =
        RecursiveLookupAccepted surface ->
      RecursiveLookup definitions key expectedRevision surface.
Proof.
  intros eqKey Heq definitions environment key expectedRevision revisionMatches surface
    Hstable Hrevision Hdecision.
  pose proof (stabilize_public_output_is_exact_projection
    NamedCallableDefinition NamedCallableKey CallableRefinementSurface
    eqKey definitionKey definitionPublicSurface definitions environment Hstable)
    as Henvironment.
  pose proof (accepted_recursive_lookup_has_exact_public_member
    NamedCallableKey CallableRefinementSurface eqKey Heq
    key revisionMatches environment surface Hdecision)
    as [Hmember HrevisionMatch].
  unfold RecursiveLookup.
  split.
  - unfold StabilizedLookup.
    change (In (key, surface)
      (publicProjection definitionKey definitionPublicSurface definitions)).
    rewrite <- Henvironment.
    exact Hmember.
  - apply Hrevision. exact HrevisionMatch.
Qed.
