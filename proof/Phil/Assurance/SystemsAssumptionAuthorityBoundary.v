From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  D-SYS-ASSUMPTION-AUTHORITY-01 — SYS-013 local graph/scope coherence is not
  itself imported assumption authority.

  Native correspondence:

  - Phil.Systems.AssumptionDependency verifies the exact required registry,
    forward and reverse dependency relations and the stage-local validity-scope
    revision carried on each edge.
  - Phil.Core.SystemsEvidencePreservation models the stronger Certified premise:
    every retained stage assumption carries accepted AssumptionAuthority.
  - Phil.Assurance.Verify checks the immutable assumption record selected by the
    manifest, including digest, permission and validity-context agreement.

  The missing application-level correspondence is therefore an explicit exact
  binding from each required StageAssumptionKey to the immutable assumption
  authority that was actually selected and permitted for the accepting context.
  A locally coherent stage plus a successful ID lookup is insufficient if that
  authority has different content, subject/boundary meaning, scope, selection,
  permission or current-validity state.

  This bounded proof keeps that imported premise explicit.  It does not add a
  richer SYS-013 representation, grant authority to caller-supplied values, or
  change any Phase 1 trusted-computing-base boundary.
*)

Definition StageAssumptionKey := nat.
Definition ImmutableAssumptionId := nat.
Definition DigestIdentity := nat.
Definition SubjectIdentity := nat.
Definition ScopeIdentity := nat.
Definition BoundaryIdentity := nat.

Record SystemsAssumptionAuthorityModel : Type :=
  mkSystemsAssumptionAuthorityModel {
    modelRequiredAssumption : StageAssumptionKey -> bool;
    modelStageScope : StageAssumptionKey -> option ScopeIdentity;
    modelLocalGraphCoherent : StageAssumptionKey -> bool;
    modelAuthorityMap : StageAssumptionKey -> option ImmutableAssumptionId;
    modelExpectedDigest : StageAssumptionKey -> DigestIdentity;
    modelExpectedSubject : StageAssumptionKey -> SubjectIdentity;
    modelExpectedBoundary : StageAssumptionKey -> BoundaryIdentity;
    modelAuthorityDigest : ImmutableAssumptionId -> option DigestIdentity;
    modelAuthoritySubject : ImmutableAssumptionId -> option SubjectIdentity;
    modelAuthorityScope : ImmutableAssumptionId -> option ScopeIdentity;
    modelAuthorityBoundary : ImmutableAssumptionId -> option BoundaryIdentity;
    modelAuthoritySelected : ImmutableAssumptionId -> bool;
    modelAuthorityPermitted : ImmutableAssumptionId -> bool;
    modelAuthorityCurrent : ImmutableAssumptionId -> bool
  }.

(*
  This is the strongest conclusion available from the bounded native SYS-013
  representation plus an external ID map: the key is required, has a nonempty
  local scope, its local dependency graph is coherent, and it names some
  immutable-assumption identity.  No semantic authority follows yet.
*)
Definition LocalStageBindingCoherent
  (model : SystemsAssumptionAuthorityModel) : Prop :=
  forall key,
    modelRequiredAssumption model key = true ->
    exists authority scope,
      modelAuthorityMap model key = Some authority /\
      modelStageScope model key = Some scope /\
      scope <> 0 /\
      modelLocalGraphCoherent model key = true.

(*
  Imported authority additionally ties the same required key to the selected
  immutable record and requires exact content, semantic subject/boundary, scope,
  manifest selection, verification-context permission and current validity.
*)
Definition ImportedAssumptionAuthorityPreserved
  (model : SystemsAssumptionAuthorityModel) : Prop :=
  forall key,
    modelRequiredAssumption model key = true ->
    exists authority scope,
      modelAuthorityMap model key = Some authority /\
      modelStageScope model key = Some scope /\
      scope <> 0 /\
      modelLocalGraphCoherent model key = true /\
      modelAuthorityDigest model authority =
        Some (modelExpectedDigest model key) /\
      modelAuthoritySubject model authority =
        Some (modelExpectedSubject model key) /\
      modelAuthorityScope model authority = Some scope /\
      modelAuthorityBoundary model authority =
        Some (modelExpectedBoundary model key) /\
      modelAuthoritySelected model authority = true /\
      modelAuthorityPermitted model authority = true /\
      modelAuthorityCurrent model authority = true.

Theorem imported_authority_implies_local_stage_binding :
  forall model,
    ImportedAssumptionAuthorityPreserved model ->
    LocalStageBindingCoherent model.
Proof.
  intros model Hauthority key Hrequired.
  pose proof (Hauthority key Hrequired) as Hbound.
  destruct Hbound as
    [authority [scope
      [Hmap
      [Hscope
      [Hpresent
      [Hlocal
      [Hdigest
      [Hsubject
      [HauthorityScope
      [Hboundary
      [Hselected
      [Hpermitted Hcurrent]]]]]]]]]]]].
  exists authority, scope.
  repeat split; assumption.
Qed.

Definition mismatchedScopeWitness : SystemsAssumptionAuthorityModel :=
  mkSystemsAssumptionAuthorityModel
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 300 else None)
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 10 else None)
    (fun key => if Nat.eqb key 1 then 100 else 0)
    (fun key => if Nat.eqb key 1 then 200 else 0)
    (fun key => if Nat.eqb key 1 then 400 else 0)
    (fun authority => if Nat.eqb authority 10 then Some 100 else None)
    (fun authority => if Nat.eqb authority 10 then Some 200 else None)
    (fun authority => if Nat.eqb authority 10 then Some 301 else None)
    (fun authority => if Nat.eqb authority 10 then Some 400 else None)
    (fun authority => Nat.eqb authority 10)
    (fun authority => Nat.eqb authority 10)
    (fun authority => Nat.eqb authority 10).

Theorem mismatched_scope_still_has_local_stage_binding :
  LocalStageBindingCoherent mismatchedScopeWitness.
Proof.
  intros key Hrequired.
  cbn in Hrequired.
  apply Nat.eqb_eq in Hrequired.
  subst key.
  exists 10, 300.
  repeat split; try reflexivity.
  discriminate.
Qed.

Theorem local_stage_binding_does_not_establish_imported_authority :
  ~ ImportedAssumptionAuthorityPreserved mismatchedScopeWitness.
Proof.
  intro Hauthority.
  pose proof (Hauthority 1 eq_refl) as Hbound.
  destruct Hbound as
    [authority [scope
      [Hmap
      [Hscope
      [Hpresent
      [Hlocal
      [Hdigest
      [Hsubject
      [HauthorityScope
      [Hboundary
      [Hselected
      [Hpermitted Hcurrent]]]]]]]]]]]].
  cbn in Hmap, Hscope, HauthorityScope.
  inversion Hmap; subst authority.
  inversion Hscope; subst scope.
  cbn in HauthorityScope.
  discriminate.
Qed.

Definition exactAuthorityWitness : SystemsAssumptionAuthorityModel :=
  mkSystemsAssumptionAuthorityModel
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 300 else None)
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 10 else None)
    (fun key => if Nat.eqb key 1 then 100 else 0)
    (fun key => if Nat.eqb key 1 then 200 else 0)
    (fun key => if Nat.eqb key 1 then 400 else 0)
    (fun authority => if Nat.eqb authority 10 then Some 100 else None)
    (fun authority => if Nat.eqb authority 10 then Some 200 else None)
    (fun authority => if Nat.eqb authority 10 then Some 300 else None)
    (fun authority => if Nat.eqb authority 10 then Some 400 else None)
    (fun authority => Nat.eqb authority 10)
    (fun authority => Nat.eqb authority 10)
    (fun authority => Nat.eqb authority 10).

Theorem exact_authority_witness_preserves_required_stage_assumption :
  ImportedAssumptionAuthorityPreserved exactAuthorityWitness.
Proof.
  intros key Hrequired.
  cbn in Hrequired.
  apply Nat.eqb_eq in Hrequired.
  subst key.
  exists 10, 300.
  repeat split; try reflexivity.
  discriminate.
Qed.

Theorem exact_authority_witness_retains_local_stage_binding :
  LocalStageBindingCoherent exactAuthorityWitness.
Proof.
  apply imported_authority_implies_local_stage_binding.
  exact exact_authority_witness_preserves_required_stage_assumption.
Qed.
