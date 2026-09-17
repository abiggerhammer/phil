From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import ArchitectureIdentity.
From Phil.Surface Require Import
  GrammarAstSessionRecursiveIdentityCarrierTotality.

(*
  Pair the declaration-local recursive ordinals from #1150/#1151 with the
  stable declaration lineage already certified by ArchitectureIdentity.

  This layer deliberately stays representation-neutral.  The certified
  architecture model exposes declaration identity as a semantic nat; concrete
  Text encodings and Core Name construction remain production correspondence
  boundaries.  No session traversal is needed here: one declaration root scopes
  the whole already-certified recursive identity carrier.
*)

Record Phase1SurfaceRecursiveSemanticKey : Type := {
  phase1_recursive_semantic_key_declaration : nat;
  phase1_recursive_semantic_key_ordinal : nat
}.

Definition phase1_surface_recursive_semantic_key
  (declaration_key ordinal : nat)
  : Phase1SurfaceRecursiveSemanticKey :=
  {| phase1_recursive_semantic_key_declaration := declaration_key;
     phase1_recursive_semantic_key_ordinal := ordinal |}.

Record Phase1SurfaceRecursiveDeclarationIdentityCarrier : Type := {
  phase1_recursive_declaration_key : nat;
  phase1_recursive_declaration_identity_carrier :
    Phase1SurfaceRecursiveIdentityCarrier
}.

Definition phase1_surface_root_recursive_identity_carrier
  (declaration : DeclarationIdentity)
  (carrier : Phase1SurfaceRecursiveIdentityCarrier)
  : Phase1SurfaceRecursiveDeclarationIdentityCarrier :=
  {| phase1_recursive_declaration_key := identityDeclarationKey declaration;
     phase1_recursive_declaration_identity_carrier := carrier |}.

Definition phase1_surface_recursive_declaration_identity_carrier_tree
  (carrier : Phase1SurfaceRecursiveDeclarationIdentityCarrier) : ParseTree :=
  phase1_surface_recursive_identity_carrier_tree
    (phase1_recursive_declaration_identity_carrier carrier).

Definition phase1_surface_recursive_declaration_identity_key
  (carrier : Phase1SurfaceRecursiveDeclarationIdentityCarrier)
  (ordinal : nat)
  : Phase1SurfaceRecursiveSemanticKey :=
  phase1_surface_recursive_semantic_key
    (phase1_recursive_declaration_key carrier)
    ordinal.

Theorem phase1_surface_root_recursive_identity_carrier_tree_preserved :
  forall declaration carrier,
    phase1_surface_recursive_declaration_identity_carrier_tree
      (phase1_surface_root_recursive_identity_carrier declaration carrier) =
    phase1_surface_recursive_identity_carrier_tree carrier.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_recursive_semantic_key_ordinal_injective :
  forall declaration_key left right,
    phase1_surface_recursive_semantic_key declaration_key left =
    phase1_surface_recursive_semantic_key declaration_key right ->
    left = right.
Proof.
  intros declaration_key left right Heq.
  exact (f_equal phase1_recursive_semantic_key_ordinal Heq).
Qed.

Theorem phase1_surface_recursive_semantic_key_declaration_injective :
  forall left right ordinal,
    phase1_surface_recursive_semantic_key left ordinal =
    phase1_surface_recursive_semantic_key right ordinal ->
    left = right.
Proof.
  intros left right ordinal Heq.
  exact (f_equal phase1_recursive_semantic_key_declaration Heq).
Qed.

Theorem phase1_surface_recursive_semantic_key_presentation_invariant :
  forall old_name old_module new_name new_module key interface_sem definition_sem
    ordinal,
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey
        (deriveDeclarationIdentity
          {| declarationPresentationName := old_name;
             declarationPresentationModule := old_module;
             declarationKey := key;
             declarationInterfaceSemantics := interface_sem;
             declarationDefinitionSemantics := definition_sem |}))
      ordinal =
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey
        (deriveDeclarationIdentity
          {| declarationPresentationName := new_name;
             declarationPresentationModule := new_module;
             declarationKey := key;
             declarationInterfaceSemantics := interface_sem;
             declarationDefinitionSemantics := definition_sem |}))
      ordinal.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_recursive_semantic_key_interface_revision_invariant :
  forall name module_path key old_interface new_interface old_definition
    new_definition ordinal,
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey
        (deriveDeclarationIdentity
          {| declarationPresentationName := name;
             declarationPresentationModule := module_path;
             declarationKey := key;
             declarationInterfaceSemantics := old_interface;
             declarationDefinitionSemantics := old_definition |}))
      ordinal =
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey
        (deriveDeclarationIdentity
          {| declarationPresentationName := name;
             declarationPresentationModule := module_path;
             declarationKey := key;
             declarationInterfaceSemantics := new_interface;
             declarationDefinitionSemantics := new_definition |}))
      ordinal.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_recursive_semantic_key_definition_revision_invariant :
  forall name module_path key interface_sem old_definition new_definition ordinal,
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey
        (deriveDeclarationIdentity
          {| declarationPresentationName := name;
             declarationPresentationModule := module_path;
             declarationKey := key;
             declarationInterfaceSemantics := interface_sem;
             declarationDefinitionSemantics := old_definition |}))
      ordinal =
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey
        (deriveDeclarationIdentity
          {| declarationPresentationName := name;
             declarationPresentationModule := module_path;
             declarationKey := key;
             declarationInterfaceSemantics := interface_sem;
             declarationDefinitionSemantics := new_definition |}))
      ordinal.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_recursive_declaration_identity_carrier_total :
  forall declaration certificate,
    exists rooted carrier,
      phase1_surface_normalize_recursive_identity_carrier certificate =
        Some carrier /\
      rooted = phase1_surface_root_recursive_identity_carrier declaration carrier /\
      phase1_surface_recursive_declaration_identity_carrier_tree rooted =
        phase1_surface_recursive_identity_certificate_tree certificate /\
      phase1_recursive_declaration_key rooted =
        identityDeclarationKey declaration.
Proof.
  intros declaration certificate.
  destruct
    (phase1_surface_normalize_recursive_identity_carrier_total certificate)
    as [carrier [Hnormalize Htree]].
  exists (phase1_surface_root_recursive_identity_carrier declaration carrier), carrier.
  repeat split.
  - exact Hnormalize.
  - reflexivity.
  - cbn.
    exact Htree.
  - reflexivity.
Qed.
