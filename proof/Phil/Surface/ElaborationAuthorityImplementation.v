From Stdlib Require Import Bool.Bool.

Inductive SurfaceElaborationDecision : Type :=
| SurfaceElaborationAccepted
| SurfaceElaborationRejected.

Definition surfaceElaborationFactsb
  (outcomeExact identityExact noIdentityRecompute noEvidence
   noAuthority noQualification noAssumption noRealizationChoice
   attributesClosed : bool) : bool :=
  outcomeExact &&
  identityExact &&
  noIdentityRecompute &&
  noEvidence &&
  noAuthority &&
  noQualification &&
  noAssumption &&
  noRealizationChoice &&
  attributesClosed.

Definition decideSurfaceElaboration
  (outcomeExact identityExact noIdentityRecompute noEvidence
   noAuthority noQualification noAssumption noRealizationChoice
   attributesClosed : bool) : SurfaceElaborationDecision :=
  if surfaceElaborationFactsb
      outcomeExact identityExact noIdentityRecompute noEvidence
      noAuthority noQualification noAssumption noRealizationChoice
      attributesClosed
  then SurfaceElaborationAccepted
  else SurfaceElaborationRejected.

Theorem exact_surface_elaboration_accepts :
  decideSurfaceElaboration
    true true true true true true true true true =
  SurfaceElaborationAccepted.
Proof. reflexivity. Qed.

Theorem category_or_competence_substitution_rejects :
  decideSurfaceElaboration
    false true true true true true true true true =
  SurfaceElaborationRejected.
Proof. reflexivity. Qed.

Theorem identity_substitution_or_recomputation_rejects :
  decideSurfaceElaboration
    true false true true true true true true true =
      SurfaceElaborationRejected /\
  decideSurfaceElaboration
    true true false true true true true true true =
      SurfaceElaborationRejected.
Proof. split; reflexivity. Qed.

Theorem invented_semantic_authority_rejects :
  decideSurfaceElaboration
    true true true false true true true true true =
      SurfaceElaborationRejected /\
  decideSurfaceElaboration
    true true true true false true true true true =
      SurfaceElaborationRejected /\
  decideSurfaceElaboration
    true true true true true false true true true =
      SurfaceElaborationRejected /\
  decideSurfaceElaboration
    true true true true true true false true true =
      SurfaceElaborationRejected /\
  decideSurfaceElaboration
    true true true true true true true false true =
      SurfaceElaborationRejected.
Proof. repeat split; reflexivity. Qed.

Theorem open_semantic_attribute_namespace_rejects :
  decideSurfaceElaboration
    true true true true true true true true false =
  SurfaceElaborationRejected.
Proof. reflexivity. Qed.
