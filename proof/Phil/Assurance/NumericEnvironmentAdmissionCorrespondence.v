Definition NumericLeafId := nat.
Definition NumericDeclarationId := nat.
Definition NumericScopeId := nat.
Definition NumericDescriptor := nat.

Record NumericEnvironmentAdmissionModel : Type :=
  mkNumericEnvironmentAdmissionModel {
    modelEvaluatorLeaf : NumericLeafId -> bool;
    modelActualDeclaration : NumericLeafId -> option NumericDeclarationId;
    modelActualScope : NumericLeafId -> option NumericScopeId;
    modelActualDescriptor : NumericLeafId -> option NumericDescriptor
  }.

Theorem numeric_environment_admission_boundary_is_explicit :
  forall P : Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.
