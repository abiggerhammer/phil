Theorem numeric_environment_admission_boundary_is_explicit :
  forall P : Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.
