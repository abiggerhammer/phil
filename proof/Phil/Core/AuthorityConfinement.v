From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import AuthorityAttenuation.

(*
  PHIL-AUTH-CONFINE-001 — reachable and provider authority confinement.

  This normalized model closes the Phase 1 authority-confinement theorem family
  over the landed pure-Phil closure checker (AUTH-004) and provider/foreign
  authority qualification layer (PROV-009 / AUTH-006).

  Authority identities are exact subject/operation pairs. Concrete Haskell Set,
  Map, list-fold, Text-key, origin-diagnostic, and evidence-key representations
  remain correspondence boundaries. External evidence, assumptions, and TCB
  boundaries are represented only as explicit conditional dispositions; their
  truth or policy admissibility is not asserted by this Rocq model.
*)

Record AuthorityUse : Type := mkAuthorityUse {
  authorityUseSubject : nat;
  authorityUseOperation : nat
}.

Definition AuthoritySet : Type := AuthorityUse -> bool.

Definition authoritySubset
  (smaller larger : AuthoritySet) : Prop :=
  forall authority,
    smaller authority = true ->
    larger authority = true.

Definition closureAuthorityConfinement
  (reachable public exercised : AuthoritySet) : Prop :=
  authoritySubset public reachable /\
  authoritySubset exercised reachable /\
  authoritySubset exercised public.

Definition negativeAuthorityClaimAllowed
  (reachable : AuthoritySet)
  (authority : AuthorityUse) : Prop :=
  reachable authority = false.

Inductive ProviderAuthoritySubject : Type :=
| SemanticProviderAuthoritySubject : nat -> nat -> ProviderAuthoritySubject
| OpaqueForeignProviderAuthoritySubject : nat -> nat -> ProviderAuthoritySubject.

Inductive ProviderAuthorityInventoryBasis : Type :=
| CheckedPurePhilAuthorityInventory
| ForeignAuthorityInventoryByEvidence
| ForeignAuthorityInventoryAssumption
| ForeignAuthorityInventoryTcbBoundary
| ForeignAuthorityInventoryFromAbiShape.

Inductive ProviderExtraAuthorityDisposition : Type :=
| ExtraAuthorityStaticallyConfined
| ExtraAuthorityExternallyConfined
| ExtraAuthorityAssumptionDependent
| ExtraAuthorityTcbBoundary
| ExtraAuthorityAssertedAbsentFromAbi.

Definition providerAuthoritySubjectAccepted
  (subject : ProviderAuthoritySubject)
  (checkedInterface checkedDefinition : nat) : Prop :=
  match subject with
  | SemanticProviderAuthoritySubject interface definition =>
      interface = checkedInterface /\
      definition = checkedDefinition
  | OpaqueForeignProviderAuthoritySubject _ _ => True
  end.

Definition providerAuthorityInventoryBasisAllowed
  (subject : ProviderAuthoritySubject)
  (basis : ProviderAuthorityInventoryBasis) : bool :=
  match subject, basis with
  | SemanticProviderAuthoritySubject _ _, CheckedPurePhilAuthorityInventory => true
  | OpaqueForeignProviderAuthoritySubject _ _, ForeignAuthorityInventoryByEvidence => true
  | OpaqueForeignProviderAuthoritySubject _ _, ForeignAuthorityInventoryAssumption => true
  | OpaqueForeignProviderAuthoritySubject _ _, ForeignAuthorityInventoryTcbBoundary => true
  | _, _ => false
  end.

Definition providerExtraAuthority
  (internal clientVisible : AuthoritySet)
  (authority : AuthorityUse) : bool :=
  andb (internal authority) (negb (clientVisible authority)).

Definition providerStaticSummariesAllowed
  (internal clientVisible staticReachable staticPublic staticExercised : AuthoritySet)
  : Prop :=
  authoritySubset staticReachable internal /\
  authoritySubset staticPublic clientVisible /\
  authoritySubset staticExercised clientVisible.

Definition providerExtraDispositionAllowed
  (subject : ProviderAuthoritySubject)
  (staticReachable staticPublic staticExercised : AuthoritySet)
  (authority : AuthorityUse)
  (disposition : ProviderExtraAuthorityDisposition) : bool :=
  match disposition with
  | ExtraAuthorityStaticallyConfined =>
      match subject with
      | SemanticProviderAuthoritySubject _ _ =>
          andb
            (staticReachable authority)
            (andb
              (negb (staticPublic authority))
              (negb (staticExercised authority)))
      | OpaqueForeignProviderAuthoritySubject _ _ => false
      end
  | ExtraAuthorityExternallyConfined => true
  | ExtraAuthorityAssumptionDependent => true
  | ExtraAuthorityTcbBoundary => true
  | ExtraAuthorityAssertedAbsentFromAbi => false
  end.

Definition providerDispositionDomainExact
  (internal clientVisible : AuthoritySet)
  (dispositions : AuthorityUse -> option ProviderExtraAuthorityDisposition)
  : Prop :=
  forall authority,
    providerExtraAuthority internal clientVisible authority = true <->
    exists disposition, dispositions authority = Some disposition.

Definition providerDispositionsAllowed
  (subject : ProviderAuthoritySubject)
  (internal clientVisible staticReachable staticPublic staticExercised : AuthoritySet)
  (dispositions : AuthorityUse -> option ProviderExtraAuthorityDisposition)
  : Prop :=
  providerDispositionDomainExact internal clientVisible dispositions /\
  (forall authority disposition,
    dispositions authority = Some disposition ->
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority disposition = true).

Definition providerAuthorityQualificationAllowed
  (subject : ProviderAuthoritySubject)
  (checkedInterface checkedDefinition : nat)
  (basis : ProviderAuthorityInventoryBasis)
  (clientVisible internal staticReachable staticPublic staticExercised : AuthoritySet)
  (dispositions : AuthorityUse -> option ProviderExtraAuthorityDisposition)
  : Prop :=
  providerAuthoritySubjectAccepted subject checkedInterface checkedDefinition /\
  providerAuthorityInventoryBasisAllowed subject basis = true /\
  providerStaticSummariesAllowed
    internal clientVisible staticReachable staticPublic staticExercised /\
  providerDispositionsAllowed
    subject internal clientVisible staticReachable staticPublic staticExercised
    dispositions.

Theorem closure_public_authority_must_be_reachable :
  forall reachable public exercised,
    closureAuthorityConfinement reachable public exercised ->
    authoritySubset public reachable.
Proof.
  intros reachable public exercised Hchecked.
  unfold closureAuthorityConfinement in Hchecked.
  destruct Hchecked as [Hpublic _].
  exact Hpublic.
Qed.

Theorem closure_exercised_authority_must_be_reachable :
  forall reachable public exercised,
    closureAuthorityConfinement reachable public exercised ->
    authoritySubset exercised reachable.
Proof.
  intros reachable public exercised Hchecked.
  unfold closureAuthorityConfinement in Hchecked.
  destruct Hchecked as [_ [Hexercised _]].
  exact Hexercised.
Qed.

Theorem closure_exercise_must_stay_within_public_authority :
  forall reachable public exercised,
    closureAuthorityConfinement reachable public exercised ->
    authoritySubset exercised public.
Proof.
  intros reachable public exercised Hchecked.
  unfold closureAuthorityConfinement in Hchecked.
  destruct Hchecked as [_ [_ Hpublic]].
  exact Hpublic.
Qed.

Theorem broader_internal_authority_may_be_confined :
  forall reachable public exercised,
    authoritySubset public reachable ->
    authoritySubset exercised reachable ->
    authoritySubset exercised public ->
    closureAuthorityConfinement reachable public exercised.
Proof.
  intros reachable public exercised Hpublic Hexercised Hconfined.
  unfold closureAuthorityConfinement.
  repeat split; assumption.
Qed.

Theorem negative_authority_claim_checks_reachable_authority :
  forall reachable authority,
    negativeAuthorityClaimAllowed reachable authority ->
    reachable authority = false.
Proof.
  intros reachable authority Hnegative.
  exact Hnegative.
Qed.

Theorem hidden_reachable_authority_refutes_negative_claim :
  forall reachable authority,
    reachable authority = true ->
    negativeAuthorityClaimAllowed reachable authority ->
    False.
Proof.
  intros reachable authority Hreachable Hnegative.
  unfold negativeAuthorityClaimAllowed in Hnegative.
  rewrite Hreachable in Hnegative.
  discriminate.
Qed.

Theorem public_absence_alone_cannot_establish_negative_authority :
  forall authority : AuthorityUse,
    exists reachable public : AuthoritySet,
      public authority = false /\
      reachable authority = true.
Proof.
  intros authority.
  exists (fun _ => true), (fun _ => false).
  split; reflexivity.
Qed.

Theorem authority_use_subject_is_identity_bearing :
  forall firstSubject secondSubject operation,
    firstSubject <> secondSubject ->
    mkAuthorityUse firstSubject operation <>
    mkAuthorityUse secondSubject operation.
Proof.
  intros firstSubject secondSubject operation Hdifferent Hequal.
  inversion Hequal.
  contradiction.
Qed.

Theorem semantic_provider_authority_binds_exact_revisions :
  forall interface definition checkedInterface checkedDefinition,
    providerAuthoritySubjectAccepted
      (SemanticProviderAuthoritySubject interface definition)
      checkedInterface checkedDefinition ->
    interface = checkedInterface /\
    definition = checkedDefinition.
Proof.
  intros interface definition checkedInterface checkedDefinition Haccepted.
  exact Haccepted.
Qed.

Theorem semantic_provider_requires_pure_phil_inventory_basis :
  forall interface definition basis,
    providerAuthorityInventoryBasisAllowed
      (SemanticProviderAuthoritySubject interface definition)
      basis = true ->
    basis = CheckedPurePhilAuthorityInventory.
Proof.
  intros interface definition basis Hallowed.
  destruct basis; simpl in Hallowed; try discriminate; reflexivity.
Qed.

Theorem opaque_provider_cannot_claim_pure_phil_inventory :
  forall interface boundary,
    providerAuthorityInventoryBasisAllowed
      (OpaqueForeignProviderAuthoritySubject interface boundary)
      CheckedPurePhilAuthorityInventory = false.
Proof.
  reflexivity.
Qed.

Theorem foreign_provider_inventory_requires_evidence_assumption_or_tcb :
  forall interface boundary basis,
    providerAuthorityInventoryBasisAllowed
      (OpaqueForeignProviderAuthoritySubject interface boundary)
      basis = true ->
    basis = ForeignAuthorityInventoryByEvidence \/
    basis = ForeignAuthorityInventoryAssumption \/
    basis = ForeignAuthorityInventoryTcbBoundary.
Proof.
  intros interface boundary basis Hallowed.
  destruct basis; simpl in Hallowed; try discriminate.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.

Theorem abi_shape_never_establishes_authority_inventory :
  forall subject,
    providerAuthorityInventoryBasisAllowed
      subject ForeignAuthorityInventoryFromAbiShape = false.
Proof.
  intros subject.
  destruct subject; reflexivity.
Qed.

Theorem provider_static_reachability_must_be_declared_internal :
  forall subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions,
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions ->
    authoritySubset staticReachable internal.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions Hchecked.
  unfold providerAuthorityQualificationAllowed in Hchecked.
  destruct Hchecked as [_ [_ [Hstatic _]]].
  unfold providerStaticSummariesAllowed in Hstatic.
  destruct Hstatic as [Hreachable _].
  exact Hreachable.
Qed.

Theorem provider_static_public_authority_must_be_client_visible :
  forall subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions,
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions ->
    authoritySubset staticPublic clientVisible.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions Hchecked.
  unfold providerAuthorityQualificationAllowed in Hchecked.
  destruct Hchecked as [_ [_ [Hstatic _]]].
  unfold providerStaticSummariesAllowed in Hstatic.
  destruct Hstatic as [_ [Hpublic _]].
  exact Hpublic.
Qed.

Theorem provider_static_exercise_must_be_client_visible :
  forall subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions,
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions ->
    authoritySubset staticExercised clientVisible.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions Hchecked.
  unfold providerAuthorityQualificationAllowed in Hchecked.
  destruct Hchecked as [_ [_ [Hstatic _]]].
  unfold providerStaticSummariesAllowed in Hstatic.
  destruct Hstatic as [_ [_ Hexercised]].
  exact Hexercised.
Qed.

Theorem every_extra_internal_authority_has_exact_disposition :
  forall subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions authority,
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions ->
    providerExtraAuthority internal clientVisible authority = true ->
    exists disposition, dispositions authority = Some disposition.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions authority Hchecked Hextra.
  unfold providerAuthorityQualificationAllowed in Hchecked.
  destruct Hchecked as [_ [_ [_ Hdispositions]]].
  unfold providerDispositionsAllowed in Hdispositions.
  destruct Hdispositions as [Hdomain _].
  apply (proj1 (Hdomain authority)).
  exact Hextra.
Qed.

Theorem dispositions_cannot_be_invented_for_non_extra_authority :
  forall subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions authority disposition,
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions ->
    dispositions authority = Some disposition ->
    providerExtraAuthority internal clientVisible authority = true.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions authority disposition Hchecked Hdisposition.
  unfold providerAuthorityQualificationAllowed in Hchecked.
  destruct Hchecked as [_ [_ [_ Hdispositions]]].
  unfold providerDispositionsAllowed in Hdispositions.
  destruct Hdispositions as [Hdomain _].
  apply (proj2 (Hdomain authority)).
  exists disposition.
  exact Hdisposition.
Qed.

Theorem every_recorded_extra_disposition_must_be_admissible :
  forall subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions authority disposition,
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions ->
    dispositions authority = Some disposition ->
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority disposition = true.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions authority disposition Hchecked Hdisposition.
  unfold providerAuthorityQualificationAllowed in Hchecked.
  destruct Hchecked as [_ [_ [_ Hdispositions]]].
  unfold providerDispositionsAllowed in Hdispositions.
  destruct Hdispositions as [_ Hadmissible].
  apply (Hadmissible authority disposition).
  exact Hdisposition.
Qed.

Theorem pure_static_confinement_requires_hidden_reachable_unexercised_authority :
  forall interface definition staticReachable staticPublic staticExercised authority,
    providerExtraDispositionAllowed
      (SemanticProviderAuthoritySubject interface definition)
      staticReachable staticPublic staticExercised
      authority ExtraAuthorityStaticallyConfined = true ->
    staticReachable authority = true /\
    staticPublic authority = false /\
    staticExercised authority = false.
Proof.
  intros interface definition staticReachable staticPublic staticExercised
    authority Hallowed.
  simpl in Hallowed.
  apply andb_true_iff in Hallowed as [Hreachable Hrest].
  apply andb_true_iff in Hrest as [HnotPublic HnotExercised].
  apply negb_true_iff in HnotPublic.
  apply negb_true_iff in HnotExercised.
  repeat split; assumption.
Qed.

Theorem opaque_foreign_authority_cannot_use_static_phil_confinement :
  forall interface boundary staticReachable staticPublic staticExercised authority,
    providerExtraDispositionAllowed
      (OpaqueForeignProviderAuthoritySubject interface boundary)
      staticReachable staticPublic staticExercised
      authority ExtraAuthorityStaticallyConfined = false.
Proof.
  reflexivity.
Qed.

Theorem abi_absence_is_never_confinement_evidence :
  forall subject staticReachable staticPublic staticExercised authority,
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority ExtraAuthorityAssertedAbsentFromAbi = false.
Proof.
  intros subject staticReachable staticPublic staticExercised authority.
  destruct subject; reflexivity.
Qed.

Theorem external_confinement_is_explicit_conditional_disposition :
  forall subject staticReachable staticPublic staticExercised authority,
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority ExtraAuthorityExternallyConfined = true.
Proof.
  intros subject staticReachable staticPublic staticExercised authority.
  destruct subject; reflexivity.
Qed.

Theorem assumption_dependent_authority_is_explicit_conditional_disposition :
  forall subject staticReachable staticPublic staticExercised authority,
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority ExtraAuthorityAssumptionDependent = true.
Proof.
  intros subject staticReachable staticPublic staticExercised authority.
  destruct subject; reflexivity.
Qed.

Theorem tcb_authority_boundary_is_explicit_conditional_disposition :
  forall subject staticReachable staticPublic staticExercised authority,
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority ExtraAuthorityTcbBoundary = true.
Proof.
  intros subject staticReachable staticPublic staticExercised authority.
  destruct subject; reflexivity.
Qed.