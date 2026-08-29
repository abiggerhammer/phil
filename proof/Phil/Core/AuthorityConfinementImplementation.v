From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import AuthorityConfinement.

(*
  PHIL-AUTH-CONFINE-IMPL-001 — representation-neutral executable decisions for
  Certified PHIL-AUTH-CONFINE-001.

  Concrete Set/Map/list/Text/evidence representations stay native. Production
  reflects their exact finite facts into Booleans and constructor kinds; the
  extracted kernel owns final semantic acceptance. Handwritten bridge and
  diagnostic code may reject on disagreement but may not turn kernel rejection
  into success.
*)

Definition decideClosureAuthorityConfinement
  (publicSubsetReachable exercisedSubsetReachable exercisedSubsetPublic : bool)
  : bool :=
  andb publicSubsetReachable
    (andb exercisedSubsetReachable exercisedSubsetPublic).

Theorem closure_authority_confinement_decision_accept_iff_certified :
  forall reachable public exercised
         publicSubsetReachable exercisedSubsetReachable exercisedSubsetPublic,
    (publicSubsetReachable = true <-> authoritySubset public reachable) ->
    (exercisedSubsetReachable = true <-> authoritySubset exercised reachable) ->
    (exercisedSubsetPublic = true <-> authoritySubset exercised public) ->
    decideClosureAuthorityConfinement
      publicSubsetReachable exercisedSubsetReachable exercisedSubsetPublic = true <->
    closureAuthorityConfinement reachable public exercised.
Proof.
  intros reachable public exercised
    publicSubsetReachable exercisedSubsetReachable exercisedSubsetPublic
    Hpublic Hreachable HpublicExercise.
  unfold decideClosureAuthorityConfinement, closureAuthorityConfinement.
  repeat rewrite andb_true_iff.
  rewrite Hpublic, Hreachable, HpublicExercise.
  reflexivity.
Qed.

Definition decideNegativeAuthorityClaim (authorityReachable : bool) : bool :=
  negb authorityReachable.

Theorem negative_authority_claim_decision_accept_iff_certified :
  forall reachable authority,
    decideNegativeAuthorityClaim (reachable authority) = true <->
    negativeAuthorityClaimAllowed reachable authority.
Proof.
  intros reachable authority.
  unfold decideNegativeAuthorityClaim, negativeAuthorityClaimAllowed.
  rewrite negb_true_iff.
  reflexivity.
Qed.

Inductive ProviderAuthoritySubjectKind : Type :=
| SemanticProviderAuthoritySubjectKind
| OpaqueForeignProviderAuthoritySubjectKind.

Definition providerAuthoritySubjectKind
  (subject : ProviderAuthoritySubject) : ProviderAuthoritySubjectKind :=
  match subject with
  | SemanticProviderAuthoritySubject _ _ => SemanticProviderAuthoritySubjectKind
  | OpaqueForeignProviderAuthoritySubject _ _ => OpaqueForeignProviderAuthoritySubjectKind
  end.

Definition decideProviderAuthoritySubject
  (kind : ProviderAuthoritySubjectKind)
  (interfaceMatches definitionMatches : bool) : bool :=
  match kind with
  | SemanticProviderAuthoritySubjectKind =>
      andb interfaceMatches definitionMatches
  | OpaqueForeignProviderAuthoritySubjectKind => true
  end.

Theorem semantic_provider_authority_subject_decision_accept_iff_certified :
  forall (interface definition checkedInterface checkedDefinition : nat)
         (interfaceMatches definitionMatches : bool),
    (interfaceMatches = true <-> interface = checkedInterface) ->
    (definitionMatches = true <-> definition = checkedDefinition) ->
    decideProviderAuthoritySubject
      SemanticProviderAuthoritySubjectKind interfaceMatches definitionMatches = true <->
    providerAuthoritySubjectAccepted
      (SemanticProviderAuthoritySubject interface definition)
      checkedInterface checkedDefinition.
Proof.
  intros interface definition checkedInterface checkedDefinition
    interfaceMatches definitionMatches Hinterface Hdefinition.
  unfold decideProviderAuthoritySubject, providerAuthoritySubjectAccepted.
  rewrite andb_true_iff, Hinterface, Hdefinition.
  reflexivity.
Qed.

Theorem opaque_provider_authority_subject_decision_accept_iff_certified :
  forall (interface boundary checkedInterface checkedDefinition : nat)
         (interfaceMatches definitionMatches : bool),
    decideProviderAuthoritySubject
      OpaqueForeignProviderAuthoritySubjectKind interfaceMatches definitionMatches = true <->
    providerAuthoritySubjectAccepted
      (OpaqueForeignProviderAuthoritySubject interface boundary)
      checkedInterface checkedDefinition.
Proof.
  intros interface boundary checkedInterface checkedDefinition
    interfaceMatches definitionMatches.
  unfold decideProviderAuthoritySubject, providerAuthoritySubjectAccepted.
  split; intro H.
  - exact I.
  - reflexivity.
Qed.

Inductive ProviderAuthorityInventoryBasisKind : Type :=
| CheckedPurePhilAuthorityInventoryKind
| ForeignAuthorityInventoryByEvidenceKind
| ForeignAuthorityInventoryAssumptionKind
| ForeignAuthorityInventoryTcbBoundaryKind
| ForeignAuthorityInventoryFromAbiShapeKind.

Definition providerAuthorityInventoryBasisKind
  (basis : ProviderAuthorityInventoryBasis) : ProviderAuthorityInventoryBasisKind :=
  match basis with
  | CheckedPurePhilAuthorityInventory => CheckedPurePhilAuthorityInventoryKind
  | ForeignAuthorityInventoryByEvidence => ForeignAuthorityInventoryByEvidenceKind
  | ForeignAuthorityInventoryAssumption => ForeignAuthorityInventoryAssumptionKind
  | ForeignAuthorityInventoryTcbBoundary => ForeignAuthorityInventoryTcbBoundaryKind
  | ForeignAuthorityInventoryFromAbiShape => ForeignAuthorityInventoryFromAbiShapeKind
  end.

Definition decideProviderAuthorityInventoryBasis
  (subjectKind : ProviderAuthoritySubjectKind)
  (basisKind : ProviderAuthorityInventoryBasisKind) : bool :=
  match subjectKind, basisKind with
  | SemanticProviderAuthoritySubjectKind, CheckedPurePhilAuthorityInventoryKind => true
  | OpaqueForeignProviderAuthoritySubjectKind, ForeignAuthorityInventoryByEvidenceKind => true
  | OpaqueForeignProviderAuthoritySubjectKind, ForeignAuthorityInventoryAssumptionKind => true
  | OpaqueForeignProviderAuthoritySubjectKind, ForeignAuthorityInventoryTcbBoundaryKind => true
  | _, _ => false
  end.

Theorem provider_authority_inventory_basis_decision_matches_certified :
  forall subject basis,
    decideProviderAuthorityInventoryBasis
      (providerAuthoritySubjectKind subject)
      (providerAuthorityInventoryBasisKind basis) =
    providerAuthorityInventoryBasisAllowed subject basis.
Proof.
  intros subject basis.
  destruct subject; destruct basis; reflexivity.
Qed.

Definition decideProviderExtraAuthority
  (internal clientVisible : bool) : bool :=
  andb internal (negb clientVisible).

Theorem provider_extra_authority_decision_matches_certified :
  forall internal clientVisible authority,
    decideProviderExtraAuthority
      (internal authority) (clientVisible authority) =
    providerExtraAuthority internal clientVisible authority.
Proof.
  intros.
  reflexivity.
Qed.

Definition decideProviderStaticSummaries
  (staticReachableSubsetInternal
   staticPublicSubsetClientVisible
   staticExercisedSubsetClientVisible : bool) : bool :=
  andb staticReachableSubsetInternal
    (andb staticPublicSubsetClientVisible staticExercisedSubsetClientVisible).

Theorem provider_static_summaries_decision_accept_iff_certified :
  forall internal clientVisible staticReachable staticPublic staticExercised
         staticReachableSubsetInternal
         staticPublicSubsetClientVisible
         staticExercisedSubsetClientVisible,
    (staticReachableSubsetInternal = true <->
      authoritySubset staticReachable internal) ->
    (staticPublicSubsetClientVisible = true <->
      authoritySubset staticPublic clientVisible) ->
    (staticExercisedSubsetClientVisible = true <->
      authoritySubset staticExercised clientVisible) ->
    decideProviderStaticSummaries
      staticReachableSubsetInternal
      staticPublicSubsetClientVisible
      staticExercisedSubsetClientVisible = true <->
    providerStaticSummariesAllowed
      internal clientVisible staticReachable staticPublic staticExercised.
Proof.
  intros internal clientVisible staticReachable staticPublic staticExercised
    staticReachableSubsetInternal staticPublicSubsetClientVisible
    staticExercisedSubsetClientVisible
    Hreachable Hpublic Hexercised.
  unfold decideProviderStaticSummaries, providerStaticSummariesAllowed.
  repeat rewrite andb_true_iff.
  rewrite Hreachable, Hpublic, Hexercised.
  reflexivity.
Qed.

Inductive ProviderExtraAuthorityDispositionKind : Type :=
| ExtraAuthorityStaticallyConfinedKind
| ExtraAuthorityExternallyConfinedKind
| ExtraAuthorityAssumptionDependentKind
| ExtraAuthorityTcbBoundaryKind
| ExtraAuthorityAssertedAbsentFromAbiKind.

Definition providerExtraAuthorityDispositionKind
  (disposition : ProviderExtraAuthorityDisposition)
  : ProviderExtraAuthorityDispositionKind :=
  match disposition with
  | ExtraAuthorityStaticallyConfined => ExtraAuthorityStaticallyConfinedKind
  | ExtraAuthorityExternallyConfined => ExtraAuthorityExternallyConfinedKind
  | ExtraAuthorityAssumptionDependent => ExtraAuthorityAssumptionDependentKind
  | ExtraAuthorityTcbBoundary => ExtraAuthorityTcbBoundaryKind
  | ExtraAuthorityAssertedAbsentFromAbi => ExtraAuthorityAssertedAbsentFromAbiKind
  end.

Definition decideProviderExtraDisposition
  (subjectKind : ProviderAuthoritySubjectKind)
  (dispositionKind : ProviderExtraAuthorityDispositionKind)
  (staticReachable staticPublic staticExercised : bool) : bool :=
  match dispositionKind with
  | ExtraAuthorityStaticallyConfinedKind =>
      match subjectKind with
      | SemanticProviderAuthoritySubjectKind =>
          andb staticReachable
            (andb (negb staticPublic) (negb staticExercised))
      | OpaqueForeignProviderAuthoritySubjectKind => false
      end
  | ExtraAuthorityExternallyConfinedKind => true
  | ExtraAuthorityAssumptionDependentKind => true
  | ExtraAuthorityTcbBoundaryKind => true
  | ExtraAuthorityAssertedAbsentFromAbiKind => false
  end.

Theorem provider_extra_disposition_decision_matches_certified :
  forall subject staticReachable staticPublic staticExercised authority disposition,
    decideProviderExtraDisposition
      (providerAuthoritySubjectKind subject)
      (providerExtraAuthorityDispositionKind disposition)
      (staticReachable authority)
      (staticPublic authority)
      (staticExercised authority) =
    providerExtraDispositionAllowed
      subject staticReachable staticPublic staticExercised
      authority disposition.
Proof.
  intros subject staticReachable staticPublic staticExercised authority disposition.
  destruct subject; destruct disposition; reflexivity.
Qed.

Definition decideProviderAuthorityQualificationFacts
  (subjectAccepted inventoryBasisAccepted staticSummariesAccepted
   dispositionDomainExactAccepted dispositionValuesAllowedAccepted : bool)
  : bool :=
  andb subjectAccepted
    (andb inventoryBasisAccepted
      (andb staticSummariesAccepted
        (andb dispositionDomainExactAccepted dispositionValuesAllowedAccepted))).

Theorem provider_authority_qualification_facts_accept_iff_certified :
  forall (subject : ProviderAuthoritySubject)
         (checkedInterface checkedDefinition : nat)
         (basis : ProviderAuthorityInventoryBasis)
         (clientVisible internal staticReachable staticPublic staticExercised : AuthoritySet)
         (dispositions : AuthorityUse -> option ProviderExtraAuthorityDisposition)
         (subjectAccepted inventoryBasisAccepted staticSummariesAccepted
          dispositionDomainExactAccepted dispositionValuesAllowedAccepted : bool),
    (subjectAccepted = true <->
      providerAuthoritySubjectAccepted subject checkedInterface checkedDefinition) ->
    inventoryBasisAccepted = providerAuthorityInventoryBasisAllowed subject basis ->
    (staticSummariesAccepted = true <->
      providerStaticSummariesAllowed
        internal clientVisible staticReachable staticPublic staticExercised) ->
    (dispositionDomainExactAccepted = true <->
      providerDispositionDomainExact internal clientVisible dispositions) ->
    (dispositionValuesAllowedAccepted = true <->
      forall authority disposition,
        dispositions authority = Some disposition ->
        providerExtraDispositionAllowed
          subject staticReachable staticPublic staticExercised
          authority disposition = true) ->
    decideProviderAuthorityQualificationFacts
      subjectAccepted inventoryBasisAccepted staticSummariesAccepted
      dispositionDomainExactAccepted dispositionValuesAllowedAccepted = true <->
    providerAuthorityQualificationAllowed
      subject checkedInterface checkedDefinition basis
      clientVisible internal staticReachable staticPublic staticExercised
      dispositions.
Proof.
  intros subject checkedInterface checkedDefinition basis
    clientVisible internal staticReachable staticPublic staticExercised
    dispositions subjectAccepted inventoryBasisAccepted staticSummariesAccepted
    dispositionDomainExactAccepted dispositionValuesAllowedAccepted
    Hsubject Hinventory Hstatic Hdomain Hvalues.
  unfold decideProviderAuthorityQualificationFacts,
    providerAuthorityQualificationAllowed, providerDispositionsAllowed.
  repeat rewrite andb_true_iff.
  rewrite Hsubject, Hinventory, Hstatic, Hdomain, Hvalues.
  reflexivity.
Qed.
