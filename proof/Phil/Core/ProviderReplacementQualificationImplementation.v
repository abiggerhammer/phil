From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProviderReplacementQualification.

(*
  PHIL-PROV-REPLACE-001 — representation-neutral replacement decision surface.

  Production already validates each side independently, then reflects concrete
  identity equality/difference and finite Set/Map coverage into Boolean facts.
  This layer owns the ordered semantic decision over those facts. It deliberately
  does not reimplement Text, Map, Set, revision construction, or admission
  checking; truth of the reflected facts remains the native bridge boundary.
*)

Inductive ProviderReplacementDecision : Type :=
| ProviderReplacementAccepted
| ProviderReplacementAdmissionRequired
| ProviderReplacementInterfaceMismatch
| ProviderReplacementOccurrenceMismatch
| ProviderReplacementInstanceMismatch
| ProviderReplacementSameSemanticSubject
| ProviderReplacementRealizationUnchanged
| ProviderReplacementClaimLineageInherited
| ProviderReplacementEvidenceLineageInherited
| ProviderReplacementAdmissionLineageInherited
| ProviderReplacementSharedEvidenceWithoutScope
| ProviderReplacementUnexpectedEvidenceReuse.

Definition decideProviderReplacementByFacts
  (priorAdmitted replacementAdmitted
   interfaceMatches occurrenceMatches instanceMatches
   subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
   allSharedEvidenceScoped noUnexpectedReuse : bool)
  : ProviderReplacementDecision :=
  if priorAdmitted then
    if replacementAdmitted then
      if interfaceMatches then
        if occurrenceMatches then
          if instanceMatches then
            if subjectDiffers then
              if realizationDiffers then
                if claimDiffers then
                  if evidenceDiffers then
                    if admissionDiffers then
                      if allSharedEvidenceScoped then
                        if noUnexpectedReuse then
                          ProviderReplacementAccepted
                        else ProviderReplacementUnexpectedEvidenceReuse
                      else ProviderReplacementSharedEvidenceWithoutScope
                    else ProviderReplacementAdmissionLineageInherited
                  else ProviderReplacementEvidenceLineageInherited
                else ProviderReplacementClaimLineageInherited
              else ProviderReplacementRealizationUnchanged
            else ProviderReplacementSameSemanticSubject
          else ProviderReplacementInstanceMismatch
        else ProviderReplacementOccurrenceMismatch
      else ProviderReplacementInterfaceMismatch
    else ProviderReplacementAdmissionRequired
  else ProviderReplacementAdmissionRequired.

Inductive ProviderReplacementReuseDecision : Type :=
| ProviderReplacementReuseAccepted
| ProviderReplacementReuseReferenceMismatch
| ProviderReplacementReusePriorClaimMismatch
| ProviderReplacementReuseNewClaimMismatch
| ProviderReplacementReuseScopeMissing.

Definition decideProviderReplacementReuseByFacts
  (referenceMatches priorClaimMatches newClaimMatches hasValidityScope : bool)
  : ProviderReplacementReuseDecision :=
  if referenceMatches then
    if priorClaimMatches then
      if newClaimMatches then
        if hasValidityScope then
          ProviderReplacementReuseAccepted
        else ProviderReplacementReuseScopeMissing
      else ProviderReplacementReuseNewClaimMismatch
    else ProviderReplacementReusePriorClaimMismatch
  else ProviderReplacementReuseReferenceMismatch.

Theorem provider_replacement_all_reflected_facts_accept :
  decideProviderReplacementByFacts
    true true true true true true true true true true true true =
    ProviderReplacementAccepted.
Proof. reflexivity. Qed.

Theorem provider_replacement_acceptance_requires_all_reflected_facts :
  forall priorAdmitted replacementAdmitted
         interfaceMatches occurrenceMatches instanceMatches
         subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
         allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      priorAdmitted replacementAdmitted
      interfaceMatches occurrenceMatches instanceMatches
      subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementAccepted ->
    priorAdmitted = true /\
    replacementAdmitted = true /\
    interfaceMatches = true /\
    occurrenceMatches = true /\
    instanceMatches = true /\
    subjectDiffers = true /\
    realizationDiffers = true /\
    claimDiffers = true /\
    evidenceDiffers = true /\
    admissionDiffers = true /\
    allSharedEvidenceScoped = true /\
    noUnexpectedReuse = true.
Proof.
  intros priorAdmitted replacementAdmitted
    interfaceMatches occurrenceMatches instanceMatches
    subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
    allSharedEvidenceScoped noUnexpectedReuse Haccepted.
  destruct priorAdmitted; simpl in Haccepted; try discriminate.
  destruct replacementAdmitted; simpl in Haccepted; try discriminate.
  destruct interfaceMatches; simpl in Haccepted; try discriminate.
  destruct occurrenceMatches; simpl in Haccepted; try discriminate.
  destruct instanceMatches; simpl in Haccepted; try discriminate.
  destruct subjectDiffers; simpl in Haccepted; try discriminate.
  destruct realizationDiffers; simpl in Haccepted; try discriminate.
  destruct claimDiffers; simpl in Haccepted; try discriminate.
  destruct evidenceDiffers; simpl in Haccepted; try discriminate.
  destruct admissionDiffers; simpl in Haccepted; try discriminate.
  destruct allSharedEvidenceScoped; simpl in Haccepted; try discriminate.
  destruct noUnexpectedReuse; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem provider_replacement_prior_admission_failure_has_precedence :
  forall replacementAdmitted interfaceMatches occurrenceMatches instanceMatches
         subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
         allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      false replacementAdmitted interfaceMatches occurrenceMatches instanceMatches
      subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementAdmissionRequired.
Proof. reflexivity. Qed.

Theorem provider_replacement_new_admission_failure_has_precedence :
  forall interfaceMatches occurrenceMatches instanceMatches
         subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
         allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true false interfaceMatches occurrenceMatches instanceMatches
      subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementAdmissionRequired.
Proof. reflexivity. Qed.

Theorem provider_replacement_interface_failure_has_precedence :
  forall occurrenceMatches instanceMatches subjectDiffers realizationDiffers
         claimDiffers evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true false occurrenceMatches instanceMatches subjectDiffers realizationDiffers
      claimDiffers evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse =
      ProviderReplacementInterfaceMismatch.
Proof. reflexivity. Qed.

Theorem provider_replacement_occurrence_failure_has_precedence :
  forall instanceMatches subjectDiffers realizationDiffers claimDiffers
         evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true false instanceMatches subjectDiffers realizationDiffers claimDiffers
      evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse =
      ProviderReplacementOccurrenceMismatch.
Proof. reflexivity. Qed.

Theorem provider_replacement_instance_failure_has_precedence :
  forall subjectDiffers realizationDiffers claimDiffers evidenceDiffers
         admissionDiffers allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true false subjectDiffers realizationDiffers claimDiffers
      evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse =
      ProviderReplacementInstanceMismatch.
Proof. reflexivity. Qed.

Theorem provider_replacement_same_subject_has_precedence :
  forall realizationDiffers claimDiffers evidenceDiffers admissionDiffers
         allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true true false realizationDiffers claimDiffers evidenceDiffers
      admissionDiffers allSharedEvidenceScoped noUnexpectedReuse =
      ProviderReplacementSameSemanticSubject.
Proof. reflexivity. Qed.

Theorem provider_replacement_unchanged_realization_has_precedence :
  forall claimDiffers evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true true true false claimDiffers evidenceDiffers admissionDiffers
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementRealizationUnchanged.
Proof. reflexivity. Qed.

Theorem provider_replacement_inherited_claim_has_precedence :
  forall evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true true true true false evidenceDiffers admissionDiffers
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementClaimLineageInherited.
Proof. reflexivity. Qed.

Theorem provider_replacement_inherited_evidence_has_precedence :
  forall admissionDiffers allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true true true true true false admissionDiffers
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementEvidenceLineageInherited.
Proof. reflexivity. Qed.

Theorem provider_replacement_inherited_admission_has_precedence :
  forall allSharedEvidenceScoped noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true true true true true true false
      allSharedEvidenceScoped noUnexpectedReuse = ProviderReplacementAdmissionLineageInherited.
Proof. reflexivity. Qed.

Theorem provider_replacement_unscoped_shared_evidence_has_precedence :
  forall noUnexpectedReuse,
    decideProviderReplacementByFacts
      true true true true true true true true true true false noUnexpectedReuse =
      ProviderReplacementSharedEvidenceWithoutScope.
Proof. reflexivity. Qed.

Theorem provider_replacement_spurious_reuse_has_precedence :
  decideProviderReplacementByFacts
    true true true true true true true true true true true false =
    ProviderReplacementUnexpectedEvidenceReuse.
Proof. reflexivity. Qed.

Theorem provider_replacement_reuse_all_reflected_facts_accept :
  decideProviderReplacementReuseByFacts true true true true =
    ProviderReplacementReuseAccepted.
Proof. reflexivity. Qed.

Theorem provider_replacement_reuse_acceptance_requires_all_reflected_facts :
  forall referenceMatches priorClaimMatches newClaimMatches hasValidityScope,
    decideProviderReplacementReuseByFacts
      referenceMatches priorClaimMatches newClaimMatches hasValidityScope =
      ProviderReplacementReuseAccepted ->
    referenceMatches = true /\
    priorClaimMatches = true /\
    newClaimMatches = true /\
    hasValidityScope = true.
Proof.
  intros referenceMatches priorClaimMatches newClaimMatches hasValidityScope Haccepted.
  destruct referenceMatches; simpl in Haccepted; try discriminate.
  destruct priorClaimMatches; simpl in Haccepted; try discriminate.
  destruct newClaimMatches; simpl in Haccepted; try discriminate.
  destruct hasValidityScope; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem provider_replacement_reuse_reference_failure_has_precedence :
  forall priorClaimMatches newClaimMatches hasValidityScope,
    decideProviderReplacementReuseByFacts
      false priorClaimMatches newClaimMatches hasValidityScope =
      ProviderReplacementReuseReferenceMismatch.
Proof. reflexivity. Qed.

Theorem provider_replacement_reuse_prior_claim_failure_has_precedence :
  forall newClaimMatches hasValidityScope,
    decideProviderReplacementReuseByFacts true false newClaimMatches hasValidityScope =
      ProviderReplacementReusePriorClaimMismatch.
Proof. reflexivity. Qed.

Theorem provider_replacement_reuse_new_claim_failure_has_precedence :
  forall hasValidityScope,
    decideProviderReplacementReuseByFacts true true false hasValidityScope =
      ProviderReplacementReuseNewClaimMismatch.
Proof. reflexivity. Qed.

Theorem provider_replacement_reuse_scope_failure_has_precedence :
  decideProviderReplacementReuseByFacts true true true false =
    ProviderReplacementReuseScopeMissing.
Proof. reflexivity. Qed.
