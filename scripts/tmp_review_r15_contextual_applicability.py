from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    if old not in text:
        raise SystemExit(f"R15 anchor not found in {path}: {old[:160]!r}")
    p.write_text(text.replace(old, new, 1))


# Retain the admission coordinates already committed into the admission revision.
replace_once(
    "src/Phil/Core/ProviderQualificationIdentity.hs",
    """data CheckedProviderQualificationAdmissionIdentity = CheckedProviderQualificationAdmissionIdentity\n  { checkedQualificationAdmissionClaimRevision :: QualificationClaimRevision\n  , checkedQualificationAdmissionEvidenceRevision :: QualificationEvidenceRevision\n  , checkedQualificationAdmissionRevision :: QualificationAdmissionRevision\n  , checkedQualificationAdmissionDecision :: ProviderQualificationAdmissionDecision\n  }\n""",
    """data CheckedProviderQualificationAdmissionIdentity = CheckedProviderQualificationAdmissionIdentity\n  { checkedQualificationAdmissionClaimRevision :: QualificationClaimRevision\n  , checkedQualificationAdmissionEvidenceRevision :: QualificationEvidenceRevision\n  , checkedQualificationAdmissionRevision :: QualificationAdmissionRevision\n  , checkedQualificationAdmissionProviderOccurrence :: Text\n  , checkedQualificationAdmissionRealizationContextRevision :: Text\n  , checkedQualificationAdmissionDecision :: ProviderQualificationAdmissionDecision\n  }\n""",
)
replace_once(
    "src/Phil/Core/ProviderQualificationIdentity.hs",
    """        { checkedQualificationAdmissionClaimRevision = expectedClaim\n        , checkedQualificationAdmissionEvidenceRevision = expectedEvidence\n        , checkedQualificationAdmissionRevision = deriveQualificationAdmissionRevision admission\n        , checkedQualificationAdmissionDecision = qualificationAdmissionDecision admission\n        }\n""",
    """        { checkedQualificationAdmissionClaimRevision = expectedClaim\n        , checkedQualificationAdmissionEvidenceRevision = expectedEvidence\n        , checkedQualificationAdmissionRevision = deriveQualificationAdmissionRevision admission\n        , checkedQualificationAdmissionProviderOccurrence =\n            qualificationAdmissionProviderOccurrence admission\n        , checkedQualificationAdmissionRealizationContextRevision =\n            qualificationAdmissionRealizationContextRevision admission\n        , checkedQualificationAdmissionDecision = qualificationAdmissionDecision admission\n        }\n""",
)

# Bind the relative PROV-014 applicability coordinates back to the checked
# contextual admission before accepting the existing certified relative relation.
replace_once(
    "src/Phil/Core/ProviderQualificationApplicability.hs",
    """import ProviderQualificationLineageTargetKernel\n  ( AdmissionApplicabilityDecision (..)\n  , decideAdmissionApplicabilityByFacts\n  )\n""",
    """import ProviderQualificationLineageTargetKernel\n  ( AdmissionApplicabilityDecision (..)\n  , AdmissionContextDecision (..)\n  , decideAdmissionApplicabilityByFacts\n  , decideAdmissionContextByFacts\n  )\n""",
)
replace_once(
    "src/Phil/Core/ProviderQualificationApplicability.hs",
    """  | ProviderApplicabilityRealizationRevisionMismatch RealizationRevision RealizationRevision\n  | ProviderApplicabilitySelectionAdmissionMismatch\n""",
    """  | ProviderApplicabilityRealizationRevisionMismatch RealizationRevision RealizationRevision\n  | ProviderApplicabilityAdmissionOccurrenceMismatch Text Text\n  | ProviderApplicabilityAdmissionRealizationContextMismatch Text Text\n  | ProviderApplicabilitySelectionAdmissionMismatch\n""",
)
replace_once(
    "src/Phil/Core/ProviderQualificationApplicability.hs",
    """    AdmissionApplicabilityAcceptedDecision ->\n      Right CheckedProviderAdmissionApplicability\n        { checkedProviderApplicabilityAdmissionRevision = expectedAdmission\n        , checkedProviderApplicabilityClaimRevision = expectedClaim\n        , checkedProviderApplicabilityTargetEvidenceRevision = expectedTargetEvidence\n        , checkedProviderApplicabilityRequirementOccurrence =\n            providerApplicabilityRequirementOccurrence applicability\n        , checkedProviderApplicabilityInstanceRevision =\n            providerApplicabilityInstanceRevision applicability\n        , checkedProviderApplicabilityRealizationRevision =\n            providerApplicabilityRealizationRevision applicability\n        }\n""",
    """    AdmissionApplicabilityAcceptedDecision ->\n      case contextDecision of\n        AdmissionContextAcceptedDecision ->\n          Right CheckedProviderAdmissionApplicability\n            { checkedProviderApplicabilityAdmissionRevision = expectedAdmission\n            , checkedProviderApplicabilityClaimRevision = expectedClaim\n            , checkedProviderApplicabilityTargetEvidenceRevision = expectedTargetEvidence\n            , checkedProviderApplicabilityRequirementOccurrence =\n                providerApplicabilityRequirementOccurrence applicability\n            , checkedProviderApplicabilityInstanceRevision =\n                providerApplicabilityInstanceRevision applicability\n            , checkedProviderApplicabilityRealizationRevision =\n                providerApplicabilityRealizationRevision applicability\n            }\n        AdmissionContextOccurrenceDecision ->\n          Left (ProviderApplicabilityAdmissionOccurrenceMismatch\n            expectedAdmissionOccurrence actualApplicabilityOccurrence)\n        AdmissionContextRealizationDecision ->\n          Left (ProviderApplicabilityAdmissionRealizationContextMismatch\n            expectedAdmissionRealization actualApplicabilityRealization)\n""",
)
replace_once(
    "src/Phil/Core/ProviderQualificationApplicability.hs",
    """    expectedTargetEvidence = deriveTargetRealizationEvidenceRevision targetEvidence\n    admitted = case checkedQualificationAdmissionDecision admission of\n""",
    """    expectedTargetEvidence = deriveTargetRealizationEvidenceRevision targetEvidence\n    expectedAdmissionOccurrence = checkedQualificationAdmissionProviderOccurrence admission\n    expectedAdmissionRealization =\n      checkedQualificationAdmissionRealizationContextRevision admission\n    actualApplicabilityOccurrence = unProviderRequirementOccurrenceKey\n      (providerApplicabilityRequirementOccurrence applicability)\n    actualApplicabilityRealization = case providerApplicabilityRealizationRevision applicability of\n      RealizationRevision value -> value\n    contextDecision = decideAdmissionContextByFacts\n      (actualApplicabilityOccurrence == expectedAdmissionOccurrence)\n      (actualApplicabilityRealization == expectedAdmissionRealization)\n    admitted = case checkedQualificationAdmissionDecision admission of\n""",
)

# Update the pre-existing direct PROV-014 fixture to carry an internally coherent
# checked contextual admission rather than a context-free hand-built record.
replace_once(
    "test/Phase1ProviderQualificationApplicabilityMain.hs",
    """  , checkedQualificationAdmissionRevision = admissionRevision\n  , checkedQualificationAdmissionDecision = QualificationAdmitted\n""",
    """  , checkedQualificationAdmissionRevision = admissionRevision\n  , checkedQualificationAdmissionProviderOccurrence = "provider.requirement.blob"\n  , checkedQualificationAdmissionRealizationContextRevision = "architecture.realization:v1"\n  , checkedQualificationAdmissionDecision = QualificationAdmitted\n""",
)

# Strengthen the Certified model with the two missing context-binding facts while
# preserving the original 20-fact relative AdmissionApplicable theorem family.
replace_once(
    "proof/Phil/Core/ProviderQualificationLineageTarget.v",
    """Record CheckedProviderQualificationAdmission : Type :=\n  mkCheckedProviderQualificationAdmission {\n    checkedAdmissionClaimRevision : QualificationClaimRevision;\n    checkedAdmissionRevision : QualificationAdmissionRevision;\n    checkedAdmissionDecision : ProviderQualificationAdmissionDecision\n  }.\n""",
    """Record CheckedProviderQualificationAdmission : Type :=\n  mkCheckedProviderQualificationAdmission {\n    checkedAdmissionClaimRevision : QualificationClaimRevision;\n    checkedAdmissionRevision : QualificationAdmissionRevision;\n    checkedAdmissionProviderOccurrence : ProviderRequirementOccurrenceKey;\n    checkedAdmissionRealizationContext : RealizationRevision;\n    checkedAdmissionDecision : ProviderQualificationAdmissionDecision\n  }.\n""",
)
replace_once(
    "proof/Phil/Core/ProviderQualificationLineageTarget.v",
    """Theorem applicability_requires_admitted_qualification :\n""",
    """(* REVIEW-R15 closes the context edge deliberately left implicit by the\n   relative PROV-014 relation.  The normalized proof model projects the provider\n   occurrence and realization-context coordinates carried by the checked\n   admission into the exact requirement-occurrence/realization coordinates used\n   by applicability. *)\nRecord AdmissionContextBound\n  (admission : CheckedProviderQualificationAdmission)\n  (applicability : ProviderConcreteAdmissionApplicability) : Prop :=\n  mkAdmissionContextBound {\n    applicability_occurrence_bound_to_admission :\n      applicabilityRequirementOccurrence applicability =\n        checkedAdmissionProviderOccurrence admission;\n    applicability_realization_bound_to_admission :\n      applicabilityRealizationRevision applicability =\n        checkedAdmissionRealizationContext admission\n  }.\n\nTheorem stale_admission_occurrence_cannot_be_relocated :\n  forall admission applicability,\n    applicabilityRequirementOccurrence applicability <>\n      checkedAdmissionProviderOccurrence admission ->\n    ~ AdmissionContextBound admission applicability.\nProof.\n  intros admission applicability Hneq Hbound.\n  destruct Hbound as [Hoccurrence _].\n  apply Hneq. exact Hoccurrence.\nQed.\n\nTheorem stale_admission_realization_cannot_be_relocated :\n  forall admission applicability,\n    applicabilityRealizationRevision applicability <>\n      checkedAdmissionRealizationContext admission ->\n    ~ AdmissionContextBound admission applicability.\nProof.\n  intros admission applicability Hneq Hbound.\n  destruct Hbound as [_ Hrealization].\n  apply Hneq. exact Hrealization.\nQed.\n\nTheorem applicability_requires_admitted_qualification :\n""",
)

# Reflect the new Certified context relation into a separate tiny extracted
# decision so the established 20-fact PROV-014 kernel remains independently
# inspectable and its existing diagnostics/order do not move.
with Path("proof/Phil/Core/ProviderQualificationLineageTargetImplementation.v").open("a") as out:
    out.write(r'''\n\nInductive AdmissionContextDecision : Type :=\n| AdmissionContextAcceptedDecision\n| AdmissionContextOccurrenceDecision\n| AdmissionContextRealizationDecision.\n\nDefinition decideAdmissionContextByFacts\n  (occurrence realization : bool) : AdmissionContextDecision :=\n  if occurrence then\n    if realization\n    then AdmissionContextAcceptedDecision\n    else AdmissionContextRealizationDecision\n  else AdmissionContextOccurrenceDecision.\n\nDefinition AdmissionContextFactsSatisfied\n  (occurrence realization : bool) : Prop :=\n  occurrence = true /\\ realization = true.\n\nTheorem admission_context_decision_accepted_iff :\n  forall occurrence realization,\n    decideAdmissionContextByFacts occurrence realization =\n      AdmissionContextAcceptedDecision <->\n    AdmissionContextFactsSatisfied occurrence realization.\nProof.\n  intros occurrence realization.\n  unfold decideAdmissionContextByFacts, AdmissionContextFactsSatisfied.\n  destruct occurrence; simpl; [|intuition discriminate].\n  destruct realization; simpl; intuition discriminate.\nQed.\n\nDefinition reflectedAdmissionContextDecision\n  (admission : CheckedProviderQualificationAdmission)\n  (applicability : ProviderConcreteAdmissionApplicability) :\n  AdmissionContextDecision :=\n  decideAdmissionContextByFacts\n    (Nat.eqb\n      (applicabilityRequirementOccurrence applicability)\n      (checkedAdmissionProviderOccurrence admission))\n    (Nat.eqb\n      (applicabilityRealizationRevision applicability)\n      (checkedAdmissionRealizationContext admission)).\n\nTheorem reflected_admission_context_decision_exact :\n  forall admission applicability,\n    reflectedAdmissionContextDecision admission applicability =\n      AdmissionContextAcceptedDecision <->\n    AdmissionContextBound admission applicability.\nProof.\n  intros admission applicability.\n  unfold reflectedAdmissionContextDecision.\n  rewrite admission_context_decision_accepted_iff.\n  split.\n  - intros [Hoccurrence Hrealization].\n    apply Nat.eqb_eq in Hoccurrence.\n    apply Nat.eqb_eq in Hrealization.\n    constructor; assumption.\n  - intros Hbound.\n    destruct Hbound as [Hoccurrence Hrealization].\n    split.\n    + apply Nat.eqb_eq. exact Hoccurrence.\n    + apply Nat.eqb_eq. exact Hrealization.\nQed.\n''')

replace_once(
    "proof/Phil/Core/ProviderQualificationLineageTargetImplementationExtraction.v",
    """  decideTargetReuseByFacts\n  decideAdmissionApplicabilityByFacts.\n""",
    """  decideTargetReuseByFacts\n  decideAdmissionApplicabilityByFacts\n  decideAdmissionContextByFacts.\n""",
)

# Extend extracted-kernel direct controls without perturbing the original 20
# PROV-014 positions.
replace_once(
    "app/ProviderLineageTargetDecisionCorrespondenceMain.hs",
    """  _ -> False\n\nreuse :: Bool""",
    """  _ -> False\n\nisContext :: AdmissionContextDecision -> AdmissionContextDecision -> Bool\nisContext expected actual = case (expected, actual) of\n  (AdmissionContextAcceptedDecision, AdmissionContextAcceptedDecision) -> True\n  (AdmissionContextOccurrenceDecision, AdmissionContextOccurrenceDecision) -> True\n  (AdmissionContextRealizationDecision, AdmissionContextRealizationDecision) -> True\n  _ -> False\n\nreuse :: Bool""",
)
replace_once(
    "app/ProviderLineageTargetDecisionCorrespondenceMain.hs",
    """app = decideAdmissionApplicabilityByFacts\n\nmain :: IO ()\n""",
    """app = decideAdmissionApplicabilityByFacts\n\ncontext :: Bool -> Bool -> AdmissionContextDecision\ncontext = decideAdmissionContextByFacts\n\nmain :: IO ()\n""",
)
with Path("app/ProviderLineageTargetDecisionCorrespondenceMain.hs").open("a") as out:
    out.write(r'''\n  assert "REVIEW-R15 exact contextual admission binding accepts" $\n    isContext AdmissionContextAcceptedDecision (context True True)\n  assert "REVIEW-R15 stale provider occurrence rejects" $\n    isContext AdmissionContextOccurrenceDecision (context False True)\n  assert "REVIEW-R15 stale realization context rejects" $\n    isContext AdmissionContextRealizationDecision (context True False)\n''')

# Document the strengthened competence edge without rewriting historical slice
# descriptions as if the omission had never existed.
replace_once(
    "docs/phase-1/provider-admission-applicability-v1.md",
    """## Symbols are not applicability\n""",
    """## Contextual admission binding (REVIEW-R15 reconciliation)\n\nThe accepted admission identity is content-bound to the provider occurrence and realization-context revision for which policy admitted it. The checked admission therefore retains those two coordinates. Before the existing relative PROV-014 applicability relation can accept, the checker projects them into the normalized provider-requirement occurrence and `RealizationRevision` coordinates used by the applicability binding and requires exact equality.\n\nChanging the applicability occurrence or realization together with the selected description no longer makes a stale admission applicable. A genuine relocation must produce a fresh contextual admission (and therefore a fresh `QualificationAdmissionRevision`) or use a separately specified checked reuse relation.\n\nThis contextual edge is Certified separately as `AdmissionContextBound`; the original `AdmissionApplicable` relation remains the relative target/selection relation. Production acceptance requires both.\n\n## Symbols are not applicability\n""",
)
replace_once(
    "docs/phase-1/provider-lineage-target-implementation-refinement-v1.md",
    """`reflected_admission_applicability_decision_exact` proves acceptance exactly equivalent to Certified `AdmissionApplicable`.\n\nExported symbol metadata""",
    """`reflected_admission_applicability_decision_exact` proves acceptance exactly equivalent to Certified `AdmissionApplicable`.\n\nREVIEW-R15 adds a second extracted decision, `decideAdmissionContextByFacts`, for the two independent contextual coordinates retained from the original checked admission: provider occurrence and realization context. `reflected_admission_context_decision_exact` proves exact equivalence to Certified `AdmissionContextBound`. Production PROV-014 acceptance now requires both the established relative applicability decision and this contextual binding decision.\n\nExported symbol metadata""",
)
replace_once(
    "docs/phase-1/provider-lineage-target-production-binding-v1.md",
    """Exported symbols remain deliberately absent from the semantic decision, matching the Certified theorem: symbol rename alone is nonsemantic.\n""",
    """Exported symbols remain deliberately absent from the semantic decision, matching the Certified theorem: symbol rename alone is nonsemantic.\n\nREVIEW-R15 strengthens the production boundary with the separately Certified `AdmissionContextBound` relation. The checked admission retains the provider occurrence and realization-context revision already included in its content-addressed admission identity; `decideAdmissionContextByFacts` requires the applicability requirement occurrence and realization revision to be the exact normalized projections of those coordinates. The existing 20-fact relative PROV-014 decision remains unchanged and is composed with this new context decision.\n""",
)

# Extend both long-lived proof/binding workflows so this new correspondence stays
# in the existing Certified/Implementation-Refined gate, in addition to the
# dedicated REVIEW-R15 regression workflow that will be installed after staging.
for workflow in [
    ".github/workflows/phase1-provider-lineage-target-proofs.yml",
    ".github/workflows/phase1-provider-lineage-target-production-binding.yml",
]:
    replace_once(
        workflow,
        """      - 'src/Phil/Core/ProviderQualificationApplicability.hs'\n""",
        """      - 'src/Phil/Core/ProviderQualificationApplicability.hs'\n      - 'src/Phil/Core/ProviderQualificationIdentity.hs'\n      - 'test/Phase1ReviewR15ContextualApplicabilityMain.hs'\n""",
    )
    # same path block appears for push; update it separately
    replace_once(
        workflow,
        """      - 'src/Phil/Core/ProviderQualificationApplicability.hs'\n""",
        """      - 'src/Phil/Core/ProviderQualificationApplicability.hs'\n      - 'src/Phil/Core/ProviderQualificationIdentity.hs'\n      - 'test/Phase1ReviewR15ContextualApplicabilityMain.hs'\n""",
    )

replace_once(
    ".github/workflows/phase1-provider-lineage-target-proofs.yml",
    """          grep -q 'decideAdmissionApplicabilityByFacts' ProviderQualificationLineageTargetKernel.hs\n""",
    """          grep -q 'decideAdmissionApplicabilityByFacts' ProviderQualificationLineageTargetKernel.hs\n          grep -q 'decideAdmissionContextByFacts' ProviderQualificationLineageTargetKernel.hs\n""",
)
replace_once(
    ".github/workflows/phase1-provider-lineage-target-proofs.yml",
    """          cabal exec -- runghc -Wall -Werror -isrc test/Phase1ProviderQualificationApplicabilityMain.hs\n""",
    """          cabal exec -- runghc -Wall -Werror -isrc test/Phase1ProviderQualificationApplicabilityMain.hs\n          cabal exec -- runghc -Wall -Werror -isrc test/Phase1ReviewR15ContextualApplicabilityMain.hs\n""",
)
replace_once(
    ".github/workflows/phase1-provider-lineage-target-production-binding.yml",
    """          cabal exec -- runghc -Wall -Werror -isrc \\\n            test/Phase1ProviderQualificationApplicabilityMain.hs\n""",
    """          cabal exec -- runghc -Wall -Werror -isrc \\\n            test/Phase1ProviderQualificationApplicabilityMain.hs\n          cabal exec -- runghc -Wall -Werror -isrc \\\n            test/Phase1ReviewR15ContextualApplicabilityMain.hs\n""",
)

print("R15 contextual applicability patch applied")
