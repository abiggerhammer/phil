From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import CallableInvocation.

(*
  PHIL-CALL-INVOKE-001 / CALL-019 — finite executable correspondence.

  The production path has independent fail-closed gates.  This reflected layer
  records their conjunction without replacing concrete Text/Map/Set/list
  normalization, Surface evaluation, authority-state lookup, or diagnostic
  reconstruction.
*)

Inductive CallableInvocationDecision : Type :=
| CallableInvocationAccepted
| CallableInvocationRejected.

Definition callableInvocationFactsb
  (surfaceAccepted semanticContractPresent exactDeclaration ordinaryNamespace
   authorityPossessed refinementValid effectBoundValid failureBoundValid
   outcomeDomainExact outcomeBranchesExact callerControlExact
   residualObligationsExact callerResourceResidueExact lifecycleExact : bool)
  : bool :=
  andb surfaceAccepted
    (andb semanticContractPresent
      (andb exactDeclaration
        (andb ordinaryNamespace
          (andb authorityPossessed
            (andb refinementValid
              (andb effectBoundValid
                (andb failureBoundValid
                  (andb outcomeDomainExact
                    (andb outcomeBranchesExact
                      (andb callerControlExact
                        (andb residualObligationsExact
                          (andb callerResourceResidueExact lifecycleExact))))))))))))).

Definition decideCallableInvocation
  (surfaceAccepted semanticContractPresent exactDeclaration ordinaryNamespace
   authorityPossessed refinementValid effectBoundValid failureBoundValid
   outcomeDomainExact outcomeBranchesExact callerControlExact
   residualObligationsExact callerResourceResidueExact lifecycleExact : bool)
  : CallableInvocationDecision :=
  if callableInvocationFactsb
      surfaceAccepted semanticContractPresent exactDeclaration ordinaryNamespace
      authorityPossessed refinementValid effectBoundValid failureBoundValid
      outcomeDomainExact outcomeBranchesExact callerControlExact
      residualObligationsExact callerResourceResidueExact lifecycleExact
  then CallableInvocationAccepted
  else CallableInvocationRejected.

Theorem callable_invocation_facts_true_iff_all_gates :
  forall surfaceAccepted semanticContractPresent exactDeclaration ordinaryNamespace
         authorityPossessed refinementValid effectBoundValid failureBoundValid
         outcomeDomainExact outcomeBranchesExact callerControlExact
         residualObligationsExact callerResourceResidueExact lifecycleExact,
    callableInvocationFactsb
      surfaceAccepted semanticContractPresent exactDeclaration ordinaryNamespace
      authorityPossessed refinementValid effectBoundValid failureBoundValid
      outcomeDomainExact outcomeBranchesExact callerControlExact
      residualObligationsExact callerResourceResidueExact lifecycleExact = true <->
    surfaceAccepted = true /\
    semanticContractPresent = true /\
    exactDeclaration = true /\
    ordinaryNamespace = true /\
    authorityPossessed = true /\
    refinementValid = true /\
    effectBoundValid = true /\
    failureBoundValid = true /\
    outcomeDomainExact = true /\
    outcomeBranchesExact = true /\
    callerControlExact = true /\
    residualObligationsExact = true /\
    callerResourceResidueExact = true /\
    lifecycleExact = true.
Proof.
  intros.
  unfold callableInvocationFactsb.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem exact_callable_invocation_accepts :
  decideCallableInvocation
    true true true true true true true true true true true true true true =
    CallableInvocationAccepted.
Proof.
  reflexivity.
Qed.

Theorem missing_semantic_contract_rejects :
  decideCallableInvocation
    true false true true true true true true true true true true true true =
    CallableInvocationRejected.
Proof.
  reflexivity.
Qed.

Theorem wrong_declaration_identity_rejects :
  decideCallableInvocation
    true true false true true true true true true true true true true true =
    CallableInvocationRejected.
Proof.
  reflexivity.
Qed.

Theorem provider_or_primitive_namespace_substitution_rejects :
  decideCallableInvocation
    true true true false true true true true true true true true true true =
    CallableInvocationRejected.
Proof.
  reflexivity.
Qed.

Theorem missing_possessed_authority_rejects :
  decideCallableInvocation
    true true true true false true true true true true true true true true =
    CallableInvocationRejected.
Proof.
  reflexivity.
Qed.

Theorem effect_or_failure_widening_rejects :
  decideCallableInvocation
    true true true true true true false true true true true true true true =
      CallableInvocationRejected /\
  decideCallableInvocation
    true true true true true true true false true true true true true true =
      CallableInvocationRejected.
Proof.
  split; reflexivity.
Qed.

Theorem incomplete_or_substituted_outcome_domain_rejects :
  decideCallableInvocation
    true true true true true true true true false true true true true true =
      CallableInvocationRejected /\
  decideCallableInvocation
    true true true true true true true true true false true true true true =
      CallableInvocationRejected.
Proof.
  split; reflexivity.
Qed.

Theorem caller_control_substitution_rejects :
  decideCallableInvocation
    true true true true true true true true true true false true true true =
    CallableInvocationRejected.
Proof.
  reflexivity.
Qed.

Theorem residual_or_resource_substitution_rejects :
  decideCallableInvocation
    true true true true true true true true true true true false true true =
      CallableInvocationRejected /\
  decideCallableInvocation
    true true true true true true true true true true true true false true =
      CallableInvocationRejected.
Proof.
  split; reflexivity.
Qed.

Theorem missing_lifecycle_evidence_rejects :
  decideCallableInvocation
    true true true true true true true true true true true true true false =
    CallableInvocationRejected.
Proof.
  reflexivity.
Qed.
