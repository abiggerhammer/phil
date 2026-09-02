From Phil.Core Require RuntimePrimitiveIdentity.
From Phil.LLVM Require RuntimeSymbolIdentity.

(*
  LLVM target refinement for PHIL-TARGET-RUNTIME-PRIM-001.

  The historical PHIL-LLVM-RUNTIME-SYM-001 theorem remains unchanged.  This
  bridge proves that its physical primitive/signature naming rule is one exact
  instantiation of the target-neutral runtime primitive identity relation.
*)

Definition llvmRuntimeSymbolAsTargetPrimitive
  (model : RuntimeSymbolIdentity.RuntimeSymbolModel)
  : RuntimePrimitiveIdentity.RuntimePrimitiveIdentityModel :=
  RuntimePrimitiveIdentity.mkRuntimePrimitiveIdentityModel
    (RuntimeSymbolIdentity.runtimeSymbolPrimitive model)
    (RuntimeSymbolIdentity.runtimeSymbolSignature model)
    (RuntimeSymbolIdentity.runtimeSymbolBuilder model)
    (RuntimeSymbolIdentity.runtimeSymbolActual model)
    (RuntimeSymbolIdentity.runtimeSymbolRevision model)
    (RuntimeSymbolIdentity.runtimeSymbolEvidence model)
    (RuntimeSymbolIdentity.runtimeSymbolUse model)
    (RuntimeSymbolIdentity.runtimeSymbolClaimCount model)
    (RuntimeSymbolIdentity.runtimeSymbolAssuranceIdentityEncoded model).

Theorem verified_llvm_runtime_symbol_refines_target_runtime_primitive :
  forall model,
    RuntimeSymbolIdentity.RuntimeSymbolVerificationSuccess model ->
    RuntimePrimitiveIdentity.RuntimePrimitiveIdentityVerificationSuccess
      (llvmRuntimeSymbolAsTargetPrimitive model).
Proof.
  intros model H.
  constructor.
  - exact
      (RuntimeSymbolIdentity.runtime_symbol_success_physical_identity model H).
  - exact
      (RuntimeSymbolIdentity.runtime_symbol_success_no_assurance_encoding model H).
Qed.

Theorem llvm_runtime_symbol_assurance_independence_is_target_neutral :
  forall model revisionA evidenceA useA countA
         revisionB evidenceB useB countB,
    RuntimePrimitiveIdentity.targetEntryFor
      (llvmRuntimeSymbolAsTargetPrimitive model)
      revisionA evidenceA useA countA =
    RuntimePrimitiveIdentity.targetEntryFor
      (llvmRuntimeSymbolAsTargetPrimitive model)
      revisionB evidenceB useB countB.
Proof.
  intros.
  apply RuntimePrimitiveIdentity.runtime_primitive_entry_is_independent_of_assurance_metadata.
Qed.
