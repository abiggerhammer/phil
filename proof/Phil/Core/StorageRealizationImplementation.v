From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import StorageRealization.

(*
  PHIL-MEM-REALIZE-001 — representation-neutral executable decision kernel
  for the Certified storage-realization validity relation.

  Concrete Text/Map/Set representation, finite enumeration of physical
  objects, semantic key serialization, allocator/provider truth, target memory
  facts, diagnostics, and extraction/toolchain correctness remain explicit
  native/evidence/TCB boundaries.
*)

Definition decideStorageRealizationValidByFacts
  (subjectBasisAdmitted exactSubjectPresent semanticRevisionNonzero
   outcomeRevisionNonzero physicalStrategyNonzero selectedSemanticsNonzero
   physicalObjectsNonzero : bool) : bool :=
  andb subjectBasisAdmitted
    (andb exactSubjectPresent
      (andb semanticRevisionNonzero
        (andb outcomeRevisionNonzero
          (andb physicalStrategyNonzero
            (andb selectedSemanticsNonzero physicalObjectsNonzero))))).

Theorem storage_realization_decision_accept_iff_certified :
  forall facts
         subjectBasisAdmitted exactSubjectPresent semanticRevisionNonzero
         outcomeRevisionNonzero physicalStrategyNonzero selectedSemanticsNonzero
         physicalObjectsNonzero,
    (subjectBasisAdmitted = true <->
      storage_subject_binding_admitted (storageRealizationSubject facts)) ->
    (exactSubjectPresent = true <->
      exists subject,
        storageRealizationSubject facts = ExactStorageSemanticSubject subject) ->
    (semanticRevisionNonzero = true <->
      storageRealizationSemanticRevision facts <> 0) ->
    (outcomeRevisionNonzero = true <->
      storageRealizationOutcomeRevision facts <> 0) ->
    (physicalStrategyNonzero = true <->
      storageRealizationPhysicalStrategy facts <> 0) ->
    (selectedSemanticsNonzero = true <->
      storageRealizationSelectedSemantics facts <> 0) ->
    (physicalObjectsNonzero = true <->
      forall object,
        storageRealizationPhysicalObjects facts object = true -> object <> 0) ->
    decideStorageRealizationValidByFacts
      subjectBasisAdmitted exactSubjectPresent semanticRevisionNonzero
      outcomeRevisionNonzero physicalStrategyNonzero selectedSemanticsNonzero
      physicalObjectsNonzero = true <->
    StorageRealizationValid facts.
Proof.
  intros facts
    subjectBasisAdmitted0 exactSubjectPresent0 semanticRevisionNonzero0
    outcomeRevisionNonzero0 physicalStrategyNonzero0 selectedSemanticsNonzero0
    physicalObjectsNonzero0
    HsubjectBasis HexactSubject HsemanticRevision HoutcomeRevision
    HphysicalStrategy HselectedSemantics HphysicalObjects.
  unfold decideStorageRealizationValidByFacts.
  repeat rewrite andb_true_iff.
  rewrite HsubjectBasis, HexactSubject, HsemanticRevision, HoutcomeRevision,
    HphysicalStrategy, HselectedSemantics, HphysicalObjects.
  split.
  - intros [Hsubject [Hexact [Hsemantic [Houtcome [Hstrategy [Hselected Hobjects]]]]]].
    repeat (split; [assumption |]).
    assumption.
  - intros Hvalid.
    destruct Hvalid as
      [Hsubject [Hexact [Hsemantic [Houtcome [Hstrategy [Hselected Hobjects]]]]]].
    repeat (split; [assumption |]).
    assumption.
Qed.
