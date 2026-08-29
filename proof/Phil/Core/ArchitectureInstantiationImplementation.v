From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ArchitectureInstantiation.

(*
  Representation-neutral implementation correspondence for Certified
  PHIL-ARCH-INST-001.

  Production remains responsible for reflecting concrete Map/list/Text facts
  into the Booleans consumed here.  These lemmas characterize the complete
  decision surface already present in ArchitectureInstantiation.v; they do not
  strengthen the Certified graph semantics.
*)

Theorem child_slot_decision_accepted_iff_fresh :
  forall slotFresh,
    decideChildSlotByFacts slotFresh = ChildSlotAccepted <->
    slotFresh = true.
Proof.
  destruct slotFresh; simpl; intuition discriminate.
Qed.

Theorem child_slot_decision_duplicate_iff_not_fresh :
  forall slotFresh,
    decideChildSlotByFacts slotFresh = ChildSlotDuplicate <->
    slotFresh = false.
Proof.
  destruct slotFresh; simpl; intuition discriminate.
Qed.

Theorem architecture_requirement_decision_unresolved_iff_implicit :
  forall hasExplicitDisposition isBoundTo targetExists interfaceMatches,
    decideArchitectureRequirementByFacts
      hasExplicitDisposition isBoundTo targetExists interfaceMatches =
      ArchitectureRequirementUnresolved <->
    hasExplicitDisposition = false.
Proof.
  destruct hasExplicitDisposition, isBoundTo, targetExists, interfaceMatches;
    simpl; intuition discriminate.
Qed.

Theorem architecture_requirement_decision_missing_target_iff_reflected :
  forall hasExplicitDisposition isBoundTo targetExists interfaceMatches,
    decideArchitectureRequirementByFacts
      hasExplicitDisposition isBoundTo targetExists interfaceMatches =
      ArchitectureRequirementMissingBindingTarget <->
    hasExplicitDisposition = true /\
    isBoundTo = true /\
    targetExists = false.
Proof.
  destruct hasExplicitDisposition, isBoundTo, targetExists, interfaceMatches;
    simpl; intuition discriminate.
Qed.

Theorem architecture_requirement_decision_interface_mismatch_iff_reflected :
  forall hasExplicitDisposition isBoundTo targetExists interfaceMatches,
    decideArchitectureRequirementByFacts
      hasExplicitDisposition isBoundTo targetExists interfaceMatches =
      ArchitectureRequirementInterfaceMismatch <->
    hasExplicitDisposition = true /\
    isBoundTo = true /\
    targetExists = true /\
    interfaceMatches = false.
Proof.
  destruct hasExplicitDisposition, isBoundTo, targetExists, interfaceMatches;
    simpl; intuition discriminate.
Qed.

Theorem architecture_requirement_decision_accepted_iff_reflected :
  forall hasExplicitDisposition isBoundTo targetExists interfaceMatches,
    decideArchitectureRequirementByFacts
      hasExplicitDisposition isBoundTo targetExists interfaceMatches =
      ArchitectureRequirementAccepted <->
    hasExplicitDisposition = true /\
    (isBoundTo = false \/
      (targetExists = true /\ interfaceMatches = true)).
Proof.
  destruct hasExplicitDisposition, isBoundTo, targetExists, interfaceMatches;
    simpl; intuition discriminate.
Qed.

Theorem root_requirement_decision_is_architecture_requirement_decision :
  forall hasExplicitDisposition isBoundTo targetExists interfaceMatches,
    decideRootRequirementByFacts
      hasExplicitDisposition isBoundTo targetExists interfaceMatches =
    decideArchitectureRequirementByFacts
      hasExplicitDisposition isBoundTo targetExists interfaceMatches.
Proof.
  reflexivity.
Qed.

Theorem architecture_reference_decision_accepted_iff_target_exists :
  forall targetExists,
    decideArchitectureReferenceByFacts targetExists =
      ArchitectureReferenceAccepted <->
    targetExists = true.
Proof.
  destruct targetExists; simpl; intuition discriminate.
Qed.

Theorem architecture_reference_decision_unknown_iff_target_missing :
  forall targetExists,
    decideArchitectureReferenceByFacts targetExists =
      ArchitectureReferenceUnknownTarget <->
    targetExists = false.
Proof.
  destruct targetExists; simpl; intuition discriminate.
Qed.
