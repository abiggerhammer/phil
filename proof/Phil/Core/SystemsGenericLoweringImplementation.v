From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsGenericLowering.

(*
  Mechanical implementation-refinement surface for already-Certified
  PHIL-SYS-GENERIC-001.  The extracted classifier owns only the normalized
  admission condition proved by SystemsGenericLowering.v.  Concrete Haskell
  Maps/Sets/Text, canonical serialization, digest construction, lowering
  diagnostics, and witness adapters remain explicit correspondence boundaries.
*)

Inductive GenericSystemsLoweringDecision : Type :=
| GenericSystemsLoweringAcceptedDecision
| GenericSystemsLoweringContextRevisionDecision
| GenericSystemsLoweringVerifierProfileDecision
| GenericSystemsLoweringRealizationRefsDecision
| GenericSystemsLoweringRealizationSemanticDecision
| GenericSystemsLoweringResultCorrespondenceDecision
| GenericSystemsLoweringStageClosureDecision.

Definition decideGenericSystemsLoweringByFacts
  (contextRevisionPresent
   verifierProfilePresent
   realizationRefsPresent
   realizationSemanticPresent
   resultMatchesModel
   stageClosureAccepted : bool)
  : GenericSystemsLoweringDecision :=
  if contextRevisionPresent then
    if verifierProfilePresent then
      if realizationRefsPresent then
        if realizationSemanticPresent then
          if resultMatchesModel then
            if stageClosureAccepted
            then GenericSystemsLoweringAcceptedDecision
            else GenericSystemsLoweringStageClosureDecision
          else GenericSystemsLoweringResultCorrespondenceDecision
        else GenericSystemsLoweringRealizationSemanticDecision
      else GenericSystemsLoweringRealizationRefsDecision
    else GenericSystemsLoweringVerifierProfileDecision
  else GenericSystemsLoweringContextRevisionDecision.

Theorem generic_systems_lowering_decision_exact :
  forall contextRevisionPresent verifierProfilePresent realizationRefsPresent
         realizationSemanticPresent resultMatchesModel stageClosureAccepted,
    decideGenericSystemsLoweringByFacts
      contextRevisionPresent verifierProfilePresent realizationRefsPresent
      realizationSemanticPresent resultMatchesModel stageClosureAccepted =
      GenericSystemsLoweringAcceptedDecision <->
    contextRevisionPresent = true /\
    verifierProfilePresent = true /\
    realizationRefsPresent = true /\
    realizationSemanticPresent = true /\
    resultMatchesModel = true /\
    stageClosureAccepted = true.
Proof.
  intros contextRevisionPresent verifierProfilePresent realizationRefsPresent
    realizationSemanticPresent resultMatchesModel stageClosureAccepted.
  unfold decideGenericSystemsLoweringByFacts.
  destruct contextRevisionPresent; destruct verifierProfilePresent;
    destruct realizationRefsPresent; destruct realizationSemanticPresent;
    destruct resultMatchesModel; destruct stageClosureAccepted;
    simpl; intuition congruence.
Qed.

Theorem generic_systems_lowering_decision_corresponds_certification :
  forall input context result factModel live mechanisms dispositions kinds
         justifications scope effective identity
         contextRevisionPresent verifierProfilePresent realizationRefsPresent
         realizationSemanticPresent resultMatchesModel stageClosureAccepted,
    (contextRevisionPresent = true <-> genericContextRevision context <> 0) ->
    (verifierProfilePresent = true <->
      genericContextVerifierProfileRevision context <> 0) ->
    (realizationRefsPresent = true <->
      genericContextRealizationRefsRevision context <> 0) ->
    (realizationSemanticPresent = true <->
      genericContextRealizationSemanticRevision context <> 0) ->
    (resultMatchesModel = true <->
      result = lowerGenericSystemsModel input context) ->
    (stageClosureAccepted = true <->
      SystemsStageClosurePreserved
        factModel live mechanisms dispositions kinds justifications
        scope effective identity) ->
    decideGenericSystemsLoweringByFacts
      contextRevisionPresent verifierProfilePresent realizationRefsPresent
      realizationSemanticPresent resultMatchesModel stageClosureAccepted =
      GenericSystemsLoweringAcceptedDecision <->
    CertifiedGenericSystemsLowering
      input context result factModel live mechanisms dispositions kinds
      justifications scope effective identity.
Proof.
  intros input context result factModel live mechanisms dispositions kinds
    justifications scope effective identity
    contextRevisionPresent verifierProfilePresent realizationRefsPresent
    realizationSemanticPresent resultMatchesModel stageClosureAccepted
    Hcontext Hprofile Hrefs Hrealization Hresult Hclosure.
  split.
  - intros Haccepted.
    apply generic_systems_lowering_decision_exact in Haccepted.
    destruct Haccepted as
      [HcontextAccepted
        [HprofileAccepted
          [HrefsAccepted
            [HrealizationAccepted [HresultAccepted HclosureAccepted]]]]].
    constructor.
    + split.
      * repeat split.
        -- exact ((proj1 Hcontext) HcontextAccepted).
        -- exact ((proj1 Hprofile) HprofileAccepted).
        -- exact ((proj1 Hrefs) HrefsAccepted).
        -- exact ((proj1 Hrealization) HrealizationAccepted).
      * exact ((proj1 Hresult) HresultAccepted).
    + exact ((proj1 Hclosure) HclosureAccepted).
  - intros Hcertified.
    destruct Hcertified as [Hlowering Hstage].
    destruct Hlowering as [Hvalid HresultExact].
    destruct Hvalid as [HcontextValid [HprofileValid [HrefsValid HrealizationValid]]].
    apply generic_systems_lowering_decision_exact.
    repeat split.
    + exact ((proj2 Hcontext) HcontextValid).
    + exact ((proj2 Hprofile) HprofileValid).
    + exact ((proj2 Hrefs) HrefsValid).
    + exact ((proj2 Hrealization) HrealizationValid).
    + exact ((proj2 Hresult) HresultExact).
    + exact ((proj2 Hclosure) Hstage).
Qed.
