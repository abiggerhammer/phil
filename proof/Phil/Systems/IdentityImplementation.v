From Stdlib Require Import Bool.Bool.

From Phil.Systems Require Import Identity.

(*
  Mechanical implementation-refinement surface for already-Certified
  PHIL-SYS-ID-001.  The extracted classifiers own only the exact equality
  gates stated in Identity.v.  Concrete digest construction, canonical
  serialization, Map/Set traversal, and detailed Haskell diagnostics remain
  explicit correspondence boundaries.
*)

Inductive ArtifactIdentityDecision : Type :=
| ArtifactIdentityAcceptedDecision
| ArtifactIdentitySourceDecision
| ArtifactIdentityTargetDecision
| ArtifactIdentityImplementationDecision
| ArtifactIdentityDeclaredRootDecision
| ArtifactIdentityManifestRootDecision.

Definition decideArtifactIdentityByFacts
  (sourceMatches targetMatches implementationMatches
   declaredRootMatches manifestRootMatches : bool)
  : ArtifactIdentityDecision :=
  if sourceMatches then
    if targetMatches then
      if implementationMatches then
        if declaredRootMatches then
          if manifestRootMatches
          then ArtifactIdentityAcceptedDecision
          else ArtifactIdentityManifestRootDecision
        else ArtifactIdentityDeclaredRootDecision
      else ArtifactIdentityImplementationDecision
    else ArtifactIdentityTargetDecision
  else ArtifactIdentitySourceDecision.

Theorem artifact_identity_decision_exact :
  forall sourceMatches targetMatches implementationMatches
         declaredRootMatches manifestRootMatches,
    decideArtifactIdentityByFacts
      sourceMatches targetMatches implementationMatches
      declaredRootMatches manifestRootMatches =
      ArtifactIdentityAcceptedDecision <->
    sourceMatches = true /\
    targetMatches = true /\
    implementationMatches = true /\
    declaredRootMatches = true /\
    manifestRootMatches = true.
Proof.
  intros sourceMatches targetMatches implementationMatches
    declaredRootMatches manifestRootMatches.
  unfold decideArtifactIdentityByFacts.
  destruct sourceMatches; destruct targetMatches; destruct implementationMatches;
    destruct declaredRootMatches; destruct manifestRootMatches;
    simpl; intuition congruence.
Qed.

Theorem artifact_identity_decision_corresponds_verification :
  forall model sourceMatches targetMatches implementationMatches
         declaredRootMatches manifestRootMatches,
    (sourceMatches = true <->
      stageSourceArtifact model = trustedSourceArtifact model) ->
    (targetMatches = true <->
      stageTargetArtifact model = computedSystemsProgram model) ->
    (implementationMatches = true <->
      manifestImplementationArtifact model = computedSystemsArtifact model) ->
    (declaredRootMatches = true <->
      declaredLoweringRoot model = computedLoweringRoot model) ->
    (manifestRootMatches = true <->
      manifestLoweringRoot model = declaredLoweringRoot model) ->
    decideArtifactIdentityByFacts
      sourceMatches targetMatches implementationMatches
      declaredRootMatches manifestRootMatches =
      ArtifactIdentityAcceptedDecision <->
    ArtifactIdentityVerified model.
Proof.
  intros model sourceMatches targetMatches implementationMatches
    declaredRootMatches manifestRootMatches
    Hsource Htarget Himplementation Hdeclared Hmanifest.
  split.
  - intros Haccepted.
    apply artifact_identity_decision_exact in Haccepted.
    destruct Haccepted as
      [HsourceAccepted
        [HtargetAccepted
          [HimplementationAccepted [HdeclaredAccepted HmanifestAccepted]]]].
    repeat split.
    + exact ((proj1 Hsource) HsourceAccepted).
    + exact ((proj1 Htarget) HtargetAccepted).
    + exact ((proj1 Himplementation) HimplementationAccepted).
    + exact ((proj1 Hdeclared) HdeclaredAccepted).
    + exact ((proj1 Hmanifest) HmanifestAccepted).
  - intros Hverified.
    destruct Hverified as
      [HsourceVerified
        [HtargetVerified
          [HimplementationVerified [HdeclaredVerified HmanifestVerified]]]].
    apply artifact_identity_decision_exact.
    repeat split.
    + exact ((proj2 Hsource) HsourceVerified).
    + exact ((proj2 Htarget) HtargetVerified).
    + exact ((proj2 Himplementation) HimplementationVerified).
    + exact ((proj2 Hdeclared) HdeclaredVerified).
    + exact ((proj2 Hmanifest) HmanifestVerified).
Qed.

Inductive DecisionBindingDecision : Type :=
| DecisionBindingAcceptedDecision
| DecisionBindingNonemptyDecision
| DecisionBindingMapKeyDecision
| DecisionBindingDigestDecision
| DecisionBindingSourceDecision
| DecisionBindingTargetDecision.

Definition decideDecisionBindingByFacts
  (nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches : bool)
  : DecisionBindingDecision :=
  if nonemptyStableId then
    if mapKeyMatches then
      if digestMatches then
        if sourceMatches then
          if targetMatches
          then DecisionBindingAcceptedDecision
          else DecisionBindingTargetDecision
        else DecisionBindingSourceDecision
      else DecisionBindingDigestDecision
    else DecisionBindingMapKeyDecision
  else DecisionBindingNonemptyDecision.

Theorem decision_binding_decision_exact :
  forall nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches,
    decideDecisionBindingByFacts
      nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches =
      DecisionBindingAcceptedDecision <->
    nonemptyStableId = true /\
    mapKeyMatches = true /\
    digestMatches = true /\
    sourceMatches = true /\
    targetMatches = true.
Proof.
  intros nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches.
  unfold decideDecisionBindingByFacts.
  destruct nonemptyStableId; destruct mapKeyMatches; destruct digestMatches;
    destruct sourceMatches; destruct targetMatches;
    simpl; intuition congruence.
Qed.

Theorem decision_binding_decision_corresponds_verification :
  forall source target decision
         nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches,
    (nonemptyStableId = true <-> decisionMapKey decision <> 0) ->
    (mapKeyMatches = true <->
      decisionMapKey decision = decisionStableId decision) ->
    (digestMatches = true <->
      decisionDeclaredDigest decision = decisionComputedDigest decision) ->
    (sourceMatches = true <-> decisionSourceArtifact decision = source) ->
    (targetMatches = true <-> decisionTargetArtifact decision = target) ->
    decideDecisionBindingByFacts
      nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches =
      DecisionBindingAcceptedDecision <->
    DecisionBindingVerified source target decision.
Proof.
  intros source target decision
    nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches
    Hnonempty Hkey Hdigest Hsource Htarget.
  split.
  - intros Haccepted.
    apply decision_binding_decision_exact in Haccepted.
    destruct Haccepted as
      [HnonemptyAccepted
        [HkeyAccepted [HdigestAccepted [HsourceAccepted HtargetAccepted]]]].
    repeat split.
    + exact ((proj1 Hnonempty) HnonemptyAccepted).
    + exact ((proj1 Hkey) HkeyAccepted).
    + exact ((proj1 Hdigest) HdigestAccepted).
    + exact ((proj1 Hsource) HsourceAccepted).
    + exact ((proj1 Htarget) HtargetAccepted).
  - intros Hverified.
    destruct Hverified as
      [HnonemptyVerified
        [HkeyVerified [HdigestVerified [HsourceVerified HtargetVerified]]]].
    apply decision_binding_decision_exact.
    repeat split.
    + exact ((proj2 Hnonempty) HnonemptyVerified).
    + exact ((proj2 Hkey) HkeyVerified).
    + exact ((proj2 Hdigest) HdigestVerified).
    + exact ((proj2 Hsource) HsourceVerified).
    + exact ((proj2 Htarget) HtargetVerified).
Qed.
