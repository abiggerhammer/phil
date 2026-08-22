From Stdlib Require Import Strings.String Bool.Bool.

From Phil.Core Require Import Syntax Context SessionStep.

(*
  Proof-oriented model of Phil.Core.Recognition and the grammar gate in
  Phil.Core.Session.

  General Phil [Ty] remains opaque to the existing proof corpus.  The ingress
  gate needs only a grammar-relevant projection of message types, so this file
  models exactly the three cases observed by frameGrammar: ordinary, frame, and
  recursively refined.  This keeps the recognition theorem narrow while still
  proving the recursive refined-frame classification rather than assuming it.
*)

Definition GrammarId := string.
Definition FrameId := string.

Inductive GrammarTy : Type :=
| GrammarOther : GrammarTy
| GrammarFrame : GrammarId -> GrammarTy
| GrammarRefined : GrammarTy -> GrammarTy.

Fixpoint frameGrammar (ty : GrammarTy) : option GrammarId :=
  match ty with
  | GrammarOther => None
  | GrammarFrame grammar => Some grammar
  | GrammarRefined inner => frameGrammar inner
  end.

Inductive RawIngressResult : Type :=
| RawIngressAdvanced : RawIngressResult
| RawIngressRequiresRecognition : GrammarId -> RawIngressResult.

Definition rawReceive (messageTy : GrammarTy) : RawIngressResult :=
  match frameGrammar messageTy with
  | Some grammar => RawIngressRequiresRecognition grammar
  | None => RawIngressAdvanced
  end.

Definition rawOfferPayload (payloadTy : option GrammarTy) : RawIngressResult :=
  match payloadTy with
  | None => RawIngressAdvanced
  | Some messageTy =>
      match frameGrammar messageTy with
      | Some grammar => RawIngressRequiresRecognition grammar
      | None => RawIngressAdvanced
      end
  end.

(* PHIL-RECOG-GATE-001: generic receive cannot cross a grammar-backed ingress. *)
Theorem raw_receive_grammar_backed_rejected :
  forall (messageTy : GrammarTy) (grammar : GrammarId),
    frameGrammar messageTy = Some grammar ->
    rawReceive messageTy = RawIngressRequiresRecognition grammar.
Proof.
  intros messageTy grammar Hgrammar.
  unfold rawReceive.
  rewrite Hgrammar.
  reflexivity.
Qed.

(* PHIL-RECOG-GATE-001: generic external choice cannot cross a grammar payload. *)
Theorem raw_offer_grammar_payload_rejected :
  forall (messageTy : GrammarTy) (grammar : GrammarId),
    frameGrammar messageTy = Some grammar ->
    rawOfferPayload (Some messageTy) = RawIngressRequiresRecognition grammar.
Proof.
  intros messageTy grammar Hgrammar.
  unfold rawOfferPayload.
  rewrite Hgrammar.
  reflexivity.
Qed.

Inductive ReceiveFrameClassification : Type :=
| DirectFrameReady : GrammarId -> ReceiveFrameClassification
| RefinedFrameNeedsValueChecking : GrammarId -> ReceiveFrameClassification
| NotGrammarBacked : ReceiveFrameClassification.

Definition receiveFrameClassification (messageTy : GrammarTy)
  : ReceiveFrameClassification :=
  match messageTy with
  | GrammarFrame grammar => DirectFrameReady grammar
  | GrammarRefined inner =>
      match frameGrammar inner with
      | Some grammar => RefinedFrameNeedsValueChecking grammar
      | None => NotGrammarBacked
      end
  | GrammarOther => NotGrammarBacked
  end.

(* PHIL-RECOG-REFINE-001: refinement never silently strips the grammar gate. *)
Theorem refined_grammar_receive_fails_closed :
  forall (inner : GrammarTy) (grammar : GrammarId),
    frameGrammar inner = Some grammar ->
    receiveFrameClassification (GrammarRefined inner) =
      RefinedFrameNeedsValueChecking grammar.
Proof.
  intros inner grammar Hgrammar.
  simpl.
  rewrite Hgrammar.
  reflexivity.
Qed.

Corollary refined_grammar_raw_receive_still_rejected :
  forall (inner : GrammarTy) (grammar : GrammarId),
    frameGrammar inner = Some grammar ->
    rawReceive (GrammarRefined inner) = RawIngressRequiresRecognition grammar.
Proof.
  intros inner grammar Hgrammar.
  apply raw_receive_grammar_backed_rejected.
  simpl.
  exact Hgrammar.
Qed.

(*
  Once pendingSpecFor has dynamically established a TyPendingRecv owner, the
  proof treats that fact as a typed capability.  [pendingType] is the opaque
  embedding of the Haskell TyPendingRecv constructor into the existing
  proof-side Ty abstraction.  The ownership equality is exactly the fact
  established by successful pendingSpecFor lookup.
*)

Record PendingSpec : Type := mkPendingSpec
  { pendingSourceEndpoint : Name
  ; pendingGrammar : GrammarId
  ; pendingFrame : FrameId
  ; pendingBinder : Name
  ; pendingContinuation : Session
  }.

Parameter pendingType : PendingSpec -> Ty.

Record PendingCapability : Type := mkPendingCapability
  { capabilityName : Name
  ; capabilitySpec : PendingSpec
  ; capabilityContext : ResourceContext
  ; capabilityOwned :
      linearBindings capabilityContext capabilityName =
        Some (pendingType capabilitySpec)
  }.

Record ParsedWitness : Type := mkParsedWitness
  { parsedPendingOwner : Name
  ; parsedGrammar : GrammarId
  ; parsedFrame : FrameId
  ; parsedValueName : Name
  }.

Record RecognitionFailure : Type := mkRecognitionFailure
  { failurePendingOwner : Name
  ; failureGrammar : GrammarId
  ; failureFrame : FrameId
  ; failureDetail : string
  }.

Inductive RecognitionStepResult : Type :=
| RecognitionRejected : RecognitionStepResult
| RecognitionCommitted : ResourceContext -> RecognitionStepResult.

Definition commitReceiveModel
  (capability : PendingCapability)
  (successor : Name)
  (parsed : ParsedWitness) : RecognitionStepResult :=
  let pendingName := capabilityName capability in
  let pending := capabilitySpec capability in
  let context := capabilityContext capability in
  if String.eqb (parsedPendingOwner parsed) pendingName then
    if String.eqb (parsedGrammar parsed) (pendingGrammar pending) then
      if String.eqb (parsedFrame parsed) (pendingFrame pending) then
        if String.eqb pendingName successor then
          RecognitionRejected
        else if String.eqb (pendingSourceEndpoint pending) successor then
          RecognitionRejected
        else
          match consumeLinear pendingName context with
          | ConsumeError _ => RecognitionRejected
          | Consumed _ consumed =>
              match insertBinding
                      Linear successor
                      (endpointType (pendingContinuation pending))
                      consumed with
              | InsertError _ => RecognitionRejected
              | Inserted continued => RecognitionCommitted continued
              end
          end
      else RecognitionRejected
    else RecognitionRejected
  else RecognitionRejected.

(*
  PHIL-RECOG-COMMIT-001.

  A successful commit is possible only with evidence for this exact pending
  owner/grammar/frame, with a successor distinct from both ingress identities.
  It consumes the pending linear capability and installs exactly the recorded
  continuation endpoint, while preserving unrelated linear resources and loans.
*)
Theorem commitReceive_success_exact :
  forall (capability : PendingCapability)
         (successor : Name)
         (parsed : ParsedWitness)
         (next : ResourceContext),
    commitReceiveModel capability successor parsed = RecognitionCommitted next ->
    parsedPendingOwner parsed = capabilityName capability /\
    parsedGrammar parsed = pendingGrammar (capabilitySpec capability) /\
    parsedFrame parsed = pendingFrame (capabilitySpec capability) /\
    String.eqb (capabilityName capability) successor = false /\
    String.eqb (pendingSourceEndpoint (capabilitySpec capability)) successor = false /\
    linearBindings (capabilityContext capability) (capabilityName capability) =
      Some (pendingType (capabilitySpec capability)) /\
    linearBindings next (capabilityName capability) = None /\
    linearBindings next successor =
      Some (endpointType (pendingContinuation (capabilitySpec capability))) /\
    (forall other : Name,
      String.eqb other (capabilityName capability) = false ->
      String.eqb other successor = false ->
      linearBindings next other =
        linearBindings (capabilityContext capability) other) /\
    sharedLoans next = sharedLoans (capabilityContext capability).
Proof.
  intros capability successor parsed next Hcommit.
  destruct capability as [pendingName pending context HcapOwned].
  destruct pending as [source grammar frame binder continuation].
  destruct parsed as [parsedOwner parsedGrammarId parsedFrameId valueName].
  simpl in *.
  unfold commitReceiveModel in Hcommit.
  simpl in Hcommit.
  destruct (String.eqb parsedOwner pendingName) eqn:Howner.
  - destruct (String.eqb parsedGrammarId grammar) eqn:Hgrammar.
    + destruct (String.eqb parsedFrameId frame) eqn:Hframe.
      * destruct (String.eqb pendingName successor) eqn:HpendingSuccessor.
        -- discriminate.
        -- destruct (String.eqb source successor) eqn:HsourceSuccessor.
           ++ discriminate.
           ++ destruct (consumeLinear pendingName context)
                as [consumeError | consumedTy consumed] eqn:Hconsume.
              ** discriminate.
              ** destruct
                   (insertBinding Linear successor (endpointType continuation) consumed)
                   as [insertError | continued] eqn:Hinsert.
                 --- discriminate.
                 --- inversion Hcommit; subst next; clear Hcommit.
                     apply String.eqb_eq in Howner.
                     apply String.eqb_eq in Hgrammar.
                     apply String.eqb_eq in Hframe.
                     pose proof
                       (consumeLinear_success_exact
                         pendingName context consumed consumedTy Hconsume)
                       as HconsumeExact.
                     pose proof
                       (insertBinding_success_exact
                         Linear successor (endpointType continuation)
                         consumed continued Hinsert)
                       as HinsertExact.
                     destruct HconsumeExact as
                       [HconsumeOwned
                         [HpendingGone
                           [HconsumeOther [HU [HA HconsumeLoans]]]]].
                     destruct HinsertExact as
                       [HsuccU
                         [HsuccA
                           [HsuccL
                             [Hselected [HinsertOther HinsertLoans]]]]].
                     simpl in Hselected.
                     destruct Hselected as
                       [HnextU [HnextA HsuccessorInstalled]].
                     pose proof
                       (HinsertOther pendingName HpendingSuccessor)
                       as HpendingPreserved.
                     destruct HpendingPreserved as
                       [HpendingU [HpendingA HpendingLinearPreserved]].
                     repeat split; try assumption.
                     { rewrite HpendingLinearPreserved.
                       exact HpendingGone. }
                     { intros other HotherPending HotherSuccessor.
                       pose proof
                         (HconsumeOther other HotherPending)
                         as HconsumePreserved.
                       pose proof
                         (HinsertOther other HotherSuccessor)
                         as HinsertPreserved.
                       destruct HinsertPreserved as
                         [HotherU [HotherA HinsertLinearPreserved]].
                       rewrite HinsertLinearPreserved.
                       exact HconsumePreserved. }
                     { rewrite HinsertLoans.
                       exact HconsumeLoans. }
      * discriminate.
    + discriminate.
  - discriminate.
Qed.

Definition failPendingRecognitionModel
  (capability : PendingCapability)
  (failure : RecognitionFailure) : RecognitionStepResult :=
  let pendingName := capabilityName capability in
  let pending := capabilitySpec capability in
  let context := capabilityContext capability in
  if String.eqb (failurePendingOwner failure) pendingName then
    if String.eqb (failureGrammar failure) (pendingGrammar pending) then
      if String.eqb (failureFrame failure) (pendingFrame pending) then
        match consumeLinear pendingName context with
        | ConsumeError _ => RecognitionRejected
        | Consumed _ consumed => RecognitionCommitted consumed
        end
      else RecognitionRejected
    else RecognitionRejected
  else RecognitionRejected.

(*
  PHIL-RECOG-FAIL-001.

  A successful failure transition requires the same provenance match as commit,
  then consumes the pending capability without constructing a successor.  The
  failure detail is deliberately absent from the matching condition.
*)
Theorem failPendingRecognition_success_exact :
  forall (capability : PendingCapability)
         (failure : RecognitionFailure)
         (next : ResourceContext),
    failPendingRecognitionModel capability failure = RecognitionCommitted next ->
    failurePendingOwner failure = capabilityName capability /\
    failureGrammar failure = pendingGrammar (capabilitySpec capability) /\
    failureFrame failure = pendingFrame (capabilitySpec capability) /\
    linearBindings (capabilityContext capability) (capabilityName capability) =
      Some (pendingType (capabilitySpec capability)) /\
    linearBindings next (capabilityName capability) = None /\
    (forall other : Name,
      String.eqb other (capabilityName capability) = false ->
      linearBindings next other =
        linearBindings (capabilityContext capability) other) /\
    sharedLoans next = sharedLoans (capabilityContext capability).
Proof.
  intros capability failure next Hfailure.
  destruct capability as [pendingName pending context HcapOwned].
  destruct pending as [source grammar frame binder continuation].
  destruct failure as [failureOwner failureGrammarId failureFrameId detail].
  simpl in *.
  unfold failPendingRecognitionModel in Hfailure.
  simpl in Hfailure.
  destruct (String.eqb failureOwner pendingName) eqn:Howner.
  - destruct (String.eqb failureGrammarId grammar) eqn:Hgrammar.
    + destruct (String.eqb failureFrameId frame) eqn:Hframe.
      * destruct (consumeLinear pendingName context)
          as [consumeError | consumedTy consumed] eqn:Hconsume.
        -- discriminate.
        -- inversion Hfailure; subst next; clear Hfailure.
           apply String.eqb_eq in Howner.
           apply String.eqb_eq in Hgrammar.
           apply String.eqb_eq in Hframe.
           pose proof
             (consumeLinear_success_exact
               pendingName context consumed consumedTy Hconsume)
             as HconsumeExact.
           destruct HconsumeExact as
             [HconsumeOwned
               [HpendingGone [Hother [HU [HA Hloans]]]]].
           repeat split; assumption.
      * discriminate.
    + discriminate.
  - discriminate.
Qed.
