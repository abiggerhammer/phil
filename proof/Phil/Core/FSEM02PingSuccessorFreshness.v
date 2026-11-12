From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression
  FSEM02OfferSuccessorFreshness.

(* NON-NORMATIVE FSEM-02: the source Ping role projection, nominal instance
   and actual Haskell error constructors are independently checked inputs.
   This extensional resource model is not universal Haskell refinement. *)
Open Scope string_scope.

Theorem fsem02PingSendReceiveRejectOccupiedSuccessor :
  forall binder ty continuation endpoint successor context,
    String.eqb successor endpoint = false ->
    bindingExists successor context = true ->
    fsem02Progression FSEM02Send
      (Send binder ty continuation) endpoint successor context = StepFailed /\
    fsem02Progression FSEM02Receive
      (Receive binder ty continuation) endpoint successor context = StepFailed.
Proof.
  intros binder ty continuation endpoint successor context Hdistinct Hoccupied.
  split.
  - change (continueEndpointResource endpoint successor continuation context
      = StepFailed).
    apply fsem02OccupiedUnrelatedSuccessorCannotContinue; assumption.
  - change (continueEndpointResource endpoint successor continuation context
      = StepFailed).
    apply fsem02OccupiedUnrelatedSuccessorCannotContinue; assumption.
Qed.

Theorem fsem02PingSendReceiveRejectPredecessorReuse :
  forall binder ty continuation endpoint context,
    fsem02Progression FSEM02Send (Send binder ty continuation)
      endpoint endpoint context = StepFailed /\
    fsem02Progression FSEM02Receive (Receive binder ty continuation)
      endpoint endpoint context = StepFailed.
Proof.
  intros binder ty continuation endpoint context.
  split; eapply same_name_successor_rejects; reflexivity.
Qed.

(* The existing SessionStep result states the linear frame and loan
   preservation. This strengthens that finite model with *full extensional*
   affine-map preservation, hence borrowed affine spectators cannot disappear
   during successful linear endpoint continuation. *)
Theorem fsem02PingContinuationPreservesAffineAndLoans :
  forall action head endpoint successor context next continuation,
    selectedContinuation action head = Some (Some continuation) ->
    fsem02Progression action head endpoint successor context = StepSucceeded next ->
    affineBindings next = affineBindings context /\
    sharedLoans next = sharedLoans context.
Proof.
  intros action head endpoint successor context next continuation Hselected Hstep.
  unfold fsem02Progression in Hstep.
  rewrite Hselected in Hstep.
  unfold continueEndpointResource in Hstep.
  destruct (consumeLinear endpoint context) as [error | owned consumed]
    eqn:Hconsume; try discriminate.
  destruct (String.eqb endpoint successor) eqn:Hsame; try discriminate.
  destruct (insertBinding Linear successor (endpointType continuation) consumed)
    as [error | continued] eqn:Hinsert; try discriminate.
  inversion Hstep; subst next; clear Hstep.
  pose proof (consumeLinear_success_exact endpoint context consumed owned Hconsume)
    as HconsumeExact.
  destruct HconsumeExact as [_ [_ [_ [_ [Haffine Hloans]]]]].
  unfold insertBinding in Hinsert.
  destruct (bindingExists successor consumed) eqn:Hoccupied; try discriminate.
  inversion Hinsert; subst continued; simpl.
  split; assumption.
Qed.

Theorem fsem02PingSendReceivePreserveAffineLoans :
  forall binder ty continuation endpoint successor context sent received,
    fsem02Progression FSEM02Send (Send binder ty continuation)
      endpoint successor context = StepSucceeded sent ->
    fsem02Progression FSEM02Receive (Receive binder ty continuation)
      endpoint successor context = StepSucceeded received ->
    affineBindings sent = affineBindings context /\
    sharedLoans sent = sharedLoans context /\
    affineBindings received = affineBindings context /\
    sharedLoans received = sharedLoans context.
Proof.
  intros binder ty continuation endpoint successor context sent received
    Hsend Hreceive.
  pose proof (fsem02PingContinuationPreservesAffineAndLoans
    FSEM02Send (Send binder ty continuation) endpoint successor
    context sent continuation eq_refl Hsend) as [HsendA HsendLoans].
  pose proof (fsem02PingContinuationPreservesAffineAndLoans
    FSEM02Receive (Receive binder ty continuation) endpoint successor
    context received continuation eq_refl Hreceive) as [HrecvA HrecvLoans].
  repeat split; assumption.
Qed.
