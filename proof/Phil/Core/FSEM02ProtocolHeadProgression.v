From Stdlib Require Import Strings.String.

From Phil.Core Require Import Syntax Context SessionStep ConcurrencySemantics.

(*
  FSEM-02 / bounded non-normative progression model.

  The selected head is an INPUT established by the concrete protocol checker.
  This file does not infer TyEndpoint from SessionStep.endpointType (an abstract
  historical token), does not prove Haskell-to-Rocq refinement, and does not
  claim an implementation scheduler or a global rendezvous simulation.
  Offer branch-label uniqueness is a separately checked Haskell premise.
*)

Inductive FSEM02Action : Type :=
| FSEM02Send
| FSEM02Receive
| FSEM02Select (label : string)
| FSEM02Offer (label : string)
| FSEM02Close (outcome : Outcome).

Fixpoint offeredContinuation (label : string) (branches : Branches)
  : option Session :=
  match branches with
  | BNil => None
  | BCons candidate _ continuation rest =>
      if String.eqb label candidate then Some continuation
      else offeredContinuation label rest
  end.

Definition selectedContinuation (action : FSEM02Action) (head : Session)
  : option (option Session) :=
  match action, head with
  | FSEM02Send, Send _ _ continuation => Some (Some continuation)
  | FSEM02Receive, Receive _ _ continuation => Some (Some continuation)
  | FSEM02Select label, Select branches =>
      match offeredContinuation label branches with
      | Some continuation => Some (Some continuation)
      | None => None
      end
  | FSEM02Offer label, Offer branches =>
      match offeredContinuation label branches with
      | Some continuation => Some (Some continuation)
      | None => None
      end
  | FSEM02Close actual, End expected =>
      if String.eqb expected actual then Some None else None
  | _, _ => None
  end.

Definition fsem02Progression
  (action : FSEM02Action) (head : Session)
  (endpoint successor : Name) (context : ResourceContext)
  : ResourceStepResult :=
  match selectedContinuation action head with
  | Some (Some continuation) =>
      continueEndpointResource endpoint successor continuation context
  | Some None => closeEndpointResource endpoint context
  | None => StepFailed
  end.

Theorem continuing_head_exact_predecessor_and_successor :
  forall action head endpoint successor context next continuation,
    selectedContinuation action head = Some (Some continuation) ->
    fsem02Progression action head endpoint successor context =
      StepSucceeded next ->
    String.eqb endpoint successor = false /\
    (exists endpointTy : Ty,
      linearBindings context endpoint = Some endpointTy) /\
    linearBindings next endpoint = None /\
    linearBindings next successor = Some (endpointType continuation) /\
    (forall other : Name,
      String.eqb other endpoint = false ->
      String.eqb other successor = false ->
      linearBindings next other = linearBindings context other) /\
    sharedLoans next = sharedLoans context.
Proof.
  intros action head endpoint successor context next continuation Hselected Hstep.
  unfold fsem02Progression in Hstep.
  rewrite Hselected in Hstep.
  exact (continueEndpointResource_success_exact
    endpoint successor continuation context next Hstep).
Qed.

Theorem matched_terminal_close_consumes_without_successor :
  forall action head endpoint successor context next,
    selectedContinuation action head = Some None ->
    fsem02Progression action head endpoint successor context =
      StepSucceeded next ->
    (exists endpointTy : Ty,
      linearBindings context endpoint = Some endpointTy) /\
    linearBindings next endpoint = None /\
    (forall other : Name,
      String.eqb other endpoint = false ->
      linearBindings next other = linearBindings context other) /\
    sharedLoans next = sharedLoans context.
Proof.
  intros action head endpoint successor context next Hselected Hstep.
  unfold fsem02Progression in Hstep.
  rewrite Hselected in Hstep.
  exact (closeEndpointResource_success_exact endpoint context next Hstep).
Qed.

Theorem terminal_is_not_a_send_head :
  forall outcome endpoint successor context,
    fsem02Progression FSEM02Send (End outcome) endpoint successor context =
      StepFailed.
Proof. reflexivity. Qed.

Theorem unavailable_offer_branch_rejects :
  forall label branches endpoint successor context,
    offeredContinuation label branches = None ->
    fsem02Progression (FSEM02Offer label) (Offer branches)
      endpoint successor context = StepFailed.
Proof.
  intros label branches endpoint successor context Hmissing.
  unfold fsem02Progression, selectedContinuation.
  rewrite Hmissing.
  reflexivity.
Qed.

(*
  A bounded, head-matched choice comparison: the selector's chosen label and
  the offerer's externally supplied label yield the same LOCAL resource
  transition on an identical admitted branch catalog. This does not prove
  network rendezvous or that a source offer covers every branch.
*)
Theorem select_offer_identical_local_resource_step :
  forall label branches endpoint successor context,
    fsem02Progression (FSEM02Select label) (Select branches)
      endpoint successor context =
    fsem02Progression (FSEM02Offer label) (Offer branches)
      endpoint successor context.
Proof. reflexivity. Qed.

Theorem unavailable_select_branch_rejects :
  forall label branches endpoint successor context,
    offeredContinuation label branches = None ->
    fsem02Progression (FSEM02Select label) (Select branches)
      endpoint successor context = StepFailed.
Proof.
  intros label branches endpoint successor context Hmissing.
  unfold fsem02Progression, selectedContinuation.
  rewrite Hmissing. reflexivity.
Qed.

Theorem select_wrong_head_is_rejected :
  forall label outcome endpoint successor context,
    fsem02Progression (FSEM02Select label) (End outcome)
      endpoint successor context = StepFailed.
Proof. reflexivity. Qed.

Theorem selected_branch_consumes_and_types_exact_successor :
  forall label branches endpoint successor context next continuation,
    offeredContinuation label branches = Some continuation ->
    fsem02Progression (FSEM02Select label) (Select branches)
      endpoint successor context = StepSucceeded next ->
    linearBindings next endpoint = None /\
    linearBindings next successor = Some (endpointType continuation).
Proof.
  intros label branches endpoint successor context next continuation Hlabel Hstep.
  assert (Hselected :
    selectedContinuation (FSEM02Select label) (Select branches) =
      Some (Some continuation)).
  { simpl. now rewrite Hlabel. }
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Select label) (Select branches)
    endpoint successor context next continuation
    Hselected Hstep) as Hresources.
  destruct Hresources as [_ [_ [Hgone [Hnext _]]]].
  split; assumption.
Qed.

Theorem wrong_terminal_outcome_rejects :
  forall expected actual endpoint successor context,
    String.eqb expected actual = false ->
    fsem02Progression (FSEM02Close actual) (End expected)
      endpoint successor context = StepFailed.
Proof.
  intros expected actual endpoint successor context Hmismatch.
  unfold fsem02Progression, selectedContinuation.
  rewrite Hmismatch.
  reflexivity.
Qed.

Theorem same_name_successor_rejects :
  forall action head endpoint context continuation,
    selectedContinuation action head = Some (Some continuation) ->
    fsem02Progression action head endpoint endpoint context = StepFailed.
Proof.
  intros action head endpoint context continuation Hselected.
  unfold fsem02Progression.
  rewrite Hselected.
  unfold continueEndpointResource.
  destruct (consumeLinear endpoint context) as [error | ty after] eqn:Hconsume.
  - reflexivity.
  - rewrite String.eqb_refl. reflexivity.
Qed.

Theorem stale_linear_predecessor_cannot_succeed :
  forall action head endpoint successor context next,
    linearBindings context endpoint = None ->
    fsem02Progression action head endpoint successor context <>
      StepSucceeded next.
Proof.
  intros action head endpoint successor context next Hmissing Hsuccess.
  unfold fsem02Progression in Hsuccess.
  destruct (selectedContinuation action head)
    as [[continuation |] |] eqn:Hselected.
  - unfold continueEndpointResource, consumeLinear in Hsuccess.
    destruct (sharedLoans context endpoint); try discriminate.
    rewrite Hmissing in Hsuccess. discriminate.
  - unfold closeEndpointResource, consumeLinear in Hsuccess.
    destruct (sharedLoans context endpoint); try discriminate.
    rewrite Hmissing in Hsuccess. discriminate.
  - discriminate.
Qed.

(*
  This is a CONDITIONAL composition of two independent models:
  successful local endpoint consumption and an already-admitted restricted
  rendezvous in ConcurrencySemantics. It does not derive RendezvousValid from
  matching Haskell send/receive calls, nor prove transfer of every other key.
*)
Theorem admitted_restricted_rendezvous_and_local_step :
  forall action head endpoint successor context next continuation
         admitted ownershipBefore ownershipAfter rendezvous subject,
    selectedContinuation action head = Some (Some continuation) ->
    fsem02Progression action head endpoint successor context =
      StepSucceeded next ->
    RendezvousValid admitted ownershipBefore ownershipAfter rendezvous ->
    rendezvousRestrictedSubject rendezvous = Some subject ->
    linearBindings next endpoint = None /\
    ownershipBefore subject = Some (rendezvousSenderProcess rendezvous) /\
    ownershipAfter subject = Some (rendezvousReceiverProcess rendezvous).
Proof.
  intros action head endpoint successor context next continuation
    admitted ownershipBefore ownershipAfter rendezvous subject
    Hselected Hstep Hrendezvous Hrestricted.
  pose proof
    (continuing_head_exact_predecessor_and_successor
      action head endpoint successor context next continuation
      Hselected Hstep) as Hresource.
  destruct Hresource as [_ [_ [Hgone _]]].
  pose proof
    (restricted_rendezvous_transfers_exact_owner
      admitted ownershipBefore ownershipAfter rendezvous subject
      Hrendezvous Hrestricted) as [Hbefore Hafter].
  repeat split; assumption.
Qed.
