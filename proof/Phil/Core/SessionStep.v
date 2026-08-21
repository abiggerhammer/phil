From Stdlib Require Import Strings.String.

From Phil.Core Require Import Syntax Context.

(*
  Resource-effect model for the common successful paths in Phil.Core.Session.

  The Haskell send/receive/select/offer operations all consume the current
  linear endpoint and then call continueWith, which rejects endpoint-name reuse
  and inserts a fresh linear successor carrying the continuation session. Close
  consumes the endpoint and installs no successor.

  Session/action matching and the concrete TyEndpoint constructor are outside
  this resource theorem. [endpointType] is the proof-side token for the endpoint
  type carrying a continuation; the theorem never inspects that type.
*)

Parameter endpointType : Session -> Ty.

Inductive ResourceStepResult : Type :=
| StepFailed : ResourceStepResult
| StepSucceeded : ResourceContext -> ResourceStepResult.

Definition continueEndpointResource
  (endpoint successor : Name)
  (continuation : Session)
  (context : ResourceContext) : ResourceStepResult :=
  match consumeLinear endpoint context with
  | ConsumeError _ => StepFailed
  | Consumed _ consumed =>
      if String.eqb endpoint successor then
        StepFailed
      else
        match insertBinding Linear successor (endpointType continuation) consumed with
        | InsertError _ => StepFailed
        | Inserted continued => StepSucceeded continued
        end
  end.

Definition closeEndpointResource
  (endpoint : Name)
  (context : ResourceContext) : ResourceStepResult :=
  match consumeLinear endpoint context with
  | ConsumeError _ => StepFailed
  | Consumed _ consumed => StepSucceeded consumed
  end.

(*
  PHIL-SESSION-STEP-001, non-close case.

  Successful continuation consumes the old linear endpoint, installs the
  continuation under a distinct fresh successor, preserves every unrelated
  linear lookup, and leaves the active-loan set unchanged.
*)
Theorem continueEndpointResource_success_exact :
  forall (endpoint successor : Name)
         (continuation : Session)
         (context next : ResourceContext),
    continueEndpointResource endpoint successor continuation context =
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
  intros endpoint successor continuation context next Hstep.
  unfold continueEndpointResource in Hstep.
  destruct (consumeLinear endpoint context) as [consumeError | consumedTy consumed]
    eqn:Hconsume.
  - discriminate.
  - destruct (String.eqb endpoint successor) eqn:Hdistinct.
    + discriminate.
    + destruct
        (insertBinding Linear successor (endpointType continuation) consumed)
        as [insertError | continued] eqn:Hinsert.
      * discriminate.
      * inversion Hstep; subst next; clear Hstep.
        pose proof
          (consumeLinear_success_exact
            endpoint context consumed consumedTy Hconsume)
          as HconsumeExact.
        pose proof
          (insertBinding_success_exact
            Linear successor (endpointType continuation)
            consumed continued Hinsert)
          as HinsertExact.
        destruct HconsumeExact as
          [Howned [HendpointGone [HconsumeOther [HU [HA HconsumeLoans]]]]].
        destruct HinsertExact as
          [HsuccU [HsuccA [HsuccL [Hselected [HinsertOther HinsertLoans]]]]].
        simpl in Hselected.
        destruct Hselected as [HnextU [HnextA HsuccessorInstalled]].
        pose proof (HinsertOther endpoint Hdistinct) as HendpointPreserved.
        destruct HendpointPreserved as
          [HendpointU [HendpointA HendpointLinearPreserved]].
        split.
        -- reflexivity.
        -- split.
           ++ exists consumedTy. exact Howned.
           ++ split.
              ** rewrite HendpointLinearPreserved. exact HendpointGone.
              ** split.
                 --- exact HsuccessorInstalled.
                 --- split.
                     +++ intros other HotherEndpoint HotherSuccessor.
                         pose proof (HconsumeOther other HotherEndpoint)
                           as HconsumePreserved.
                         pose proof (HinsertOther other HotherSuccessor)
                           as HinsertPreserved.
                         destruct HinsertPreserved as
                           [HotherU [HotherA HinsertLinearPreserved]].
                         rewrite HinsertLinearPreserved.
                         exact HconsumePreserved.
                     +++ rewrite HinsertLoans. exact HconsumeLoans.
Qed.

(*
  PHIL-SESSION-STEP-001, close case.

  Successful close consumes the old endpoint, installs no successor, preserves
  every other linear lookup, and leaves the active-loan set unchanged.
*)
Theorem closeEndpointResource_success_exact :
  forall (endpoint : Name) (context next : ResourceContext),
    closeEndpointResource endpoint context = StepSucceeded next ->
    (exists endpointTy : Ty,
      linearBindings context endpoint = Some endpointTy) /\
    linearBindings next endpoint = None /\
    (forall other : Name,
      String.eqb other endpoint = false ->
      linearBindings next other = linearBindings context other) /\
    sharedLoans next = sharedLoans context.
Proof.
  intros endpoint context next Hstep.
  unfold closeEndpointResource in Hstep.
  destruct (consumeLinear endpoint context) as [consumeError | consumedTy consumed]
    eqn:Hconsume.
  - discriminate.
  - inversion Hstep; subst next; clear Hstep.
    pose proof
      (consumeLinear_success_exact endpoint context consumed consumedTy Hconsume)
      as HconsumeExact.
    destruct HconsumeExact as
      [Howned [HendpointGone [Hother [HU [HA Hloans]]]]].
    split.
    + exists consumedTy. exact Howned.
    + split.
      * exact HendpointGone.
      * split.
        -- exact Hother.
        -- exact Hloans.
Qed.
