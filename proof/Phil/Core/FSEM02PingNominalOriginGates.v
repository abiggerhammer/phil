From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression.

(* NON-NORMATIVE FSEM-02. Nominal protocol identity and role are external
   verified inputs, never derived from equal local Send/Receive Session heads.
   This is a conditional resource model, not Haskell implementation refinement. *)
Open Scope string_scope.

Definition fsem02NominalPingGate
  (expectedInstance liveInstance expectedRole liveRole : string)
  (action : FSEM02Action) (head : Session)
  (endpoint successor : Name) (context : ResourceContext)
  : ResourceStepResult :=
  if String.eqb expectedInstance liveInstance then
    if String.eqb expectedRole liveRole then
      fsem02Progression action head endpoint successor context
    else StepFailed
  else StepFailed.

Theorem fsem02PingWrongInstanceCannotAdvance :
  forall expectedInstance liveInstance expectedRole liveRole
         action head endpoint successor context,
    String.eqb expectedInstance liveInstance = false ->
    fsem02NominalPingGate expectedInstance liveInstance
      expectedRole liveRole action head endpoint successor context = StepFailed.
Proof.
  intros expectedInstance liveInstance expectedRole liveRole
    action head endpoint successor context Hwrong.
  unfold fsem02NominalPingGate.
  now rewrite Hwrong.
Qed.

Theorem fsem02PingWrongRoleCannotAdvance :
  forall expectedInstance liveInstance expectedRole liveRole
         action head endpoint successor context,
    String.eqb expectedInstance liveInstance = true ->
    String.eqb expectedRole liveRole = false ->
    fsem02NominalPingGate expectedInstance liveInstance
      expectedRole liveRole action head endpoint successor context = StepFailed.
Proof.
  intros expectedInstance liveInstance expectedRole liveRole
    action head endpoint successor context Hinstance Hrole.
  unfold fsem02NominalPingGate.
  now rewrite Hinstance, Hrole.
Qed.

Theorem fsem02PingMatchingNominalIdentityDelegates :
  forall instance role action head endpoint successor context,
    fsem02NominalPingGate instance instance role role
      action head endpoint successor context =
    fsem02Progression action head endpoint successor context.
Proof.
  intros instance role action head endpoint successor context.
  unfold fsem02NominalPingGate.
  now rewrite !String.eqb_refl.
Qed.

Theorem fsem02PingMatchingSendConsumesExactPredecessor :
  forall instance role binder ty continuation endpoint successor context next,
    fsem02NominalPingGate instance instance role role FSEM02Send
      (Send binder ty continuation) endpoint successor context =
      StepSucceeded next ->
    linearBindings next endpoint = None /\
    linearBindings next successor = Some (endpointType continuation).
Proof.
  intros instance role binder ty continuation endpoint successor context next Hstep.
  rewrite fsem02PingMatchingNominalIdentityDelegates in Hstep.
  pose proof (continuing_head_exact_predecessor_and_successor
    FSEM02Send (Send binder ty continuation) endpoint successor
    context next continuation eq_refl Hstep) as [_ [_ [Hgone [Hnext _]]]].
  split; assumption.
Qed.

Theorem fsem02PingMatchingReceiveConsumesExactPredecessor :
  forall instance role binder ty continuation endpoint successor context next,
    fsem02NominalPingGate instance instance role role FSEM02Receive
      (Receive binder ty continuation) endpoint successor context =
      StepSucceeded next ->
    linearBindings next endpoint = None /\
    linearBindings next successor = Some (endpointType continuation).
Proof.
  intros instance role binder ty continuation endpoint successor context next Hstep.
  rewrite fsem02PingMatchingNominalIdentityDelegates in Hstep.
  pose proof (continuing_head_exact_predecessor_and_successor
    FSEM02Receive (Receive binder ty continuation) endpoint successor
    context next continuation eq_refl Hstep) as [_ [_ [Hgone [Hnext _]]]].
  split; assumption.
Qed.

Theorem fsem02PingWrongInstanceCannotProduceSuccess :
  forall expectedInstance liveInstance expectedRole liveRole
         action head endpoint successor context next,
    String.eqb expectedInstance liveInstance = false ->
    fsem02NominalPingGate expectedInstance liveInstance
      expectedRole liveRole action head endpoint successor context <>
      StepSucceeded next.
Proof.
  intros expectedInstance liveInstance expectedRole liveRole
    action head endpoint successor context next Hwrong Hsuccess.
  rewrite (fsem02PingWrongInstanceCannotAdvance
    expectedInstance liveInstance expectedRole liveRole
    action head endpoint successor context Hwrong) in Hsuccess.
  discriminate.
Qed.
