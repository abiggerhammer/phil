From Phil.Core Require Import Syntax Context SessionStep
  FSEM02ProtocolHeadProgression FSEM02PingJointAtomicity.

(* Non-normative FSEM-02: two distinct admitted process contexts after a
   source-checked Ping Send/Receive rendezvous. The End heads, nominal
   process grants, activation and disposal authority remain premises.
   No Haskell refinement or atomic simultaneous Close is inferred. *)

Definition fsem02PingClientThenServerClose
  (outcome : Outcome) (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02Progression (FSEM02Close outcome) clientHead
          clientEndpoint clientEndpoint clientBefore with
  | StepFailed => None
  | StepSucceeded clientAfter =>
      match fsem02Progression (FSEM02Close outcome) serverHead
              serverEndpoint serverEndpoint serverBefore with
      | StepFailed => None
      | StepSucceeded serverAfter => Some (clientAfter, serverAfter)
      end
  end.

Definition fsem02PingServerThenClientClose
  (outcome : Outcome) (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02Progression (FSEM02Close outcome) serverHead
          serverEndpoint serverEndpoint serverBefore with
  | StepFailed => None
  | StepSucceeded serverAfter =>
      match fsem02Progression (FSEM02Close outcome) clientHead
              clientEndpoint clientEndpoint clientBefore with
      | StepFailed => None
      | StepSucceeded clientAfter => Some (clientAfter, serverAfter)
      end
  end.

Theorem fsem02PingJointTerminalCloseDiamond :
  forall outcome clientHead serverHead clientEndpoint serverEndpoint
         clientBefore serverBefore,
    fsem02PingClientThenServerClose outcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore =
    fsem02PingServerThenClientClose outcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore.
Proof.
  intros outcome clientHead serverHead clientEndpoint serverEndpoint
    clientBefore serverBefore.
  unfold fsem02PingClientThenServerClose, fsem02PingServerThenClientClose.
  destruct (fsem02Progression (FSEM02Close outcome) clientHead
    clientEndpoint clientEndpoint clientBefore);
  destruct (fsem02Progression (FSEM02Close outcome) serverHead
    serverEndpoint serverEndpoint serverBefore); reflexivity.
Qed.

Theorem fsem02PingJointCloseRejectsFailedClient :
  forall outcome clientHead serverHead clientEndpoint serverEndpoint
         clientBefore serverBefore,
    fsem02Progression (FSEM02Close outcome) clientHead
      clientEndpoint clientEndpoint clientBefore = StepFailed ->
    fsem02PingClientThenServerClose outcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore = None.
Proof.
  intros outcome clientHead serverHead clientEndpoint serverEndpoint
    clientBefore serverBefore Hfailed.
  unfold fsem02PingClientThenServerClose.
  now rewrite Hfailed.
Qed.

Theorem fsem02PingJointCloseRejectsFailedServer :
  forall outcome clientHead serverHead clientEndpoint serverEndpoint
         clientBefore serverBefore,
    fsem02Progression (FSEM02Close outcome) serverHead
      serverEndpoint serverEndpoint serverBefore = StepFailed ->
    fsem02PingClientThenServerClose outcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore = None.
Proof.
  intros outcome clientHead serverHead clientEndpoint serverEndpoint
    clientBefore serverBefore Hfailed.
  unfold fsem02PingClientThenServerClose.
  destruct (fsem02Progression (FSEM02Close outcome) clientHead
    clientEndpoint clientEndpoint clientBefore).
  - reflexivity.
  - now rewrite Hfailed.
Qed.

Theorem fsem02PingJointCloseSuccessProjectsBoth :
  forall outcome clientHead serverHead clientEndpoint serverEndpoint
         clientBefore serverBefore clientAfter serverAfter,
    fsem02PingClientThenServerClose outcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore =
      Some (clientAfter, serverAfter) ->
    fsem02Progression (FSEM02Close outcome) clientHead
      clientEndpoint clientEndpoint clientBefore = StepSucceeded clientAfter /\
    fsem02Progression (FSEM02Close outcome) serverHead
      serverEndpoint serverEndpoint serverBefore = StepSucceeded serverAfter.
Proof.
  intros outcome clientHead serverHead clientEndpoint serverEndpoint
    clientBefore serverBefore clientAfter serverAfter Hpair.
  unfold fsem02PingClientThenServerClose in Hpair.
  destruct (fsem02Progression (FSEM02Close outcome) clientHead
    clientEndpoint clientEndpoint clientBefore) as [|actualClient] eqn:Hclient;
    try discriminate.
  destruct (fsem02Progression (FSEM02Close outcome) serverHead
    serverEndpoint serverEndpoint serverBefore) as [|actualServer] eqn:Hserver;
    try discriminate.
  inversion Hpair; subst.
  split; congruence.
Qed.
