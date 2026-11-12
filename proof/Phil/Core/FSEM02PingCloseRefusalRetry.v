From Phil.Core Require Import Syntax Context SessionStep
  FSEM02ProtocolHeadProgression FSEM02PingJointCloseDiamond.

(* FSEM-02, non-normative. Independent nominal admission is an explicit
   Boolean input, not inferred from the source protocol's spelling.
   Refusal retains BOTH original process resource contexts. The Haskell
   conformance driver checks native diagnostic classes independently. *)

Inductive FSEM02PingCloseAttempt : Type :=
| FSEM02PingCloseRefused : ResourceContext -> ResourceContext -> FSEM02PingCloseAttempt
| FSEM02PingCloseCommitted : ResourceContext -> ResourceContext -> FSEM02PingCloseAttempt.

Definition fsem02PingTryClientClose
  (nominalAllowed : bool) (outcome : Outcome) (clientHead : Session)
  (clientEndpoint : Name) (clientBefore serverBefore : ResourceContext)
  : FSEM02PingCloseAttempt :=
  if nominalAllowed then
    match fsem02Progression (FSEM02Close outcome) clientHead
            clientEndpoint clientEndpoint clientBefore with
    | StepFailed => FSEM02PingCloseRefused clientBefore serverBefore
    | StepSucceeded clientAfter =>
        FSEM02PingCloseCommitted clientAfter serverBefore
    end
  else FSEM02PingCloseRefused clientBefore serverBefore.

Definition fsem02PingTryServerClose
  (nominalAllowed : bool) (outcome : Outcome) (serverHead : Session)
  (serverEndpoint : Name) (clientBefore serverBefore : ResourceContext)
  : FSEM02PingCloseAttempt :=
  if nominalAllowed then
    match fsem02Progression (FSEM02Close outcome) serverHead
            serverEndpoint serverEndpoint serverBefore with
    | StepFailed => FSEM02PingCloseRefused clientBefore serverBefore
    | StepSucceeded serverAfter =>
        FSEM02PingCloseCommitted clientBefore serverAfter
    end
  else FSEM02PingCloseRefused clientBefore serverBefore.

Theorem fsem02PingClientNominalRefusalPreservesBoth :
  forall outcome clientHead clientEndpoint clientBefore serverBefore,
    fsem02PingTryClientClose false outcome clientHead clientEndpoint
      clientBefore serverBefore =
    FSEM02PingCloseRefused clientBefore serverBefore.
Proof. reflexivity. Qed.

Theorem fsem02PingServerNominalRefusalPreservesBoth :
  forall outcome serverHead serverEndpoint clientBefore serverBefore,
    fsem02PingTryServerClose false outcome serverHead serverEndpoint
      clientBefore serverBefore =
    FSEM02PingCloseRefused clientBefore serverBefore.
Proof. reflexivity. Qed.

Theorem fsem02PingClientHeadRefusalPreservesBoth :
  forall outcome clientHead clientEndpoint clientBefore serverBefore,
    fsem02Progression (FSEM02Close outcome) clientHead
      clientEndpoint clientEndpoint clientBefore = StepFailed ->
    fsem02PingTryClientClose true outcome clientHead clientEndpoint
      clientBefore serverBefore =
    FSEM02PingCloseRefused clientBefore serverBefore.
Proof.
  intros outcome clientHead clientEndpoint clientBefore serverBefore Hfailed.
  unfold fsem02PingTryClientClose.
  now rewrite Hfailed.
Qed.

Theorem fsem02PingServerHeadRefusalPreservesBoth :
  forall outcome serverHead serverEndpoint clientBefore serverBefore,
    fsem02Progression (FSEM02Close outcome) serverHead
      serverEndpoint serverEndpoint serverBefore = StepFailed ->
    fsem02PingTryServerClose true outcome serverHead serverEndpoint
      clientBefore serverBefore =
    FSEM02PingCloseRefused clientBefore serverBefore.
Proof.
  intros outcome serverHead serverEndpoint clientBefore serverBefore Hfailed.
  unfold fsem02PingTryServerClose.
  now rewrite Hfailed.
Qed.

Theorem fsem02PingClientSuccessFramesPeer :
  forall outcome clientHead clientEndpoint clientBefore serverBefore clientAfter,
    fsem02PingTryClientClose true outcome clientHead clientEndpoint
      clientBefore serverBefore =
      FSEM02PingCloseCommitted clientAfter serverBefore ->
    fsem02Progression (FSEM02Close outcome) clientHead
      clientEndpoint clientEndpoint clientBefore =
      StepSucceeded clientAfter.
Proof.
  intros outcome clientHead clientEndpoint clientBefore serverBefore clientAfter Hstep.
  unfold fsem02PingTryClientClose in Hstep.
  destruct (fsem02Progression (FSEM02Close outcome) clientHead
    clientEndpoint clientEndpoint clientBefore) as [|actual] eqn:Hactual;
    try discriminate.
  inversion Hstep; subst; reflexivity.
Qed.

Theorem fsem02PingServerSuccessFramesPeer :
  forall outcome serverHead serverEndpoint clientBefore serverBefore serverAfter,
    fsem02PingTryServerClose true outcome serverHead serverEndpoint
      clientBefore serverBefore =
      FSEM02PingCloseCommitted clientBefore serverAfter ->
    fsem02Progression (FSEM02Close outcome) serverHead
      serverEndpoint serverEndpoint serverBefore =
      StepSucceeded serverAfter.
Proof.
  intros outcome serverHead serverEndpoint clientBefore serverBefore serverAfter Hstep.
  unfold fsem02PingTryServerClose in Hstep.
  destruct (fsem02Progression (FSEM02Close outcome) serverHead
    serverEndpoint serverEndpoint serverBefore) as [|actual] eqn:Hactual;
    try discriminate.
  inversion Hstep; subst; reflexivity.
Qed.

Definition fsem02PingClientRetryAfterRefusal
  (nominalAllowed : bool) (badOutcome goodOutcome : Outcome)
  (clientHead serverHead : Session) (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02PingTryClientClose nominalAllowed badOutcome clientHead
          clientEndpoint clientBefore serverBefore with
  | FSEM02PingCloseRefused originalClient originalServer =>
      fsem02PingClientThenServerClose goodOutcome clientHead serverHead
        clientEndpoint serverEndpoint originalClient originalServer
  | FSEM02PingCloseCommitted _ _ => None
  end.

Theorem fsem02PingClientRejectedTrialRetryIsDirect :
  forall badOutcome goodOutcome clientHead serverHead
         clientEndpoint serverEndpoint clientBefore serverBefore,
    fsem02PingClientRetryAfterRefusal false badOutcome goodOutcome
      clientHead serverHead clientEndpoint serverEndpoint
      clientBefore serverBefore =
    fsem02PingClientThenServerClose goodOutcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore.
Proof. reflexivity. Qed.

Theorem fsem02PingClientHeadRejectedTrialRetryIsDirect :
  forall badOutcome goodOutcome clientHead serverHead
         clientEndpoint serverEndpoint clientBefore serverBefore,
    fsem02Progression (FSEM02Close badOutcome) clientHead
      clientEndpoint clientEndpoint clientBefore = StepFailed ->
    fsem02PingClientRetryAfterRefusal true badOutcome goodOutcome
      clientHead serverHead clientEndpoint serverEndpoint
      clientBefore serverBefore =
    fsem02PingClientThenServerClose goodOutcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore.
Proof.
  intros badOutcome goodOutcome clientHead serverHead
    clientEndpoint serverEndpoint clientBefore serverBefore Hfailed.
  unfold fsem02PingClientRetryAfterRefusal, fsem02PingTryClientClose.
  now rewrite Hfailed.
Qed.

Theorem fsem02PingClientRejectedTrialRetryCommutes :
  forall badOutcome goodOutcome clientHead serverHead
         clientEndpoint serverEndpoint clientBefore serverBefore,
    fsem02PingClientRetryAfterRefusal false badOutcome goodOutcome
      clientHead serverHead clientEndpoint serverEndpoint
      clientBefore serverBefore =
    fsem02PingServerThenClientClose goodOutcome clientHead serverHead
      clientEndpoint serverEndpoint clientBefore serverBefore.
Proof.
  intros.
  rewrite fsem02PingClientRejectedTrialRetryIsDirect.
  apply fsem02PingJointTerminalCloseDiamond.
Qed.
