From Phil.Core Require Import Syntax Context SessionStep
  FSEM02ProtocolHeadProgression FSEM02PingJointCloseDiamond
  FSEM02PingCloseRefusalRetry.

(* FSEM-02 non-normative. Both trials must refuse. A committed first
   action is excluded: these models do not roll back earlier commits. *)
Definition fsem02PingRefusedClientThenServer
  (clientAllowed serverAllowed : bool)
  (clientOutcome serverOutcome : Outcome)
  (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02PingTryClientClose clientAllowed clientOutcome clientHead
          clientEndpoint clientBefore serverBefore with
  | FSEM02PingCloseCommitted _ _ => None
  | FSEM02PingCloseRefused clientOne serverOne =>
      match fsem02PingTryServerClose serverAllowed serverOutcome serverHead
              serverEndpoint clientOne serverOne with
      | FSEM02PingCloseCommitted _ _ => None
      | FSEM02PingCloseRefused clientTwo serverTwo => Some (clientTwo, serverTwo)
      end
  end.

Definition fsem02PingRefusedServerThenClient
  (clientAllowed serverAllowed : bool)
  (clientOutcome serverOutcome : Outcome)
  (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02PingTryServerClose serverAllowed serverOutcome serverHead
          serverEndpoint clientBefore serverBefore with
  | FSEM02PingCloseCommitted _ _ => None
  | FSEM02PingCloseRefused clientOne serverOne =>
      match fsem02PingTryClientClose clientAllowed clientOutcome clientHead
              clientEndpoint clientOne serverOne with
      | FSEM02PingCloseCommitted _ _ => None
      | FSEM02PingCloseRefused clientTwo serverTwo => Some (clientTwo, serverTwo)
      end
  end.

Theorem fsem02PingDoubleNominalRefusalPreservesBoth :
  forall a b ch sh ce se cb sb,
    fsem02PingRefusedClientThenServer false false a b ch sh ce se cb sb =
      Some (cb, sb).
Proof. reflexivity. Qed.

Theorem fsem02PingReversedNominalRefusalPreservesBoth :
  forall a b ch sh ce se cb sb,
    fsem02PingRefusedServerThenClient false false a b ch sh ce se cb sb =
      Some (cb, sb).
Proof. reflexivity. Qed.

Theorem fsem02PingDoubleHeadRefusalPreservesBoth :
  forall a b ch sh ce se cb sb,
    fsem02Progression (FSEM02Close a) ch ce ce cb = StepFailed ->
    fsem02Progression (FSEM02Close b) sh se se sb = StepFailed ->
    fsem02PingRefusedClientThenServer true true a b ch sh ce se cb sb =
      Some (cb, sb).
Proof.
  intros a b ch sh ce se cb sb Hc Hs.
  unfold fsem02PingRefusedClientThenServer,
    fsem02PingTryClientClose, fsem02PingTryServerClose.
  now rewrite Hc, Hs.
Qed.

Theorem fsem02PingReverseHeadRefusalPreservesBoth :
  forall a b ch sh ce se cb sb,
    fsem02Progression (FSEM02Close a) ch ce ce cb = StepFailed ->
    fsem02Progression (FSEM02Close b) sh se se sb = StepFailed ->
    fsem02PingRefusedServerThenClient true true a b ch sh ce se cb sb =
      Some (cb, sb).
Proof.
  intros a b ch sh ce se cb sb Hc Hs.
  unfold fsem02PingRefusedServerThenClient,
    fsem02PingTryClientClose, fsem02PingTryServerClose.
  now rewrite Hs, Hc.
Qed.

Theorem fsem02PingDoubleRefusalCannotHideClientCommit :
  forall clientAllowed serverAllowed a b ch sh ce se cb sb ca sa,
    fsem02PingTryClientClose clientAllowed a ch ce cb sb =
      FSEM02PingCloseCommitted ca sa ->
    fsem02PingRefusedClientThenServer clientAllowed serverAllowed
      a b ch sh ce se cb sb = None.
Proof.
  intros clientAllowed serverAllowed a b ch sh ce se cb sb ca sa Hcommit.
  unfold fsem02PingRefusedClientThenServer.
  now rewrite Hcommit.
Qed.

Definition fsem02PingDoubleRefusalRetry
  (clientBad serverBad good : Outcome)
  (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02PingRefusedClientThenServer false false
          clientBad serverBad clientHead serverHead
          clientEndpoint serverEndpoint clientBefore serverBefore with
  | None => None
  | Some (clientOriginal, serverOriginal) =>
      fsem02PingClientThenServerClose good clientHead serverHead
        clientEndpoint serverEndpoint clientOriginal serverOriginal
  end.

Theorem fsem02PingDoubleRefusalRetryIsDirect :
  forall a b good ch sh ce se cb sb,
    fsem02PingDoubleRefusalRetry a b good ch sh ce se cb sb =
    fsem02PingClientThenServerClose good ch sh ce se cb sb.
Proof. reflexivity. Qed.

Theorem fsem02PingDoubleRefusalRetryCommutes :
  forall a b good ch sh ce se cb sb,
    fsem02PingDoubleRefusalRetry a b good ch sh ce se cb sb =
    fsem02PingServerThenClientClose good ch sh ce se cb sb.
Proof.
  intros.
  rewrite fsem02PingDoubleRefusalRetryIsDirect.
  apply fsem02PingJointTerminalCloseDiamond.
Qed.
