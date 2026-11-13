From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose.

(* FSEM-02 NON-NORMATIVE: population and activation status are EXTERNAL.
   This models their precedence over owner retirement only. The native
   intermediate context and nominal checks, source-architecture validity,
   deactivation, and universal implementation refinement are NOT modeled. *)
Inductive FSEM02ActivationCloseResult : Type :=
| FSEM02UnknownProcess
| FSEM02InactiveProcess
| FSEM02OwnerRefused
| FSEM02ClosedOwner (owners : FSEM02OwnerLedger).

Definition fsem02CloseWithPopulation
  (population : string -> option bool)
  (owners : FSEM02OwnerLedger)
  (occurrence process : string) (endpoint : Name)
  : FSEM02ActivationCloseResult :=
  match population process with
  | None => FSEM02UnknownProcess
  | Some false => FSEM02InactiveProcess
  | Some true =>
      match fsem02RetireSelectedClientOwner
        owners occurrence process endpoint with
      | None => FSEM02OwnerRefused
      | Some after => FSEM02ClosedOwner after
      end
  end.

Theorem fsem02CloseUnknownProcessBeforeOwnerOrNominal :
  forall population owners occurrence process endpoint,
    population process = None ->
    fsem02CloseWithPopulation population owners
      occurrence process endpoint = FSEM02UnknownProcess.
Proof.
  intros population owners occurrence process endpoint Hunknown.
  unfold fsem02CloseWithPopulation.
  now rewrite Hunknown.
Qed.

Theorem fsem02CloseInactiveProcessBeforeOwnerOrNominal :
  forall population owners occurrence process endpoint,
    population process = Some false ->
    fsem02CloseWithPopulation population owners
      occurrence process endpoint = FSEM02InactiveProcess.
Proof.
  intros population owners occurrence process endpoint Hinactive.
  unfold fsem02CloseWithPopulation.
  now rewrite Hinactive.
Qed.

Theorem fsem02CloseAllowedRequiresActiveExactOwnerAndFrames :
  forall population owners occurrence process endpoint after,
    fsem02CloseWithPopulation population owners
      occurrence process endpoint = FSEM02ClosedOwner after ->
    population process = Some true /\
    owners occurrence = Some (process, endpoint) /\
    after occurrence = None /\
    (forall spectator, spectator <> occurrence ->
      after spectator = owners spectator).
Proof.
  intros population owners occurrence process endpoint after Hstep.
  unfold fsem02CloseWithPopulation in Hstep.
  destruct (population process) as [[|]|] eqn:Hpop;
    try discriminate.
  destruct (fsem02RetireSelectedClientOwner
    owners occurrence process endpoint) as [result|] eqn:Hretire;
    try discriminate.
  inversion Hstep; subst result.
  pose proof (fsem02SelectedClientCloseRequiresExactOwner
    owners occurrence process endpoint after Hretire) as Howner.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners occurrence process endpoint after Hretire)
    as [Habsent Hframe].
  repeat split; assumption.
Qed.

(* Source-choice success does NOT establish any external activation grant. *)
Theorem fsem02SourceChoiceEndsRemainPopulationGated :
  forall labels branches chosen peer clientOld clientNext peerOld peerNext
         clientContext peerContext owners co po cp pp cr pr ready population,
    fsem02StatefulSourceChoice labels branches chosen peer
      clientOld clientNext peerOld peerNext clientContext peerContext
      owners co po cp pp = Some ((cr, pr), ready) ->
    population cp = None ->
    population pp = Some false ->
    fsem02CloseWithPopulation population ready co cp clientNext =
      FSEM02UnknownProcess /\
    fsem02CloseWithPopulation population ready po pp peerNext =
      FSEM02InactiveProcess /\
    ready co = Some (cp, clientNext) /\
    ready po = Some (pp, peerNext) /\
    (forall spectator, spectator <> co -> spectator <> po ->
      ready spectator = owners spectator).
Proof.
  intros labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready population
    Hchoice Hmissing Hinactive.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready Hchoice)
    as [_ [Hclient [Hpeer Hframe]]].
  repeat split.
  - apply fsem02CloseUnknownProcessBeforeOwnerOrNominal. exact Hmissing.
  - apply fsem02CloseInactiveProcessBeforeOwnerOrNominal. exact Hinactive.
  - exact Hclient.
  - exact Hpeer.
  - exact Hframe.
Qed.
