From Stdlib Require Import Strings.String.
From Phil.Core Require Import Context SessionStep FSEM02ProtocolHeadProgression.

(*
  FSEM-02 NON-NORMATIVE. A fresh continuation cannot take an already
  occupied unrestricted, affine or linear occurrence, including an unrelated
  spectator or borrowed affine owner. This is a finite resource-model
  rejection lemma, not a claim that a native Core state refines this carrier.
  Head selection and protocol authority are externally provided premises.
*)

Theorem fsem02OccupiedSuccessorCannotSucceed :
  forall action head predecessor successor context continuation next,
    selectedContinuation action head = Some (Some continuation) ->
    String.eqb successor predecessor = false ->
    (unrestrictedBindings context successor <> None \/
     affineBindings context successor <> None \/
     linearBindings context successor <> None) ->
    fsem02Progression action head predecessor successor context <>
      StepSucceeded next.
Proof.
  intros action head predecessor successor context continuation next
    Hhead Hdistinct Hoccupied Hsuccess.
  unfold fsem02Progression in Hsuccess.
  rewrite Hhead in Hsuccess.
  unfold continueEndpointResource in Hsuccess.
  destruct (consumeLinear predecessor context) as
    [consumeError | consumedTy consumed] eqn:Hconsume.
  - discriminate.
  - destruct (String.eqb predecessor successor) eqn:Hsame.
    + discriminate.
    + destruct (insertBinding Linear successor (endpointType continuation) consumed)
        as [insertError | continued] eqn:Hinsert.
      * discriminate.
      * pose proof (consumeLinear_success_exact
          predecessor context consumed consumedTy Hconsume)
          as [_ [_ [Hother [HU [HA _]]]]].
        pose proof (insertBinding_success_exact
          Linear successor (endpointType continuation) consumed continued Hinsert)
          as [HsuccU [HsuccA [HsuccL _]]].
        specialize (Hother successor Hdistinct).
        rewrite HU in HsuccU.
        rewrite HA in HsuccA.
        rewrite Hother in HsuccL.
        destruct Hoccupied as [Hoccupied | [Hoccupied | Hoccupied]].
        -- apply Hoccupied. exact HsuccU.
        -- apply Hoccupied. exact HsuccA.
        -- apply Hoccupied. exact HsuccL.
Qed.

Theorem fsem02OccupiedSuccessorRefusesWithoutNewContext :
  forall action head predecessor successor context continuation,
    selectedContinuation action head = Some (Some continuation) ->
    String.eqb successor predecessor = false ->
    (unrestrictedBindings context successor <> None \/
     affineBindings context successor <> None \/
     linearBindings context successor <> None) ->
    fsem02Progression action head predecessor successor context = StepFailed.
Proof.
  intros action head predecessor successor context continuation
    Hhead Hdistinct Hoccupied.
  destruct (fsem02Progression action head predecessor successor context)
    as [|next] eqn:Hstep.
  - reflexivity.
  - exfalso.
    eapply fsem02OccupiedSuccessorCannotSucceed; eauto.
Qed.
