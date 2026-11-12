From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression.

(* NON-NORMATIVE FSEM-02. Nominal protocol identity and role equality are
   inputs from the separately checked production protocol registry, NEVER
   inferred from equal local session heads or source syntax. This gate is
   an abstract finite model, not Haskell implementation refinement. *)
Open Scope string_scope.

Definition fsem02NominalOfferGate
  (expectedInstance liveInstance expectedRole liveRole : string)
  (label : string) (branches : Branches)
  (endpoint successor : Name) (context : ResourceContext)
  : ResourceStepResult :=
  if String.eqb expectedInstance liveInstance then
    if String.eqb expectedRole liveRole then
      fsem02Progression (FSEM02Offer label) (Offer branches)
        endpoint successor context
    else StepFailed
  else StepFailed.

Theorem fsem02WrongNominalInstanceCannotAdvanceOffer :
  forall expectedInstance liveInstance expectedRole liveRole
         label branches endpoint successor context,
    String.eqb expectedInstance liveInstance = false ->
    fsem02NominalOfferGate expectedInstance liveInstance
      expectedRole liveRole label branches endpoint successor context
      = StepFailed.
Proof.
  intros expectedInstance liveInstance expectedRole liveRole
    label branches endpoint successor context Hwrong.
  unfold fsem02NominalOfferGate.
  now rewrite Hwrong.
Qed.

Theorem fsem02WrongNominalRoleCannotAdvanceOffer :
  forall expectedInstance liveInstance expectedRole liveRole
         label branches endpoint successor context,
    String.eqb expectedInstance liveInstance = true ->
    String.eqb expectedRole liveRole = false ->
    fsem02NominalOfferGate expectedInstance liveInstance
      expectedRole liveRole label branches endpoint successor context
      = StepFailed.
Proof.
  intros expectedInstance liveInstance expectedRole liveRole
    label branches endpoint successor context Hinstance Hrole.
  unfold fsem02NominalOfferGate.
  now rewrite Hinstance, Hrole.
Qed.

Theorem fsem02MatchingNominalGateDelegatesExactLocalOffer :
  forall instance role label branches endpoint successor context,
    fsem02NominalOfferGate instance instance role role
      label branches endpoint successor context =
    fsem02Progression (FSEM02Offer label) (Offer branches)
      endpoint successor context.
Proof.
  intros instance role label branches endpoint successor context.
  unfold fsem02NominalOfferGate.
  now rewrite !String.eqb_refl.
Qed.

Theorem fsem02WrongInstanceYieldsNoSuccessfulNextContext :
  forall expectedInstance liveInstance expectedRole liveRole
         label branches endpoint successor context next,
    String.eqb expectedInstance liveInstance = false ->
    fsem02NominalOfferGate expectedInstance liveInstance
      expectedRole liveRole label branches endpoint successor context
      <> StepSucceeded next.
Proof.
  intros expectedInstance liveInstance expectedRole liveRole
    label branches endpoint successor context next Hwrong Hnext.
  rewrite (fsem02WrongNominalInstanceCannotAdvanceOffer
    expectedInstance liveInstance expectedRole liveRole
    label branches endpoint successor context Hwrong) in Hnext.
  discriminate.
Qed.
