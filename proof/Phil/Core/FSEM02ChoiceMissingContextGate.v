From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02ChoiceAmbiguousClose.
Import ListNotations.

(* Non-normative FSEM-02: these are explicit external gate observations,
   NOT derived activation, protocol-context, or nominal authority. The owner
   enumeration is an admitted finite key list, not a Map.toList theorem.
   An error constructor represents a refusal: it has no successor state. *)

Inductive FSEM02GatedEndResult : Type :=
| FSEM02ProcessUnknownGate
| FSEM02ProcessInactiveGate
| FSEM02MissingContextGate
| FSEM02UnknownOwnerGate
| FSEM02AmbiguousOwnerGate (keys : list string)
| FSEM02NominalRefusedGate
| FSEM02RetirementRefusedGate
| FSEM02ClosedGate (after : FSEM02OwnerLedger).

Definition fsem02GatedEnd
  (processPresent active contextPresent nominalGranted : bool)
  (owners : FSEM02OwnerLedger)
  (process : string) (endpoint : Name) (keys : list string)
  : FSEM02GatedEndResult :=
  if negb processPresent then FSEM02ProcessUnknownGate
  else if negb active then FSEM02ProcessInactiveGate
  else if negb contextPresent then FSEM02MissingContextGate
  else match filter (fsem02IsMatchingOwner owners process endpoint) keys with
       | [] => FSEM02UnknownOwnerGate
       | [key] =>
           if negb nominalGranted then FSEM02NominalRefusedGate
           else match fsem02RetireSelectedClientOwner owners key process endpoint with
                | None => FSEM02RetirementRefusedGate
                | Some after => FSEM02ClosedGate after
                end
       | first :: second :: rest =>
           FSEM02AmbiguousOwnerGate (first :: second :: rest)
       end.

Theorem fsem02UnknownProcessPrecedesAllOtherEndGates :
  forall active context nominal owners process endpoint keys,
    fsem02GatedEnd false active context nominal owners process endpoint keys =
      FSEM02ProcessUnknownGate.
Proof. reflexivity. Qed.

Theorem fsem02InactiveProcessPrecedesContextAndOwnerGates :
  forall context nominal owners process endpoint keys,
    fsem02GatedEnd true false context nominal owners process endpoint keys =
      FSEM02ProcessInactiveGate.
Proof. reflexivity. Qed.

Theorem fsem02MissingProtocolContextPrecedesOwnerAndNominalGates :
  forall nominal owners process endpoint keys,
    fsem02GatedEnd true true false nominal owners process endpoint keys =
      FSEM02MissingContextGate.
Proof. reflexivity. Qed.

Theorem fsem02MissingContextNeverRetiresAnyEndpoint :
  forall nominal owners process endpoint keys after,
    fsem02GatedEnd true true false nominal owners process endpoint keys <>
      FSEM02ClosedGate after.
Proof. intros; discriminate. Qed.

Theorem fsem02RestoredContextZeroOwnerRefusesExactly :
  forall nominal owners process endpoint keys,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [] ->
    fsem02GatedEnd true true true nominal owners process endpoint keys =
      FSEM02UnknownOwnerGate.
Proof.
  intros nominal owners process endpoint keys Hzero.
  unfold fsem02GatedEnd. simpl. now rewrite Hzero.
Qed.

Theorem fsem02RestoredContextAmbiguityPrecedesNominalGate :
  forall nominal owners process endpoint keys first second rest,
    filter (fsem02IsMatchingOwner owners process endpoint) keys =
      first :: second :: rest ->
    fsem02GatedEnd true true true nominal owners process endpoint keys =
      FSEM02AmbiguousOwnerGate (first :: second :: rest).
Proof.
  intros nominal owners process endpoint keys first second rest Hmultiple.
  unfold fsem02GatedEnd. simpl. now rewrite Hmultiple.
Qed.

Theorem fsem02RestoredUniqueOwnerStillNeedsNominalGrant :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02GatedEnd true true true false owners process endpoint keys =
      FSEM02NominalRefusedGate.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02GatedEnd. simpl. now rewrite Hone.
Qed.

Theorem fsem02RestoredUniqueGrantedOwnerRetiresOnlyIfRetirementSucceeds :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = Some after ->
    fsem02GatedEnd true true true true owners process endpoint keys =
      FSEM02ClosedGate after.
Proof.
  intros owners process endpoint keys key after Hone Hretire.
  unfold fsem02GatedEnd. simpl. now rewrite Hone, Hretire.
Qed.
