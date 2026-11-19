From Stdlib Require Import Lists.List Bool.Bool.
(* Bounded, NON-NORMATIVE FSEM-02 observation alphabet.
   This finite alphabet alone does not authenticate the producer, exact
   binder identities or independently supplied protocol/root authority. *)
Inductive FSEM02ObservationTag :=
| FSEM02TransferCommitted
| FSEM02SenderCloseRefused
| FSEM02ReceiverCloseRefused
| FSEM02StaleReplayRefused.

Definition fsem02ObservationCommitted (tag : FSEM02ObservationTag) : bool :=
  match tag with
  | FSEM02TransferCommitted => true
  | _ => false
  end.
Definition fsem02ObservationRefused (tag : FSEM02ObservationTag) : bool :=
  negb (fsem02ObservationCommitted tag).
