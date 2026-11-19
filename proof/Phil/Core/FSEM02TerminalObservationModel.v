From Stdlib Require Import Lists.List Bool.Bool.
(* Bounded, NON-NORMATIVE terminal observation. These tags by themselves
   do not authorize an instance, terminal outcome, selected root or disposal. *)
Inductive FSEM02TerminalObservationTag :=
| FSEM02WrongTerminalOutcomeRefused
| FSEM02TerminalClosed
| FSEM02TerminalReplayRefused.

Definition fsem02TerminalCommitted (tag : FSEM02TerminalObservationTag) : bool :=
  match tag with
  | FSEM02TerminalClosed => true
  | _ => false
  end.
Definition fsem02TerminalRefused (tag : FSEM02TerminalObservationTag) : bool :=
  negb (fsem02TerminalCommitted tag).
