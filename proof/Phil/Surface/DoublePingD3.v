From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
Import ListNotations.

(* Conditional source reference model. Selection of the original packet and
   the correspondence of native certificates to the finite checks are
   premises of its use. This file does not encode or extract the Haskell
   producer or authorize a Close. *)

Record U8 := Byte { unsigned : nat; bounded : unsigned < 256 }.
Record Entries := EntryAssignment { first : U8; second : U8 }.
Inductive Cursor := First | Second | PreClose.
Inductive Binder := ClientFirst | ClientSecond | ServerFirst | ServerSecond.
Inductive generation := InitialEndpoint | MiddleEndpoint | DoneEndpoint.
Inductive EventKey := FirstRendezvous | SecondRendezvous.
Inductive Peer := Client | Server.

Inductive prefix :=
| S0
| S1 (received1 : U8)
| S2 (received1 received2 : U8).

Definition pcs (s : prefix) : Cursor * Cursor :=
  match s with
  | S0 => (First, First)
  | S1 _ => (Second, Second)
  | S2 _ _ => (PreClose, PreClose)
  end.

Definition endpoints (s : prefix) : generation * generation :=
  match s with
  | S0 => (InitialEndpoint, InitialEndpoint)
  | S1 _ => (MiddleEndpoint, MiddleEndpoint)
  | S2 _ _ => (DoneEndpoint, DoneEndpoint)
  end.

Definition value_at (entries : Entries) (s : prefix) (binder : Binder) : option U8 :=
  match binder with
  | ClientFirst => Some (first entries)
  | ClientSecond => Some (second entries)
  | ServerFirst => match s with S1 a | S2 a _ => Some a | S0 => None end
  | ServerSecond => match s with S2 _ b => Some b | _ => None end
  end.

(* Each boolean represents a checked fact, with the correspondence between
   these facts and actual native/source certificates outside the model. *)
Record gates := Gates
  { source_cursor_ok : bool; source_binders_ok : bool; destination_fresh : bool;
    activation_and_predecessor_ok : bool; native_transition_ok : bool;
    message_ok : bool; event_and_causality_ok : bool }.

Definition all_checked (g : gates) : bool :=
  source_cursor_ok g && source_binders_ok g && destination_fresh g &&
  activation_and_predecessor_ok g && native_transition_ok g &&
  message_ok g && event_and_causality_ok g.

Inductive commits (e : Entries) : prefix -> gates -> prefix -> Type :=
| CommitFirst g : all_checked g = true -> commits e S0 g (S1 (first e))
| CommitSecond g : all_checked g = true ->
    commits e (S1 (first e)) g (S2 (first e) (second e)).

Definition step_result (e : Entries) (s : prefix) (g : gates) : option prefix :=
  if all_checked g then
    match s with
    | S0 => Some (S1 (first e))
    | S1 a => if Nat.eqb (unsigned a) (unsigned (first e))
              then Some (S2 a (second e)) else None
    | S2 _ _ => None
    end
  else None.

Definition after (e : Entries) (s : prefix) (g : gates) : prefix :=
  match step_result e s g with Some successor => successor | None => s end.

Definition occurrence e s g t (c : commits e s g t) :
    EventKey * Binder * Binder * U8 :=
  match c with
  | CommitFirst _ _ _ => (FirstRendezvous, ClientFirst, ServerFirst, first e)
  | CommitSecond _ _ _ => (SecondRendezvous, ClientSecond, ServerSecond, second e)
  end.

Definition sequence_for (_ : Peer) e g1 g2
    (c1 : commits e S0 g1 (S1 (first e)))
    (c2 : commits e (S1 (first e)) g2 (S2 (first e) (second e))) :=
  [fst (fst (fst (occurrence _ _ _ _ c1))); fst (fst (fst (occurrence _ _ _ _ c2)))].

Theorem d3_failure_preserves_prefix :
  forall e s g, all_checked g = false -> after e s g = s.
Proof. intros e s g bad. unfold after, step_result. now rewrite bad. Qed.

Theorem d3_commit_is_exact :
  forall e s g t, commits e s g t -> step_result e s g = Some t.
Proof.
  intros e s g t checked. destruct checked as [g ok | g ok].
  - unfold step_result. now rewrite ok.
  - unfold step_result. now rewrite ok, Nat.eqb_refl.
Qed.

Theorem d3_initial_relation :
  forall e,
    pcs S0 = (First, First) /\
    endpoints S0 = (InitialEndpoint, InitialEndpoint) /\
    value_at e S0 ClientFirst = Some (first e) /\
    value_at e S0 ClientSecond = Some (second e) /\
    value_at e S0 ServerFirst = None /\ value_at e S0 ServerSecond = None.
Proof. intros. repeat split. Qed.

Theorem d3_two_steps_exact :
  forall e g1 g2 mid final,
    commits e S0 g1 mid ->
    commits e mid g2 final ->
    pcs mid = (Second, Second) /\ endpoints mid = (MiddleEndpoint, MiddleEndpoint) /\
    value_at e mid ServerFirst = Some (first e) /\ value_at e mid ServerSecond = None /\
    pcs final = (PreClose, PreClose) /\ endpoints final = (DoneEndpoint, DoneEndpoint) /\
    value_at e final ServerFirst = Some (first e) /\
    value_at e final ServerSecond = Some (second e).
Proof. intros e g1 g2 mid final c1 c2. inversion c1; subst. inversion c2; subst. repeat split. Qed.

Lemma occurrence_matches_predecessor :
  forall e s g t (c : commits e s g t),
    occurrence _ _ _ _ c =
      match s with
      | S0 => (FirstRendezvous, ClientFirst, ServerFirst, first e)
      | _ => (SecondRendezvous, ClientSecond, ServerSecond, second e)
      end.
Proof. intros e s g t c. destruct c; reflexivity. Qed.

Theorem d3_occurrences_and_order :
  forall e g1 g2
    (c1 : commits e S0 g1 (S1 (first e)))
    (c2 : commits e (S1 (first e)) g2 (S2 (first e) (second e))),
    occurrence _ _ _ _ c1 = (FirstRendezvous, ClientFirst, ServerFirst, first e) /\
    occurrence _ _ _ _ c2 = (SecondRendezvous, ClientSecond, ServerSecond, second e) /\
    FirstRendezvous <> SecondRendezvous /\
    sequence_for Client e g1 g2 c1 c2 = [FirstRendezvous; SecondRendezvous] /\
    sequence_for Server e g1 g2 c1 c2 = [FirstRendezvous; SecondRendezvous].
Proof.
  intros e g1 g2 c1 c2.
  unfold sequence_for.
  rewrite (occurrence_matches_predecessor _ _ _ _ c1).
  rewrite (occurrence_matches_predecessor _ _ _ _ c2).
  repeat split. intros impossible. discriminate impossible.
Qed.

Theorem d3_preclose_has_no_step :
  forall e a b g, step_result e (S2 a b) g = None.
Proof. intros. unfold step_result. now destruct (all_checked g). Qed.

Print Assumptions d3_initial_relation.
Print Assumptions d3_failure_preserves_prefix.
Print Assumptions d3_commit_is_exact.
Print Assumptions d3_two_steps_exact.
Print Assumptions d3_occurrences_and_order.
Print Assumptions d3_preclose_has_no_step.
