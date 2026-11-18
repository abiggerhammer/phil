From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import P9G3SteveGetClosedRefinement.
Import ListNotations.

(*
  P9 G3 / FSEM-05/06: an EXECUTABLE, CLOSED-FRAGMENT candidate semantics
  with explicit provider-choice inputs. This imports the previously checked
  *candidate* P9SourceState and P9CoreState models, NOT actual Phil Surface
  evaluation, actual Core execution, linked native code or a provider law.
  It is intentionally not a normative FSEM-05 full-language interpreter.
*)

Definition p9_owner_eqb (a b : P9Owner) : bool :=
  Nat.eqb (p9_owner_run a) (p9_owner_run b) &&
  Nat.eqb (p9_owner_serial a) (p9_owner_serial b).

Definition p9_loan_eqb (a b : P9Loan) : bool :=
  p9_owner_eqb (p9_loan_owner a) (p9_loan_owner b) &&
  Nat.eqb (p9_loan_serial a) (p9_loan_serial b).

Lemma p9_owner_eqb_refl : forall o, p9_owner_eqb o o = true.
Proof.
  intros [run serial]. unfold p9_owner_eqb. simpl.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma p9_loan_eqb_refl : forall l, p9_loan_eqb l l = true.
Proof.
  intros [owner serial]. unfold p9_loan_eqb. simpl.
  rewrite p9_owner_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* Observable external read result / digest result is chosen explicitly.
   CheckOwner and CheckLoan are GHOST assertions for this checker model:
   they are not arguments of the current native digest ABI. *)
Inductive P9Input : Type :=
  | P9Call
  | P9ReadFound (read_serial : nat)
  | P9ReadNotFound
  | P9ReadStorageFailure
  | P9OpenLoan (loan_serial : nat)
  | P9Check (claimed_owner : P9Owner) (claimed_loan : P9Loan)
      (claimed_content : nat) (result : P9Digest)
  | P9CloseLoan
  | P9Release
  | P9Return.

Definition p9_source_next (s : P9SourceState) (input : P9Input)
  : option P9SourceState :=
  match s, input with
  | P9SEntry pin, P9Call => Some (P9SAwait pin)
  | P9SAwait pin, P9ReadFound serial =>
      Some (P9SFound pin (P9MkOwner (p9_run pin) serial))
  | P9SAwait pin, P9ReadNotFound =>
      Some (P9SNoOwner pin P9NotFound)
  | P9SAwait pin, P9ReadStorageFailure =>
      Some (P9SNoOwner pin P9StorageFailure)
  | P9SFound pin owner, P9OpenLoan serial =>
      Some (P9SBorrow pin owner (P9MkLoan owner serial))
  | P9SBorrow pin owner loan,
      P9Check claimed_owner claimed_loan claimed_content result =>
      if p9_owner_eqb owner claimed_owner &&
         p9_loan_eqb loan claimed_loan &&
         Nat.eqb (p9_content_id pin) claimed_content
      then Some (P9SChecked pin owner loan result)
      else None
  | P9SChecked pin owner loan result, P9CloseLoan =>
      Some (P9SClosed pin owner result)
  | P9SClosed pin owner result, P9Release =>
      Some (P9SReleased pin result)
  | P9SReleased pin result, P9Return =>
      Some (P9SDone pin (p9_digest_exit result))
  | P9SNoOwner pin outcome, P9Return =>
      Some (P9SDone pin outcome)
  | _, _ => None
  end.

(* Soundness and converse coverage are for the exact above fragment
   against the candidate declarative source-step relation. *)
Theorem p9_fsem05_fragment_step_sound :
  forall s input s',
    p9_source_next s input = Some s' -> p9_source_step s s'.
Proof.
  intros s input s' Step.
  destruct s; destruct input; simpl in Step; try discriminate.
  all: repeat match goal with
       | H : (if ?condition then _ else _) = Some _ |- _ =>
           destruct condition eqn:Guard; simpl in H; try discriminate
       end.
  all: inversion Step; subst; constructor.
Qed.

Theorem p9_fsem05_fragment_step_complete :
  forall s s',
    p9_source_step s s' ->
    exists input, p9_source_next s input = Some s'.
Proof.
  intros s s' Step.
  destruct Step.
  - exists P9Call. reflexivity.
  - exists (P9ReadFound serial). reflexivity.
  - exists P9ReadNotFound. reflexivity.
  - exists P9ReadStorageFailure. reflexivity.
  - exists (P9OpenLoan serial). reflexivity.
  - exists (P9Check o l (p9_content_id p) result).
    simpl. rewrite p9_owner_eqb_refl, p9_loan_eqb_refl,
      Nat.eqb_refl. reflexivity.
  - exists P9CloseLoan. reflexivity.
  - exists P9Release. reflexivity.
  - exists P9Return. reflexivity.
  - exists P9Return. reflexivity.
Qed.

(* Explicitly distinguish normal return, an invalid provided event,
   need-for-input, and insufficient fuel; none are silent successes. *)
Inductive P9ReplayResult : Type :=
  | P9Normal (outcome : P9Exit)
  | P9InvalidChoice
  | P9NeedsInput
  | P9FuelExhausted.

Fixpoint p9_replay (fuel : nat) (s : P9SourceState)
    (inputs : list P9Input) : P9ReplayResult :=
  match s with
  | P9SDone _ outcome =>
      match inputs with
      | [] => P9Normal outcome
      | _ :: _ => P9InvalidChoice
      end
  | _ =>
      match fuel with
      | O => P9FuelExhausted
      | S rest =>
          match inputs with
          | [] => P9NeedsInput
          | i :: remaining =>
              match p9_source_next s i with
              | None => P9InvalidChoice
              | Some next => p9_replay rest next remaining
              end
          end
      end
  end.

Definition p9_sample_pin := P9MkPin 7 101 11 13.
Definition p9_sample_owner := P9MkOwner 7 23.
Definition p9_sample_loan := P9MkLoan p9_sample_owner 29.
Definition p9_sample_good_accept : list P9Input :=
  [ P9Call; P9ReadFound 23; P9OpenLoan 29;
    P9Check p9_sample_owner p9_sample_loan 101 P9Accept;
    P9CloseLoan; P9Release; P9Return ].
Definition p9_sample_good_reject : list P9Input :=
  [ P9Call; P9ReadFound 23; P9OpenLoan 29;
    P9Check p9_sample_owner p9_sample_loan 101 P9Reject;
    P9CloseLoan; P9Release; P9Return ].

Example p9_fsem05_accept_run :
  p9_replay 7 (P9SEntry p9_sample_pin)
    p9_sample_good_accept = P9Normal P9Success.
Proof. reflexivity. Qed.

Example p9_fsem05_reject_run :
  p9_replay 7 (P9SEntry p9_sample_pin)
    p9_sample_good_reject = P9Normal P9IntegrityFailure.
Proof. reflexivity. Qed.

Example p9_fsem05_not_found :
  p9_replay 3 (P9SEntry p9_sample_pin)
    [P9Call; P9ReadNotFound; P9Return] = P9Normal P9NotFound.
Proof. reflexivity. Qed.

Example p9_fsem05_storage_failure :
  p9_replay 3 (P9SEntry p9_sample_pin)
    [P9Call; P9ReadStorageFailure; P9Return] =
    P9Normal P9StorageFailure.
Proof. reflexivity. Qed.

(* Two separate live owners may have identical payload/root/hash/pointer
   *representations*. The actual ABI does not pass the model's owner serial. *)
Example p9_fsem05_cross_invocation_rejected :
  p9_source_next
    (P9SBorrow p9_sample_pin p9_sample_owner p9_sample_loan)
    (P9Check (P9MkOwner 8 23) p9_sample_loan 101 P9Accept) = None.
Proof. reflexivity. Qed.

Example p9_fsem05_aba_incarnation_rejected :
  p9_source_next
    (P9SBorrow p9_sample_pin p9_sample_owner p9_sample_loan)
    (P9Check (P9MkOwner 7 24) p9_sample_loan 101 P9Accept) = None.
Proof. reflexivity. Qed.

Example p9_fsem05_wrong_content_operand_rejected :
  p9_source_next
    (P9SBorrow p9_sample_pin p9_sample_owner p9_sample_loan)
    (P9Check p9_sample_owner p9_sample_loan 102 P9Accept) = None.
Proof. reflexivity. Qed.

Example p9_fsem05_digest_before_borrow_rejected :
  p9_source_next
    (P9SFound p9_sample_pin p9_sample_owner)
    (P9Check p9_sample_owner p9_sample_loan 101 P9Accept) = None.
Proof. reflexivity. Qed.

Example p9_fsem05_out_of_fuel :
  p9_replay 2 (P9SEntry p9_sample_pin)
    p9_sample_good_accept = P9FuelExhausted.
Proof. reflexivity. Qed.

Example p9_fsem05_missing_environment_choice :
  p9_replay 7 (P9SEntry p9_sample_pin)
    [P9Call] = P9NeedsInput.
Proof. reflexivity. Qed.

Theorem p9_fsem06_fragment_weak_forward_step :
  forall s input s',
    p9_source_next s input = Some s' ->
    p9_erase_source s = p9_erase_source s' \/
    p9_core_step (p9_erase_source s) (p9_erase_source s').
Proof.
  intros s input s' Accepted.
  apply p9_r2_model_source_to_core_weak_step.
  eapply p9_fsem05_fragment_step_sound; eauto.
Qed.

(* Not a machine-code or native source-owner relation. This theorem is
   target MODEL reachability from the previous candidate Core machine. *)
Theorem p9_fsem06_fragment_target_model_no_cross_run :
  forall entry core pin owner result,
    p9_core_reachable entry core ->
    p9_core_step core (P9CChecked pin owner result) ->
    p9_owner_run owner = p9_run pin.
Proof.
  intros entry core pin owner result Reach Step.
  pose proof (p9_r2_model_target_digest_original_invocation
    entry core pin owner result Reach Step) as [_ Association].
  exact Association.
Qed.

Print Assumptions p9_fsem05_fragment_step_sound.
Print Assumptions p9_fsem05_fragment_step_complete.
Print Assumptions p9_fsem06_fragment_weak_forward_step.
Print Assumptions p9_fsem06_fragment_target_model_no_cross_run.
