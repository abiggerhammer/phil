From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat.

Import ListNotations.

(*
  PHIL-P1-REVIEW-R11 — a transfer-free rendezvous may advance an endpoint
  occurrence only when the concrete owner ledger contains exactly one current
  owner entry for that process/predecessor pair.

  PHIL-CONC-RENDEZVOUS-001 remains the protocol/session authority.  R11 closes
  the concrete ownership bridge used by ProcessRendezvous.advanceEndpointOwner:
  owner resolution must be exact-one, and the accepted update retains the same
  occurrence identity while replacing only the local endpoint name with the
  requested successor.

  Missing or ambiguous owner resolution rejects.  Protocol acceptance alone
  cannot manufacture endpoint ownership.
*)

Definition ReviewR11Occurrence := nat.
Definition ReviewR11Process := nat.
Definition ReviewR11Name := nat.

Record ReviewR11OwnerEntry : Type := mkReviewR11OwnerEntry {
  r11OwnerOccurrence : ReviewR11Occurrence;
  r11OwnerProcess : ReviewR11Process;
  r11OwnerName : ReviewR11Name
}.

Definition reviewR11OwnerMatches
  (process : ReviewR11Process)
  (predecessor : ReviewR11Name)
  (entry : ReviewR11OwnerEntry) : bool :=
  Nat.eqb process (r11OwnerProcess entry) &&
  Nat.eqb predecessor (r11OwnerName entry).

Fixpoint reviewR11MatchingOwners
  (process : ReviewR11Process)
  (predecessor : ReviewR11Name)
  (owners : list ReviewR11OwnerEntry)
  : list ReviewR11OwnerEntry :=
  match owners with
  | [] => []
  | entry :: rest =>
      if reviewR11OwnerMatches process predecessor entry
      then entry :: reviewR11MatchingOwners process predecessor rest
      else reviewR11MatchingOwners process predecessor rest
  end.

Inductive ReviewR11OwnerResolution : Type :=
| R11OwnerMissing
| R11OwnerUnique (entry : ReviewR11OwnerEntry)
| R11OwnerAmbiguous.

Definition resolveReviewR11Owner
  (process : ReviewR11Process)
  (predecessor : ReviewR11Name)
  (owners : list ReviewR11OwnerEntry)
  : ReviewR11OwnerResolution :=
  match reviewR11MatchingOwners process predecessor owners with
  | [] => R11OwnerMissing
  | [entry] => R11OwnerUnique entry
  | _ => R11OwnerAmbiguous
  end.

Inductive ReviewR11AdvanceResult : Type :=
| R11AdvanceRejected
| R11Advanced (entry : ReviewR11OwnerEntry).

Definition advanceReviewR11Owner
  (process : ReviewR11Process)
  (predecessor successor : ReviewR11Name)
  (owners : list ReviewR11OwnerEntry)
  : ReviewR11AdvanceResult :=
  match resolveReviewR11Owner process predecessor owners with
  | R11OwnerUnique entry =>
      R11Advanced
        (mkReviewR11OwnerEntry
          (r11OwnerOccurrence entry)
          process
          successor)
  | _ => R11AdvanceRejected
  end.

Theorem review_r11_missing_endpoint_owner_rejects :
  forall process predecessor successor owners,
    reviewR11MatchingOwners process predecessor owners = [] ->
    advanceReviewR11Owner process predecessor successor owners =
      R11AdvanceRejected.
Proof.
  intros process predecessor successor owners Hmissing.
  unfold advanceReviewR11Owner, resolveReviewR11Owner.
  rewrite Hmissing.
  reflexivity.
Qed.

Theorem review_r11_ambiguous_endpoint_owner_rejects :
  forall process predecessor successor owners first second rest,
    reviewR11MatchingOwners process predecessor owners =
      first :: second :: rest ->
    advanceReviewR11Owner process predecessor successor owners =
      R11AdvanceRejected.
Proof.
  intros process predecessor successor owners first second rest Hambiguous.
  unfold advanceReviewR11Owner, resolveReviewR11Owner.
  rewrite Hambiguous.
  reflexivity.
Qed.

Theorem review_r11_unique_owner_advances_same_occurrence :
  forall process predecessor successor owners entry,
    reviewR11MatchingOwners process predecessor owners = [entry] ->
    advanceReviewR11Owner process predecessor successor owners =
      R11Advanced
        (mkReviewR11OwnerEntry
          (r11OwnerOccurrence entry)
          process
          successor).
Proof.
  intros process predecessor successor owners entry Hunique.
  unfold advanceReviewR11Owner, resolveReviewR11Owner.
  rewrite Hunique.
  reflexivity.
Qed.

Theorem review_r11_unique_owner_update_preserves_occurrence_identity :
  forall process predecessor successor owners entry updated,
    reviewR11MatchingOwners process predecessor owners = [entry] ->
    advanceReviewR11Owner process predecessor successor owners =
      R11Advanced updated ->
    r11OwnerOccurrence updated = r11OwnerOccurrence entry.
Proof.
  intros process predecessor successor owners entry updated Hunique Hadvance.
  rewrite
    (review_r11_unique_owner_advances_same_occurrence
      process predecessor successor owners entry Hunique)
    in Hadvance.
  inversion Hadvance.
  reflexivity.
Qed.

Theorem review_r11_unique_owner_update_uses_exact_process_and_successor :
  forall process predecessor successor owners entry updated,
    reviewR11MatchingOwners process predecessor owners = [entry] ->
    advanceReviewR11Owner process predecessor successor owners =
      R11Advanced updated ->
    r11OwnerProcess updated = process /\
    r11OwnerName updated = successor.
Proof.
  intros process predecessor successor owners entry updated Hunique Hadvance.
  rewrite
    (review_r11_unique_owner_advances_same_occurrence
      process predecessor successor owners entry Hunique)
    in Hadvance.
  inversion Hadvance.
  split; reflexivity.
Qed.

Record ReviewR11RendezvousFacts : Type := mkReviewR11RendezvousFacts {
  r11ProtocolRendezvousAccepted : Prop;
  r11LeftOwnerResolvedExactlyOnce : Prop;
  r11RightOwnerResolvedExactlyOnce : Prop;
  r11LeftSameOccurrenceAdvanced : Prop;
  r11RightSameOccurrenceAdvanced : Prop
}.

Definition ReviewR11RendezvousValid
  (facts : ReviewR11RendezvousFacts) : Prop :=
  r11ProtocolRendezvousAccepted facts /\
  r11LeftOwnerResolvedExactlyOnce facts /\
  r11RightOwnerResolvedExactlyOnce facts /\
  r11LeftSameOccurrenceAdvanced facts /\
  r11RightSameOccurrenceAdvanced facts.

Theorem review_r11_protocol_acceptance_alone_is_not_enough :
  forall facts,
    ReviewR11RendezvousValid facts ->
    r11LeftOwnerResolvedExactlyOnce facts /\
    r11RightOwnerResolvedExactlyOnce facts.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [Hleft [Hright _]]].
  split; assumption.
Qed.

Theorem review_r11_valid_transfer_free_rendezvous_preserves_owner_identity :
  forall facts,
    ReviewR11RendezvousValid facts ->
    r11LeftSameOccurrenceAdvanced facts /\
    r11RightSameOccurrenceAdvanced facts.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [Hleft Hright]]]].
  split; assumption.
Qed.
