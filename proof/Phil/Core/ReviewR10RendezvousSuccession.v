From Phil.Core Require Import ConcurrencyRendezvous.

(*
  PHIL-P1-REVIEW-R10 — accepted rendezvous state composes only through the exact
  successor endpoints returned by the preceding rendezvous.

  PHIL-CONC-RENDEZVOUS-001 already proves that an accepted rendezvous consumes
  each predecessor occurrence, installs the exact successor occurrence, and
  preserves dual successor sessions. R10 adds the chain rule: the next
  rendezvous must start from that exact returned live state. Reusing a stale
  predecessor name is therefore invalid by construction.
*)

Record RendezvousChain : Type := mkRendezvousChain {
  chainFirstWitness : ConcurrencyRendezvous.DualRendezvousWitness;
  chainSecondWitness : ConcurrencyRendezvous.DualRendezvousWitness;
  chainFirstAccepted :
    ConcurrencyRendezvous.ExactInternalRendezvous chainFirstWitness;
  chainSecondAccepted :
    ConcurrencyRendezvous.ExactInternalRendezvous chainSecondWitness;
  chainSenderStateHandoff :
    ConcurrencyRendezvous.endpointProgressionBefore
      (ConcurrencyRendezvous.dualRendezvousSenderEndpoint chainSecondWitness) =
    ConcurrencyRendezvous.endpointProgressionAfter
      (ConcurrencyRendezvous.dualRendezvousSenderEndpoint chainFirstWitness);
  chainReceiverStateHandoff :
    ConcurrencyRendezvous.endpointProgressionBefore
      (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint chainSecondWitness) =
    ConcurrencyRendezvous.endpointProgressionAfter
      (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint chainFirstWitness)
}.

Theorem review_r10_first_rendezvous_consumes_both_predecessors :
  forall chain,
    (ConcurrencyRendezvous.endpointProgressionAfter
      (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
        (chainFirstWitness chain))
      (ConcurrencyRendezvous.protocolOccurrenceName
        (ConcurrencyRendezvous.endpointProgressionPredecessor
          (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
            (chainFirstWitness chain)))) = None) /\
    (ConcurrencyRendezvous.endpointProgressionAfter
      (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
        (chainFirstWitness chain))
      (ConcurrencyRendezvous.protocolOccurrenceName
        (ConcurrencyRendezvous.endpointProgressionPredecessor
          (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
            (chainFirstWitness chain)))) = None).
Proof.
  intros chain.
  apply ConcurrencyRendezvous.accepted_rendezvous_predecessors_are_consumed.
  exact (chainFirstAccepted chain).
Qed.

Theorem review_r10_first_rendezvous_installs_exact_successors :
  forall chain,
    (exists predecessorContract,
      ConcurrencyRendezvous.endpointProgressionBefore
        (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
          (chainFirstWitness chain))
        (ConcurrencyRendezvous.protocolOccurrenceName
          (ConcurrencyRendezvous.endpointProgressionPredecessor
            (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
              (chainFirstWitness chain)))) = Some predecessorContract /\
      ConcurrencyRendezvous.endpointProgressionAfter
        (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
          (chainFirstWitness chain))
        (ConcurrencyRendezvous.endpointProgressionSuccessorName
          (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
            (chainFirstWitness chain))) =
      Some (ConcurrencyRendezvous.continuedContract predecessorContract
        (ConcurrencyRendezvous.endpointProgressionSuccessorSession
          (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
            (chainFirstWitness chain))))) /\
    (exists predecessorContract,
      ConcurrencyRendezvous.endpointProgressionBefore
        (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
          (chainFirstWitness chain))
        (ConcurrencyRendezvous.protocolOccurrenceName
          (ConcurrencyRendezvous.endpointProgressionPredecessor
            (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
              (chainFirstWitness chain)))) = Some predecessorContract /\
      ConcurrencyRendezvous.endpointProgressionAfter
        (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
          (chainFirstWitness chain))
        (ConcurrencyRendezvous.endpointProgressionSuccessorName
          (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
            (chainFirstWitness chain))) =
      Some (ConcurrencyRendezvous.continuedContract predecessorContract
        (ConcurrencyRendezvous.endpointProgressionSuccessorSession
          (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
            (chainFirstWitness chain))))).
Proof.
  intros chain.
  apply ConcurrencyRendezvous.accepted_rendezvous_installs_exact_successors.
  exact (chainFirstAccepted chain).
Qed.

Theorem review_r10_second_rendezvous_starts_from_exact_first_successor_state :
  forall chain,
    ConcurrencyRendezvous.endpointProgressionBefore
      (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
        (chainSecondWitness chain)) =
    ConcurrencyRendezvous.endpointProgressionAfter
      (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
        (chainFirstWitness chain)) /\
    ConcurrencyRendezvous.endpointProgressionBefore
      (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
        (chainSecondWitness chain)) =
    ConcurrencyRendezvous.endpointProgressionAfter
      (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
        (chainFirstWitness chain)).
Proof.
  intros chain.
  split.
  - exact (chainSenderStateHandoff chain).
  - exact (chainReceiverStateHandoff chain).
Qed.

Theorem review_r10_second_rendezvous_keeps_successor_duality :
  forall chain,
    ConcurrencyRendezvous.endpointProgressionSuccessorSession
      (ConcurrencyRendezvous.dualRendezvousReceiverEndpoint
        (chainSecondWitness chain)) =
    ConcurrencyRendezvous.dualSession
      (ConcurrencyRendezvous.endpointProgressionSuccessorSession
        (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
          (chainSecondWitness chain))).
Proof.
  intros chain.
  pose proof
    (ConcurrencyRendezvous.accepted_rendezvous_current_and_successor_sessions_are_dual
      (chainSecondWitness chain) (chainSecondAccepted chain)) as H.
  exact (proj2 H).
Qed.

Theorem review_r10_stale_predecessor_absent_from_successor_state :
  forall chain,
    ConcurrencyRendezvous.endpointProgressionBefore
      (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
        (chainSecondWitness chain))
      (ConcurrencyRendezvous.protocolOccurrenceName
        (ConcurrencyRendezvous.endpointProgressionPredecessor
          (ConcurrencyRendezvous.dualRendezvousSenderEndpoint
            (chainFirstWitness chain)))) = None.
Proof.
  intros chain.
  rewrite chainSenderStateHandoff.
  exact (proj1
    (ConcurrencyRendezvous.accepted_rendezvous_predecessors_are_consumed
      (chainFirstWitness chain) (chainFirstAccepted chain))).
Qed.
