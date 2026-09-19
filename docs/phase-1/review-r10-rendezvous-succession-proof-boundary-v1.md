# PHIL-P1-REVIEW-R10 proof boundary

This slice certifies Astra Review R10: consecutive synchronous rendezvous steps compose only through the exact live successor state returned by the preceding rendezvous.

The predecessor authority is already Certified by `PHIL-CONC-RENDEZVOUS-001`. For every accepted rendezvous it proves that:

- both predecessor endpoint occurrences are consumed;
- both exact successor occurrences are installed; and
- the successor sessions remain exact duals.

R10 adds the state-composition rule: the second rendezvous' input state must be exactly the first rendezvous' output state. Therefore the old predecessor endpoint name is absent from the second step's live state and cannot be reused.

The concrete Haskell split mirrors this distinction. `checkProcessCommunicationState` is the initial-state path and remains strict against the immutable role projection. `checkProcessCommunicationSuccessor` is the live-successor path: it retains exact instance/role identity, current duality, local action admissibility, and endpoint-owner advancement without incorrectly rechecking the continuation against the initial projection.

`certifyProcessRendezvousSuccessor` is the public certified composition route. It accepts the preceding certified rendezvous, feeds its exact returned communication state into the live-successor checker, and returns the next certified state only if the second joint transition succeeds.

The permanent R10 regression exercises a real request/reply chain, checks the owner index and protocol contexts after both transitions, rejects stale predecessor endpoint names on the second step, and confirms that the activation-only checker remains strict rather than being weakened to accommodate live successors.

Concrete Map identity, endpoint occurrence lookup, owner-index update ordering, ProcessKey/Name representation, Haskell exception/result plumbing, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
