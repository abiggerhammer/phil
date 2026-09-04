# Phase 1 Concurrency Rendezvous production binding v1

This slice binds the existing production rendezvous/transfer implementation to the exact extracted decision surface staged by #690 for `PHIL-CONC-RENDEZVOUS-001`.

Production behavior remains native-first and pure. The bridge does not replace protocol checking, activation checking, participant classification, Message admissibility, resource transfer, or the process-causality representation with a second implementation. It composes those existing authorities, reflects their exact facts, and then asks the extracted kernel whether the Certified rendezvous theorem accepts them.

## Exact kernel

The checked-in reference and production copies are byte-identical to the #690 artifact:

- `generated/ConcurrencyRendezvousKernel.hs`
- `src/ConcurrencyRendezvousKernel.hs`
- size: 2,693 bytes
- SHA-256: `38ba061829cc7b4f85f678833da1ba8afa7fc2fb713ef0204b306dd1becc0a64`
- file ending: two newline bytes

CI freshly recompiles `ConcurrencyRendezvousImplementation.v`, re-extracts `ConcurrencyRendezvousKernel.hs`, checks the SHA-256 above, and `cmp`s both checked-in copies against the fresh extraction.

The exact kernel owns four Bool gates:

1. endpoint/binary exactness: nine facts;
2. participant linkage: five facts;
3. Message/coarse rendezvous linkage: seven facts;
4. the three-way `ExactInternalRendezvous` aggregate.

## Production composition

`Phil.Core.ConcurrencyRendezvousCertification` introduces two opaque predecessor witnesses.

`CertifiedRendezvousActivation` can only be created by rerunning `certifyConcurrencyActivation`, the #687 production-bound native-first activation/participant checker. The rendezvous bridge therefore does not trust a caller-supplied `ParticipantClassification` or an arbitrary activated `ProcessNetwork`.

`CertifiedRendezvousProtocol` can only be created by rerunning `instantiateBinaryProtocol` from the exact family, Message arguments, generic policy, and requirement dispositions. It retains the source family's primary/peer role orientation and both exact initial projections. This avoids inventing a new orientation witness to compensate for the compact `BinaryProtocolInstance` runtime representation.

For an accepted rendezvous, the bridge then:

1. joins protocol contexts to the certified activation state with `communicationStateFromActivation`;
2. runs the existing native `checkProcessCommunication` or `checkRestrictedProcessRendezvous`;
3. reruns the two pure local `checkProtocolAction` steps for reflected predecessor/successor evidence;
4. rechecks the exact ADR-016 `BoundaryMessageContract` and requires non-intrinsic Message evidence to equal one of the arguments used to instantiate the exact protocol;
5. reflects the nine endpoint/binary facts, including exact primary/peer roles, current dual sessions, and exact dual successors;
6. reflects the five participant facts from the opaque #687 predecessor, requiring the exact protocol-role occurrences to classify as internal to the exact sender/receiver `ProcessKey`s;
7. reflects the seven Message/coarse facts, including exact protocol instance/roles/processes and, when a `RestrictedMessageTransfer` is supplied, the exact sender-before/receiver-after owner occurrence;
8. calls all three group gates and the outer exact-rendezvous gate.

Any native-success/kernel-reject mismatch fails closed with the complete reflected fact record.

## Causality

The Certified theorem derives source causality from accepted rendezvous; scheduler order is not an input authority. Accordingly, a successful production result carries an opaque `CertifiedRendezvousCausality` that projects only to:

`SynchronousRendezvousEvent senderProcess receiverProcess`

in the existing `ProcessCausality` representation. The bridge does not accept a scheduler edge, worker identity, thread ordering, or declaration order as evidence.

The unchanged CONC-006 scheduler-independent partial-order corpus is rerun in the production-binding workflow.

## Message-bearing certified surface

`PHIL-CONC-RENDEZVOUS-001` has an independent `MessageContractAccepted` premise. The production bridge therefore fails closed unless both local protocol steps expose the same concrete `Message` type and an exact ADR-016 Message witness is supplied.

Native select/offer remains supported by `ProcessRendezvous.hs`, but a label-only select/offer step does not expose the Message witness required by this Certified theorem and is not silently promoted to one. Extending the Certified surface to label-only rendezvous requires a separate proof/model of label Message competence rather than a runtime convention.

## Restricted transfer

`certifyRestrictedProcessRendezvous` composes the stronger existing CONC-005 native transition. Before the kernel is called, native code has already required:

- affine/linear transfer mode;
- the exact sender-owned occurrence;
- exact sender and receiver endpoint actions;
- exact payload type and receiver binder;
- sender resource consumption;
- receiver resource insertion;
- exact endpoint-owner successor updates; and
- exact payload occurrence owner update sender -> receiver.

The reflected coarse fact additionally checks the same exact occurrence in the before and after global owner indexes.

## Production controls

`app/ConcurrencyRendezvousProductionBindingMain.hs` exercises:

1. accepted exact production composition on a real linear Message payload;
2. native missing-owner diagnostic precedence;
3. independent Message-evidence rejection;
4. injected endpoint-kernel disagreement;
5. injected participant-kernel disagreement;
6. injected Message/coarse-kernel disagreement;
7. injected outer exact-rendezvous disagreement; and
8. exact projection to synchronous semantic causality.

The workflow also reruns the #690 direct 28-control extracted-kernel harness, the #687 activation production harness, and the unchanged protocol projection, Message admission, exact rendezvous, restricted transfer, and scheduler-independent causality corpora.

## Residual assumptions / TCB boundary

This binding still relies on the concrete Haskell representation and runtime for:

- `Map`/`Set`/list/Text traversal and equality;
- `ProcessKey`, protocol-instance, role-occurrence, endpoint, and resource occurrence encoding;
- source-to-architecture extraction of process sites, activation contracts, and participant declarations;
- exact `ProtocolContext`/resource-map correspondence;
- `BoundaryMessageContract` semantic evidence supplied by the competent Message boundary;
- the correspondence between Haskell `Session` values and the Certified session model;
- the correspondence between `ProcessCausality` event values and the Certified source-causality relation;
- Rocq extraction, GHC, and the runtime environment.

Physical transport, buffering, IPC, locking/atomic synchronization, scheduler fairness, deadlock freedom, eventual response, deadlines, worker identity, and performance remain outside this safety theorem and require their own target/realization evidence.
