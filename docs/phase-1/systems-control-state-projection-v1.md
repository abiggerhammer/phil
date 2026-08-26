# Phase 1 Systems control-state projection v1

Status: bounded executable conformance slice for `SYS-008`.

## Governing rule

CFG and closure lowering must preserve exact resource-carrying state. Ordinary joins, loop initial entries, and loop backedges do not get separate ownership algorithms: they all re-enter one explicit state contract through the same projection checker.

A lowering may not:

- omit a required state slot;
- carry a restricted owner at the wrong structural mode;
- use one restricted owner for two post-state slots;
- leave a live linear predecessor owner unaccounted;
- carry a scoped borrowed view as state;
- substitute an equal-role/equal-representation value for a fixed semantic subject;
- send a projection over the wrong CFG edge; or
- duplicate one restricted closure capture into several target carriers.

## State boundaries

A `StateBoundaryContract` fixes:

- a stable boundary key;
- ordinary-join or loop-state kind;
- exact Systems function;
- exact target block; and
- an exact state-slot telescope.

Each `StateSlotContract` fixes:

- stable slot key;
- structural mode; and
- either no fixed subject requirement or one exact `SourceSubjectKey`.

Fixed subjects are checked against the already-verified SYS-004 `SubjectCorrespondence` relation. Runtime storage identity, pointer equality, type resemblance, and value spelling do not establish continuity.

## One projection relation

`checkStateProjection` is reused unchanged for:

- `OrdinaryJoinPredecessor`;
- `LoopInitialEntry`; and
- `LoopBackedge`.

Each projection records:

- the exact state boundary;
- exact predecessor block;
- exact outgoing arm/edge label;
- the restricted owners live at that predecessor edge and their structural modes; and
- the exact predecessor-value mapping into the state slots.

The checker independently reads the Systems CFG and requires the named edge to reach the target state block.

The slot-binding domain must exactly equal the target state telescope.

For restricted slots, the bound value must be a live owning occurrence at the exact required mode. A `BorrowedSlice` is never a state owner and cannot cross a join/backedge as state.

Every live linear predecessor owner must occur exactly once in the projection. An affine owner may be absent by legal weakening, but absence does not create an implicit maybe-present post-state value.

## Join and loop shape

An ordinary join requires at least two ordinary predecessor projections and no loop-entry/backedge projections.

A loop state requires at least one initial-entry projection and at least one backedge projection, with no ordinary-join projection. Both kinds re-enter the same `StateBoundaryContract` using the same checker.

This is the executable form of the Resource State, Join, and Invariant Checking Contract rule that loop headers reuse ordinary join-state compatibility rather than acquiring a second semantics.

## Closure capture ownership

SYS-008 adds a separate bounded representation-cardinality check for closure captures.

`ClosureCaptureProjection` consumes the same `CallableCaptureSemantic` facts used by CALL-016 and records the target carrier slots assigned to each capture occurrence.

For affine or linear captures:

- exactly one target carrier is required; and
- one target carrier cannot stand for two distinct restricted source captures.

Unrestricted captures are not subject to exactly-once carrier cardinality and may be duplicated by representation.

This checker is intentionally complementary to CALL-016. CALL-016 establishes semantic callable correspondence; SYS-008 checks that restricted capture ownership is not duplicated by the chosen target representation.

## Witnesses and conformance corpus

The real Steve integration witness uses the `put.ok` reconvergence:

- `installed` and `already-exists` are two exact arms of `BlobProvider.install-if-absent`;
- both reach `put.ok`;
- both carry the exact linear `put.candidate` owner; and
- the state slot requires the exact `steve.bytes.candidate` stable subject already established by SYS-004.

The generic loop fixture uses one `LoopWorker` state contract for both the initial entry and a backedge. Mutation cases require rejection of:

- a missing backedge slot;
- an equal-role but wrong-subject owner;
- an extra live linear owner omitted from the loop state; and
- a scoped borrowed view carried across the backedge.

The closure corpus requires:

- one carrier for one restricted capture;
- rejection of two carriers for one restricted capture;
- rejection when one carrier is shared by two restricted captures; and
- acceptance of multiple carriers for an unrestricted capture.

The control-state stage revision is canonical under map ordering.

## Deferred

This slice does not yet implement protocol-state succession (`SYS-009`), exact boundary owner/length and send commit-point semantics (`SYS-010`), evidence transfer (`SYS-011`), erasure/strengthening, assumption laundering, runtime carrier/site multiplicity, staging effects/cost, or next-stage ABI requirements.
