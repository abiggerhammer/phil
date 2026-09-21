# PHIL-AUD-DIGEST-SUBJECT-001 remediation

## Audit identity

- Finding: `PHIL-AUD-DIGEST-SUBJECT-001`
- Original event: `PHIL-AUDIT-20260921-VALIDATOR-SUBJECT`
- Corroborating event: `PHIL-AUDIT-20260921-VALIDATION-PROOF-CORRESPONDENCE`
- Original review snapshot: `bb9d36680b336e98ce4a78583602302a87b4b90e`
- Public producer: `Phil.Surface.Check.Engine.evalValidate`
- Public consumer boundary: `Phil.Surface.Check.checkSurfaceComponent` and
  `Phil.Verification.verifySurfaceApplication`

This slice is an implementation and public-consumer remediation. It does not
promote any proof or Certified-ledger status.

## Root cause

The previous `DigestMatches` path checked only that its source subject was
readable, then discarded the supplied operands and always constructed:

`DigestMatches(begin, stable-id(payload))`

Consequently malformed subjects and a real borrowed view of another byte owner
could produce evidence for the privileged pair expected by the later
`accepted` session branch.

The final evidence consumer compared propositions exactly. The defect was the
producer constructing the wrong proposition upstream.

## Stable byte-owner identity

A correct repair cannot simply whitelist the spellings `begin`,
`payloadView`, or `payload`. Evidence must describe the actual checked
subjects, and an ownership-preserving local move must not accidentally change
the semantic byte object being described.

Surface byte shapes therefore now carry an optional stable owner term in
addition to their existing byte-length/index term:

- a newly introduced byte owner receives
  `RefOpaque (SortStableId "OwnedBytes") <first-owner-name>`;
- `shapeForBinding` preserves an already assigned stable owner term through
  later ownership moves;
- a borrowed view carries that same stable term alongside the currently loaned
  binding name;
- non-byte borrowable resources keep no byte-owner term and therefore cannot be
  used as a DigestMatches byte subject.

The existing Core linear/affine use discipline remains the authority for
ownership movement. This metadata records subject identity; it does not create a
second owner.

## DigestMatches subject contract

The Phase-0 `DigestMatches` Surface route now requires:

1. no explicit validation context locator;
2. exactly two ordered subject expressions;
3. a named first subject whose semantic type is `Frame[Begin]` (including an
   allowed outer refinement);
4. a second subject whose checked value is a borrowed byte view;
5. the exact `SharedBytes` validator type; and
6. a retained stable byte-owner identity.

Only after those checks does the producer construct:

`DigestMatches(actual-begin-name, actual-stable-byte-owner)`

The accepted decision arm is unchanged and still inserts exactly that
proposition as proof evidence. Existing `select` requirement comparison is
also unchanged.

Thus validating a view of `other` may produce valid evidence about
`other`, but that evidence cannot satisfy a requirement for the separately
received `payload`.

## Regression corpus

`test/Phase1AuditDigestSubjectMain.hs` exercises both the public checker and
the public intrinsic gate for each source case. The corpus combines Astra's
original and corroborating obligations:

- valid `(begin, view)` acceptance with exact returned proof type;
- alpha-renamed view acceptance;
- legal owner move/alias preserving the original stable owner identity;
- Boolean, Unit, reversed, wrong-arity, wrong-second-type and integer-pair
  rejection;
- unknown-view rejection;
- explicit-context rejection;
- existing missing-evidence rejection;
- a genuine distinct byte owner that cannot authorize the received payload;
- complete unchanged UploadServer acceptance;
- one-site full UploadServer mutation to `(0, 1)` rejection; and
- preservation of the generic opaque-proof rejection.

The full-server mutation is checked to replace exactly one source occurrence.

The dedicated workflow also replays:

- the existing intrinsic-invalidity corpus;
- the frozen Surface conformance suite; and
- the portable negative-manifest consumer affected by the extended Surface
  shape representation.

## Assurance boundary

This repair establishes implementation-side subject/schema checking and
public-consumer propagation if the exact-head replay passes.

It does **not** by itself establish the separate proof-correspondence obligation
identified by Astra: a proof/production-binding lane still needs to connect the
checked validator descriptor to the appropriate formal subject-correspondence
claim, or explicitly retain that boundary in the assurance account.

Generic non-digest validators, native digest implementation correctness,
architecture/lowering/certification correspondence beyond the public intrinsic
gate, and final frozen-delta audit remain separate ledger work.

At authoring, exact-head CI has not yet supplied execution evidence.
