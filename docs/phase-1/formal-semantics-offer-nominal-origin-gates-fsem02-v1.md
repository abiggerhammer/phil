# FSEM-02: source-offer nominal instance and role fail-closed gates

**Status: bounded non-normative source/Core and conditional-model conformance.**
Follows protected merged #1735; FSEM-02 remains open under #1613.

## Scope and external inputs

An independently admitted and instantiated `Choice` protocol, the exact
source-checked `Server` projection, the parsed complete offer component,
and a live endpoint occurrence with the same *local Session head* are provided.
The local head alone cannot authorize a nominal protocol instance or role.

```text
Sigma ; source-offer ; local-head-matched ; liveInstance != projectedInstance
  => rejected(ProtocolInstanceMismatch sourceEndpoint expected actual)
Sigma ; source-offer ; local-head-matched ; liveRole != projectedRole
  => rejected(ProtocolRoleMismatch sourceEndpoint expected actual)
Sigma ; source-offer ; BOTH nominal values mismatched
  => rejected(ProtocolInstanceMismatch sourceEndpoint expected actual)
Sigma ; source-offer ; both nominal values match ; label=Go|Cancel
  => separately checked typed successor, predecessor consumed
```

The production `GrammarV1OfferReplayProtocolError` wraps the exact
`ProtocolInstanceMismatch` or `ProtocolRoleMismatch` constructors.
For both Go and Cancel, identical local Session text is intentionally
insufficient to continue. An unsuccessful `Either` returns **no**
post-rejection successor. Distinct live instance/role identities are
explicit inputs to `insertProtocolEndpoint`, not derived from the source.

## Executable and Rocq evidence

- The accepted full Grammar-v1 source is
  `test/fixtures/fsem02-source-offer-v1/accepted.phil`. The minimal
  rejected full source `test/fixtures/fsem02-branch-outcome-separation-v1/missing-cancel.phil`
  still rejects specifically `GrammarV1ComponentOfferMissingArm "Cancel"`.
- `test/Phase1FSEM02BranchOutcomeSeparationMain.hs` independently runs the
  real source parser, family instantiation, projection and coverage checks,
  then uses the **same exact source-rooted endpoint name and Session head**
  with wrong instance, wrong role, or both. Exact errors and the
  instance-before-role failure class are asserted for each external label;
  matching identities are separately executed as a positive control.
- `proof/Phil/Core/FSEM02OfferNominalOriginGates.v` proves the bounded
  finite identity-gate model cannot advance on mismatched instance or role,
  delegates to the existing local progression on equal identities, and
  cannot fabricate a successful successor after an instance mismatch.
  The booleans model externally supplied identity equality facts.
- `.github/workflows/fsem02-offer-nominal-origin-gates-preflight.yml`
  runs strict GHC 9.6.7 and Rocq 9.2 proof checking before broad PR CI.

## Trust premises and nonclaims

The source grammar, independent protocol admission, activation, exact
projected instance and role, selected external label, successor-name
freshness and terminal disposal authorization remain explicit premises.
A manually supplied wrong role is a negative Core test input, **not**
evidence that such a role is valid for that instance. This neither
executes the network peer nor establishes a rendezvous, complete
Haskell-to-Rocq refinement, general source semantics, architecture
certification, or proof of nominal identity from equal local heads.
The normative EBNF and TCB are unchanged.
