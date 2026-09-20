# Phase 1 INT-008 / INT-009 / INT-010 closeout audit v1

## Status

This note records the closeout audit performed after INT-007 froze the complete
Phase-1 handoff inventory.

The audit found no remaining implementation slice required for INT-008,
INT-009, or INT-010. Their exit evidence is already executable and permanent on
`main`.

## INT-008 — ordinary one-shot source integration

INT-008 closes the ordinary source-to-runtime one-shot integration path.

The executable boundary includes:

- source-level protocol endpoint parameters;
- architecture component provisioning and activation;
- exact source send/receive provisioning;
- unrestricted payload flow;
- send/receive rendezvous;
- explicit endpoint close; and
- genuine root-terminal network closure.

The cumulative source witness in
`test/Phase1INT008SourcePingTerminalMain.hs` starts from Grammar-v1 source,
derives the exact protocol/architecture/component identities, performs the
source-derived rendezvous, closes both endpoints, and requires the complete
process population to reach root terminal.

Focused permanent gates cover the constituent seams, including
`Phase1INT008ComponentSendProvisioningMain.hs`,
`Phase1INT008ArchitectureComponentProvisioningMain.hs`,
`Phase1INT008ArchitectureComponentActivationMain.hs`,
`Phase1INT008PingRendezvousTerminalMain.hs`, and the corresponding
`.github/workflows/phase1-int008-*.yml` workflows.

INT-007 additionally freezes the accepted one-shot Ping source and its canonical
VerificationBundle under INT-008/VER-012 authority.

## INT-009 — progressive Ping execution

INT-009 closes the progressive ordinary-source/runtime Ping ladder beyond the
one-shot witness.

Permanent executable evidence covers:

1. request/reply source shape and observable runtime output;
2. bounded Ping source values, loop source shape, and bounded runtime;
3. productive unbounded Ping with genuine `NetworkCanStep` progression; and
4. interruptible Ping whose external SIGINT is admitted only through explicit
   provider/capability/boundary/entry provenance, selects the source-level
   `Done` branch, closes the protocol, and reaches genuine root terminal.

The cumulative runtime controls live in the
`test/Phase1INT009*.hs` harnesses and their permanent
`.github/workflows/phase1-int009-*.yml` gates.

INT-007 freezes the request/reply, bounded, unbounded, and interruptible source
witnesses and their canonical VerificationBundles under INT-009/VER-012
authority.

## INT-010 — warning-free Haskell integration

INT-010 closes the project-owned Haskell warning-debt boundary.

The canonical signal is:

```text
cabal build all --enable-tests --ghc-options=-Werror
```

The permanent `Phase 1 Warning-Free Haskell Integration` workflow applies that
gate to the whole project and separately rechecks historically suppressed
authored seams with plain `-Wall -Werror`.

The remaining `-Wno-*` exceptions are generator/extractor-owned boundaries
documented in `warning-free-haskell-integration-v1.md`; they are not
project-authored warning debt.

## Closeout result

INT-008, INT-009, and INT-010 require no new implementation tranche after the
INT-007 freeze. Regressions remain guarded by their existing permanent
workflows, and the frozen INT-007 handoff retains the source/verification
artifacts needed to reconstruct the integration witnesses.

The next integration case is INT-011: certification and publication of the
standalone Phase-1 Phil distribution.
