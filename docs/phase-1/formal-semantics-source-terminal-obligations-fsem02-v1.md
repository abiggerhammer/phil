# FSEM-02: checked-source process and root terminal obligation gate (non-normative)

Tracking: issue #1613. This bounded source-to-production-Core slice does not promote any formal-semantics rule to normative authority, alter the Phase 1 grammar, or change the trusted computing base.

## Judgment

Premises: (1) actual independently parsed and checked Grammar-v1 send/receive source and its post-rendezvous source-close transition; (2) a two-process activated network with externally authorized binary protocol instance, nominal roles, boundary message contract and activation-owned resource occurrences; (3) two explicit DeclaredTerminalTransition records, exact terminal outcomes, and separately supplied obligation/residue facts.

Transition: grammarV1CheckRestrictedSourceTerminal checks source-derived successor identities, the live receiver payload occurrence, exact process keys and explicit Closed controls. It initializes the production ProcessRuntimeState with the *actual post-close* protocol/resource contexts, invokes the existing applyDeclaredTerminalTransition checker twice, reconciles each specified disposal against one unique (process, name) activation-owner occurrence, rejects every unaccounted owner, and finally invokes classifyProcessNetwork with externally supplied root residues. Success returns only the final native runtime, the root terminal fact and an empty restricted-owner index. Every failure returns a precise Left with no intermediate successor. No source syntax confers disposal authority.

Core local disposal enforces exact resource consumption and rejects duplicate/unknown names, unrestricted resources, live linear debt, live endpoints, and open assurance obligations. Root classification rejects nonempty root resource, obligation, or observable residues. The externally supplied empty enabled-step list is justified here only after *both* processes have actual terminal facts; it is not a source scheduler or fairness claim.

## Concrete evidence and negatives

Accepted executable source: test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil. Minimally rejected executable source: rejected-stale-close.phil in the same directory, changing only the sender's close successor into its stale predecessor, rejected exactly as GrammarV1ComponentSendCloseCloseMismatch by the checked-source harness. Terminal errors are state/authority failures, NOT invented source-level dispose syntax.

The extended test/Phase1FSEM02RestrictedSourceTransferMain.hs replays parsed send/receive and both checked close statements, then explicitly disposes the remaining receiver-owned linear Bytes[8] payload and an independently activated affine spectator, checks terminal fact identities and empty exact owner index, and verifies deterministic replay. Negative cases demand exact errors for missing payload disposition (TerminalResourceError / UnconsumedLinearResources), unaccounted spectator, duplicate/unknown disposal, open local assurance obligations, live root resources, Continue control, absent payload owner and tampered source-close successor identity. No rejection may yield a successor.

proof/Phil/Core/FSEM02SourceTerminal.v proves conditional modeled owner retirement, gate rejection, arbitrary-spectator preservation, and complete emptiness only under an explicit all-other-owners-absent premise, importing the prior source-close lemma. Rocq 9.2, no new Admitted, Axiom or Parameter. The production evidence is finite Haskell conformance, NOT a universal Haskell-to-Rocq implementation-refinement theorem; SessionStep.v and ConcurrencySemantics.v retain their separate proof/authority boundaries.

The focused .github/workflows/fsem02-restricted-terminal-preflight.yml runs strict warning-free Haskell/source-conformance and the fresh Rocq proofs before opening broad CI.

## Explicit nonclaims

Neither the parsed source close command nor this adapter establishes source-authorized payload disposal, complete source architecture/root admission (FSEM-03), assurance discharge (FSEM-04), execution of every Phase 1 construct in an independently extracted interpreter (FSEM-05), general Source-to-Core/target refinement (FSEM-06), or normative graduation (FSEM-07). Root residue validity and authorized disposal remain explicit external premises.
