# FSEM-02 — outcome-labeled paired two-step replay (bounded v1)

**Non-normative; FSEM-02 remains open.** [Tracking #1613](https://github.com/abiggerhammer/phil/issues/1613). This extends the independently admitted [Ping/Choice family envelope](formal-semantics-paired-source-family-envelope-fsem02-v1.md) with a *sequential* finite Rocq model. It deliberately does **not** certify one source program executing Ping then Choice.

## Transition and outcomes

An explicit request contains a tagged family (Ping/Choice), separately supplied source and rendezvous admission Booleans, two typed session heads, action/choice/peer labels, named predecessor and successor endpoints, and two full abstract resource contexts. The second step is applied to the **actual first-step successor contexts**, not the original inputs:

```text
step(R1, C0) = None           => FirstRefused(C0)
step(R1, C0) = Some(C1)
  step(R2, C1) = None         => SecondRefused(C1)
  step(R2, C1) = Some(C2)     => BothAccepted(C1, C2)
```

This deterministic computation is a bounded **two-step observation**, not a global scheduler, complete evaluator, or source operational semantics. The three outcomes distinguish which model step refused. A second refusal preserves the exact committed first-step contexts, without silently rolling them back.

`proof/Phil/Core/FSEM02PairedTwoStepOutcomes.v` proves the three exact outcome equivalences, four independent source/rendezvous admissions for two successes, no rollback after second refusal including a mismatched action-family guard, and conditional two-step preservation of *both entire* loan functions plus arbitrary unrelated linear spectators on both peers. The latter requires separate typed continuing-head/choice-arm premises for **each** step and disjointness from the four predecessor/successor names on each peer.

## Production executable source controls

The strict focused Haskell/GHC 9.6.7 `-Wall -Werror` preflight reruns the actual `test/Phase1FSEM02ProtocolProgressionMain.hs` and `test/Phase1FSEM02SourceJointChoiceMain.hs` suites. These execute complete accepted Ping, Go, and Cancel source fixtures and minimally rejected cases: `test/fixtures/fsem02-protocol-progression-v1/stale-close.phil` must produce the exact `GrammarV1ComponentSendCloseCloseMismatch` source rejection, while Choice wrong-body and missing-arm cases retain their production rejection classes. The native suites also check exact predecessor consumption, loan spectators, local/joint Core successor equality, refusals, and replay. **These are separately checked source programs, not a newly implemented mixed-family source witness.** The Rocq 9.2 job compiles the imported Ping/Choice bridges and this new module, forbids `Admitted`, `Axiom` or `Parameter` in the new module, and hashes compiled proof evidence.

## Trust premises and open obligations

Source-acceptance flags do not establish source-derived session activation or `ConcurrencySemantics.RendezvousValid`. Nominal protocol instance, role/peer selection, selected roots, ownership, disposal, assurance and authorization remain external inputs and obligations. The finite two-step proof does not establish native `TyEndpoint` equality to proof-side `SessionStep.endpointType`, universal Haskell `Map`/`Set` to Rocq `Context` refinement, exact native diagnostic simulation, Phase 1 fairness/progress, FSEM-05 completeness, or a single combined source program. These are deliberately unproved, not silently discharged.
