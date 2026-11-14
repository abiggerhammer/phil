# P8/P9 autonomous proof-lane coordination — 2026-11-14

## Authorization and scope

Maintainer request: establish **two distinct finite proof-development lanes** for
[accepted-domain P8 representation](https://github.com/abiggerhammer/phil/issues/1770)
and [P9 predecessor evidence/assumption authority](https://github.com/abiggerhammer/phil/issues/1771)
under the controlling [#1584](https://github.com/abiggerhammer/phil/issues/1584).
[P10 final certification](https://github.com/abiggerhammer/phil/issues/1772)
**remains blocked on both**; this is NOT authority to derive
`FinalArtifactCertified`, modify release bytes or declare Phase 1 frozen.

| Lane | Branch prefix | Required PR label | Controlling issue | INITIAL finite budget |
|---|---|---|---|---|
| P8 | `hamster/p8-representation/` | `lane: p8-representation` | #1770 | **at most 2** focused PRs |
| P9 | `hamster/p9-evidence/` | `lane: p9-evidence` | #1771 | **at most 2** focused PRs |

Each lane may have **at most one active PR**. Avoid colliding with itself,
the other new lane, existing `lane: rocq-refinement` surface proof work,
the FSEM-01 pair-programming claim and FSEM-02 semantics worker, and the
completed P11 release-audit tranche. No P8/P9 worker may claim FSEM-01/02
coord refs or use FSEM label/branch. No P10 work may claim predecessors complete
before actual exact evidence. No new native `impl-audit` scope is authorized
by these lane labels; #1584's previous budgets remain historic and spent.

### First budgets and work products

**P8 PR1/2:** At a fixed `main` snapshot, enumerate all accepted-domain
native values and exact Haskell ↔ Rocq semantic contracts needed for P10,
including genuinely recursive `SemanticForm`, Haskell Unicode `Text`,
canonical `Map`/`Set` ordering and typed source/stage/release fields.
Add executable discrimination tests or mechanically checked narrow facts where
safe. The inventory must name gaps *without* treating the old ASCII-7 / atom
diagnostics as complete accepted-domain mapping. **P8 PR2/2** may implement one
coherent candidate exact representation/codec and genuine proof/negative
controls *only if* no TCB or admissible-language change is needed. A faithful
partial slice is welcome, but must be labeled **partial**. Stop on an actual
unsupported accepted input, collision, or authority decision.

**P9 PR1/2:** At a fixed `main` snapshot, make a complete native event/
producer/consumer ledger for source evidence, same-event final evidence use,
complete SYS-012 erasure later-consumer domain and immutable SYS-013 assumption
binding/discharge. Retain permanent negative witnesses: two actual consumers
with one supplied; same event metadata but no actual final use; assumption
scope/digest/subject mismatch. **P9 PR2/2** may add one smallest actual
checked producer→consumer binding, with concrete Upload/Steve success and
negative tests, *only if* it preserves Phase 1 semantics and accepted policy.
Do not claim general completeness from a caller-supplied map, record, or
conditional Rocq `Prop`. Stop on an unresolvable competent-producer gap.

Both lanes need a **clear executed exact evidence ledger** and next-tranche
gap list after their two PRs; no authority to start PR3 without review.
Discovery may identify an earlier meaningful stop. Do not use extra PRs merely
to fulfill a numerical budget. Ordinary red CI can be repaired on the
**same** existing PR/head/branch and does not use an extra slot.

### Exclusive ownership by path / symbol

**P8 owns NEW paths** named `P8*`, `p8-*`, or `p8_` under
`proof/Phil/Verification`, `src/Phil/Verification`,
`test`, `docs/phase-1`, and `audit` for representation and concrete
coders. Existing `NativeFinalInstanceTypedCorrespondence.v` and
related shared P7 objects are **read-only inputs during PR1**.
P8 must request an explicitly assigned shared-file slice before
changing those accepted production paths or any common `FinalManifest*` proof.

**P9 owns NEW paths** named `P9*`, `p9-*`, or `p9_` under
`proof/Phil/Assurance`, `src/Phil/Assurance`,
`src/Phil/Systems`, `test`, `docs/phase-1`, and `audit`.
Existing `EvidenceErasure`, `AssumptionDependency`, ManifestClosure,
and P7 final-claim modules are **read-only inputs during PR1**.
P9 may request explicit ownership before changing a shared accepting path,
even if it appears disjoint from the literal P8 filenames.

The two lanes must not modify `proof/Phil/Surface/**`,
`proof/Phil/Core/FSEM*`, FSEM claim coordination, `src/Phil/Core/FSEM*`,
`scripts/release/**`, release or notarization workflows,
`scripts/mhb_lint.py`, auto-PR/merge intent workflows or the 244
normative conformance cases. Those shared/source authority changes require
a **new reviewed coordination decision**, not a workaround.

### Published PR / CI / safety contract

The existing PAT-backed hamster auto-PR bridge recognizes only the explicit
new prefixes; it creates the two exact native lane labels on first use.
Every PR must be **created from a prepared first content commit directly
from exact current `main`**, not a temporary branch at `main`
that accidentally uses the previous FSEM/P11 commit's title. The branch
must contain its exact issue reference, claim boundary and test evidence,
and receive exactly one native lane label.

Keep the existing merge workflow's exact tested head, branch-prefix/label
match, complete strict check-run census and allowed lone provenance-verified
nonrequired INT-011 `publish` skip (no other skip), no review blockers
and no overlap with intervening `main` files. Since GitHub REST compare
caps file lists at 300, explicitly compare **every PR path blob SHA**
between base and live main if needed. Merge *only* via
`hamster/merge/<lane>/pr-<number>/<exact-head>` from current main,
never GitHub direct merge API. Confirm actual merge commit and complete
current state on GitHub. Runs in parallel may increase runner pressure;
do not cancel other lanes' jobs. If a workflow fails with a real theorem
counterexample or proof ownership conflict, stop with the exact error,
do not weaken the theorem or skip checks.

Rocq must run **version 9.2.0** with full compiled dependency closure,
`Print Assumptions`, recursive checker evidence and negative controls.
GHC must use `-Wall -Werror`, LLVM/target assumptions remain the
declared Phase 1 TCB; no `Admitted`, new axioms, artificial nat encoder,
diagnostic-only acceptance masquerading as full representation,
caller-provided `Prop` promoted to accepting authority,
or silent language/TCB narrowing.

### Exit and review

For both lanes: **max 2 PRs, then pause** for exact maintainer review.
For P10: **do not enable/start** until P8 and P9 have actually proved the
needed P10 inputs and their competent native origins. Proof-only partial
progress never marks the full P8 or P9 issue closed. The P11 independently
reviewed, signed/notarized release candidate and checked producer→shipped
executable byte provenance remain separate gates. #1584 and #1736 OPEN;
`FinalArtifactCertified` UNPROVED; Phase 1 freeze NOT YET.
