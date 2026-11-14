# P9-E1: original ordinary source-checker evidence observations

**Control:** [#1771](https://github.com/abiggerhammer/phil/issues/1771#issuecomment-6878199353). **Status:** real native checker-instrumentation slice; not source/Core sealed authority, not final evidence use, and not P9 discharge.

The new `checkSurfaceComponentWithEvidence` invokes the *same original* checked preflight and successful Surface checker transition as ordinary `checkSurfaceComponent`. It observes actual successful checked `ValueResult.valueResultEvidence` before the old `applyValueResult` state-only projection, actual `checkRequirement` on select/receive-exact, `evalProve` focus and checked decisions, and real CALL-019 `checkCallableDecisionArm` residual evidence. Each typed evidence-use occurrence carries its checker site span, source static arm route, and sequential event ordinal. Multiple checked static `decide` / `offer` branches are preserved across `joinMetadata` resource joins and stopped path finalizations. A statically checked branch is NOT a report of runtime execution. Zero evidence uses is NOT proof of selected final use.

The event data types have public constructors for observation/test discrimination and **cannot mint authority**. E2 must bind the complete per-source-site graph and source/Core correspondence from the actual rechecked raw source into the private P2 and both P6 StageClosure arms; E3 must require genuine final consuming use in P7. This slice does not connect those producers, and does not establish complete SYS-012 later-consumer universe nor SYS-013 immutable assumption selected provenance.

The dedicated P9 workflow typechecks actual instrumented source with GHC -Wall -Werror, runs the native positive/negative branch and proof tests, and preserves existing accepted Surface proof/branch tests. It does not modify Grammar-v1/TCB, the 244 normative conformance cases, signing/release workflows, P8/Rocq/FSEM claims or other lanes.

**Remaining E1 completeness gate:** inspect every accepted proof/evidence site, branch/loop/callable alternative, ordinal reuse across an actual joined path, and exact concrete Upload/Steve evidence-positive source examples. If the sample native suite finds lost real use events, fix this *same PR* and re-run full CI; do not call it complete or advance E2 before that test evidence exists.


## Acceptance-site inventory increment (same E1 branch)

At the source Engine, distinct admitted uses cannot be exhausted by the two Core
`checkValue` calls. This E1 path also observes successful
`PrimitiveConsumeBeginPolicyEvidence` using the exact checked policy binding
and type, and successful `evalCommit` consuming a parsed-receive witness
(the pending endpoint, actual parsed shape and named witness when available).
A rejected/mismatched policy binding or parsed provenance cannot produce
an accepted event. These are *local checked semantic-use observations*, not
P7/whole-release evidence, and the parsed-evidence shape is not an authority
token or assertion of dynamic execution.

In the current checker the decision to introduce `TyValidated` evidence in
`evalValidate` or proof binders in `bindDecisionPattern` is an *evidence
producer*, not automatically proof that the evidence was later consumed.
Ordinary `evalSend`, callable argument flow, generic primitives and ambient
unrestricted reads similarly need occurrence-level classification before a
complete semantic-consumer domain can be claimed. Successful local checking
by itself must never be turned into an asserted P7 final use. The Core
`ValueResult` lists already remove repeated identical `EvidenceUse` records
within one Core result (`appendEvidenceList`), so this E1 observer faithfully
retains the resulting checked occurrences but cannot reverse that upstream
deduplication; whether a stronger per-internal-use representation is necessary
remains an explicit source/Core semantic question for a separate review.

Current native tests cover the *actual parsed production checker*, a
successful actual Core value-check use, different Core uses in statically
checked branches after a join, sequential source occurrence ordinals, named
and rejected proof, empty-use separation and an accepted primitive policy
consumption. The original EXEC-015 omission fixture was updated to initialize
the three new observation-only fields under strict `-Wmissing-fields`.
The original 244 normative rows, Grammar-v1, TCB and publication workflows
remain unchanged.

**Completeness gate remains OPEN** until all accepted evidence-use routes,
including parsed commit and higher-level source-owned use correspondence, are
checked by real positive and negative tests. E1 observations by themselves
cannot authenticate the P2 same checked-source event; E2/E3 and SYS-012/013
are separately unproved.

**Real source fixtures:** The E1 native suite now parses the actual
`examples/upload/server.phil` and requires the two independently checked
`commit_receive` events for `pendingHello` and `pendingBegin`, including
their nested static branch routes, and parses `examples/upload/client.phil`
to require its successful `prove` event. The dedicated P9 workflow also runs
the already-authoritative ordinary Steve SourceBundle/provider acceptance
regressions. These tests do not invent evidence events, and their success
means only real Surface checking/observation, **not** the future P2/P6/P7
source-rechecked authority closure. Hosted CI and full census must pass on
the final exact HEAD.

## Actual accepted-checker use-site inventory (E1 review)

This audit distinguishes **use** (recorded only after the corresponding actual
successful check) from a **producer** of candidate proof/validation data.
Current production `Engine.hs` observation call paths are:

| Actual accepting path | Observable checked event | Does it assert runtime execution? |
| --- | --- | --- |
| `evalAccept → checkValue → applyValueResult` | Each returned `ValueResult.valueResultEvidence` as `SourceCoreValueEvidence` | No |
| `evalSelect → checkRequirement` per configured selected-branch requirement | `SourceRequirementEvidence`, including selected named binder or focused plan | No |
| `evalSelect → checkSelectedPayload → checkValue/Using → applyValueResult` | Actual checked payload `SourceCoreValueEvidence` | No |
| `evalReceiveExactWithBinding → checkConfiguredRequirement → checkRequirement` | Successful configured `SourceRequirementEvidence` for required byte count | No |
| `evalProve → focusProposition / solveRequirement` | `SourceProveEvidence` for each checked focused requirement (including whether a verified decision procedure was needed) | No |
| `checkCallableDecisionArm → checkObligation → exactEvidenceBinding` | Each independently discharged `SourceCallableResidualEvidence` | No |
| `evalPrimitive PrimitiveConsumeBeginPolicyEvidence` | Successfully checked exact `SourceBeginPolicyEvidence` binding/type | No |
| `evalCommit → parsed provenance / frame checks` | `SourceParsedCommitEvidence` for accepted source pending-frame/witness pair | No |

Each path is checked by the normal `checkSurfaceComponentWithEvidence`
transition. It does not use an independent proof fixture to mint an event.
`checkStatements`, `checkValueBlock`, `checkScopedValueBlock`,
`checkDecisionArm` and `checkOfferArm` traverse the actual alternatives;
`enterEvidenceBranch` attaches original static arm coordinates and
`joinMetadata` unions all surviving event histories rather than choosing
first-path metadata. The terminal paths are retained separately.

Classification of nearby paths that **do not by themselves consume a
selected proof**: `evalValidate` and `bindDecisionPattern` create
validation decisions/bindings; `evalRecognize` creates a parsed candidate;
`evalCallable` may create a decision with stated facts; `evalSend` performs
a checked payload move and protocol transition (it does not call
`checkValue` or the evidence checker); `evalClose` and `evalRelease`
enforce resource/protocol outcomes. All may be semantically important for
SYS-012, but E1 must not mislabel their successful checks as P7 evidence use.

**Known representation boundary:** `Core.Value.appendEvidenceList` already
deduplicates identical structural `EvidenceUse` entries inside a single
`ValueResult`. E1 faithfully observes the Core checker's actual returned
list, not an imagined internal un-deduplicated occurrence trace. Distinct
ordinary source sites and static branches remain distinguished in E1.
A stronger internal occurrence authority, if required by E2/P7, cannot be
inferred from that list without a separate competent producer decision.

The on-disk Upload source test now checks both real parsed commits **and**
the two distinct successful BeginPolicy selecting/receiving proof consumers,
including source sites and branch routes. A source-coordinate mutation test
ensures identical abstract proof use at a moved source site changes the
checker-event coordinate. These tests establish observational fidelity only;
they do not authenticate source unit identity, a complete SYS-012 consumer
domain, or final use in a certified release.
