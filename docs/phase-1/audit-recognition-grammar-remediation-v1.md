# Phase 1 recognition-grammar audit remediation

**Finding:** `PHIL-AUD-RECOGNITION-GRAMMAR-001`  
**Audit event:** `PHIL-AUDIT-20260921-RECOGNITION-GRAMMAR`  
**Original review pin:** `1d6f8463942253664bed5b911ffa3170ab928069`

## Defect

The operational nonlegacy Surface recognition path accepted `recognize G from raw` without requiring `G` to equal the grammar carried by the pending raw receive.

Core recognition witnesses already bind the actual pending owner, grammar and frame, but Surface retained the source-requested grammar as a second independent coordinate. A mismatched request could therefore obtain a coherent witness for the real ingress grammar while `.value` projection interpreted the same result using the different requested grammar. Commit then used the real Core witness and could still succeed.

The legacy raw path already rejected this mismatch with `RecognitionProvenance`; the missing relation was specific to `PendingRawShape`.

## Repair

`evalRecognize` now checks the requested `GrammarId` against `rawGrammarId rawView` before constructing either the success or failure recognition outcome. A mismatch is rejected as `RecognitionProvenance` before a Surface recognition decision exists.

The existing Core owner/frame/loan checks remain unchanged. Matching recognition still produces the same Core witness, and downstream projection and commit therefore share one validated grammar authority.

## Permanent replay

`test/Phase1AuditRecognitionGrammarMain.hs` replays Astra's r01-r10 corpus through both `checkSurfaceComponent` and the public `verifySurfaceApplication` boundary:

- matching Hello and Begin recognition, semantic projection and commit remain valid;
- Hello→Begin, Begin→Hello and unrelated-grammar requests reject before projection or commit;
- genuine Hello still rejects Begin-only `.length` projection;
- the legacy matching and mismatch behavior remains unchanged; and
- raw byte views remain non-projectable before recognition.

The cases create ordinary grammar-backed endpoints in the declared Surface environment and obtain pending/raw/witness state through the real `receive_frame` → `borrow` → `recognize` path; they do not inject `PendingRawView` or `ParsedWitness` fixtures.

The dedicated workflow also replays intrinsic-invalidity and frozen Surface conformance, including the ordinary Upload server recognition path.

## Assurance boundary

This closes only the implementation/public-consumer grammar-selection slice. It does not alter Core's trusted recognition-result construction contract, prove parser execution over native bytes, close recursive session-continuation findings, establish a new Rocq theorem, change LLVM/runtime recognition, or promote Certified status. Final frozen-delta review remains separate.
