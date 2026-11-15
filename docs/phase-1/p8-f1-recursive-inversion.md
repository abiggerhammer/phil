# P8-F1 — exact canonical inversion proof development

Owner: \`lane: p8-representation\`, controlling [#1810](https://github.com/abiggerhammer/phil/issues/1810). This is a NEW F1 tranche, not a renewal of E1/E2 or the unused C3 slot.

## What is independently checked in this initial code

The executable \`p8_e1_count_scan\` is proved to consume any *already started*, entirely decimal digit suffix, preserving the exact caller-provided remainder and computing the unbounded base-ten accumulator. The canonical-first-digit lemma proves the real scanner accepts precisely framed nonempty numeric fragments when there is no forbidden leading zero. The actual E1 decimal emitter is separately shown to emit only decimal octets, with no invented Text-as-nat identity. These are mathematical inversion prerequisites; they are **not** the requested final universal numeral/frame and recursive form inversion.

The new native differential tests (GHC 9.6.7 \`-Wall -Werror\`) run the unchanged real codec against deep finite recursion, decimal boundaries, strict Unicode and D/V/Q/M typed applications, and reject independent malformed and duplicate wires. A finite test is never generalized to arbitrary native Haskell library semantics.

## Completion gate — not yet discharged

Before this PR is eligible for merge it **must additionally prove**:

1. Every finite natural \`n\` satisfies \`p8_e1_read_count (p8_e1_frame_count n ++ suffix) = Some (n,suffix)\`, and framed valid D1 UTF-8 text has the exact prefix inverse.
2. A proved parse-fuel bound for every D2-valid finite nested form/fields, and a mutual prefix/remainder inversion of actual \`p8_e1_put_form\` with \`p8_e1_parse_form_fuel\`.
3. Universal \`p8_e1_decode_form (p8_e1_put_form f) = Some f\` on \`p8_d2_valid_form f = true\`, injectivity and no-trailing, no silent set/map normalization.
4. Full exact-head Rocq/GHC CI, \`Print Assumptions\`, recursive \`rocq check\`, disjoint-path and protected merge authorization.

If a universal lemma is false, retain genuinely proved partial results but **stop without merging or relabeling E2 conditional soundness as inversion**, and record the minimum counterexample on #1810/#1770/#1584.

## Authority boundary

No general Haskell \`Data.Text\` / derived \`Ord SemanticForm\` / \`Map\` / \`Set\` semantics, accepted object bridge, immutable P9 admission or P10 whole-final-release certificate is proved here. No native source, TCB, FSEM, P9, existing P8, normative case or privileged CI file was edited.
