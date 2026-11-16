# Phil Phase 2 — experimental engineering charter

**Opened:** 2026-11-16  
**Status:** Phase 2 experimental engineering enabled; **Phase 1 is not frozen**. This is a **non-normative planning charter**, not grammar/semantic authority, TCB modification, release authorization, or verification claim.  
**Tracking:** [PH2-00 #1830](https://github.com/abiggerhammer/phil/issues/1830) · [PH2-S00 #1831](https://github.com/abiggerhammer/phil/issues/1831) · [PH2-G00 #1832](https://github.com/abiggerhammer/phil/issues/1832)

## Thesis and boundary

Phil's architecture and accepted contracts are authoritative; compiler implementations are replaceable. Phase 2 progressively replaces the bootstrap Haskell compiler/checker with independently testable Phil-native stages, while realizing the *same checked meaning* on constrained 32-bit hardware.

Phase 2 may **prototype and verify in parallel** with Phase 1 completion, but must never use experimental success to discharge a Phase 1 proof, audit, authority, release-byte or freeze obligation. Specifically, outstanding P8/P9/P10/P11, implementation correspondence, source/semantics FSEM and independent final-delta review are separately tracked and decided.

**Provisional Phase 1 development anchor (not freeze):** `main@4c118882a186606a63b6607505aaccc73839ecba` at kickoff. Each experimental result names its own immutable exact-head, grammar/contract revision, verification profile, tooling and target inputs. Ongoing `main` commits do not silently update a result's authority.

## Authority/correspondence ladder

1. **Source authority.** The existing normative Phase 1 `grammar/phase1-surface.ebnf` determines syntax, not program validity. Accepted typing, ownership, session, effects, authority, assurance and resource obligations determine admissibility.
2. **Source → Core.** Recognition, elaboration, desugaring, binder/loan/outcome identities, error discrimination and semantic preservation require a separate proof/evidence boundary.
3. **Core → Systems / checked lowering.** Target-neutral meaning must survive explicit realization and provider selection. `InvalidPhil`, `Unsupported(reason)`, a lowering/compiler defect, a target toolchain failure, and a runtime/environment failure are **different** outcomes. Backend realizability must be explicit; do not silently coerce unsupported operations or promote a proposed backend-realizability ADR into authority.
4. **Systems → machine artifact.** Toolchain/ABI identity, memory widths/alignment, linkage, runtime/provider assumptions, artifact bytes and trust boundaries are named. Compilation success alone is not an execution/certification theorem.
5. **Self-hosting cutover.** Native stages are compared with the bootstrap Haskell implementation and the accepted conformance corpus, but Haskell is **not the oracle**. A self-hosted `philc` becomes production authority only after independent correspondence, checker/assurance evidence, reproducible build artifacts, and an explicit TCB/certification cutover review.

The accepted Phase 1 conformance set (currently tracked as 244 cases) is kept unchanged without its own explicit Phase 1 authorization. New Phase 2 experiments live in a separate test/documentation namespace; never reclassify existing non-normative examples as normative by implication.

## Two initial worktracks

| Track | Why it starts now | First bounded slice | First meaningful success |
| --- | --- | --- | --- |
| **PH2-S: Self-hosting** | Reduces Haskell bootstrap reliance | [S00 #1831](https://github.com/abiggerhammer/phil/issues/1831): inspect accepted bytes/ownership operations; implement one genuinely checked bounded byte substrate operation and its accepted/rejected witnesses | Reproducible actual source → checked Core → host result, or an exact documented missing contract and STOP |
| **PH2-G: Embedded** | Independently tests 32-bit portability and target assumptions | [G00 #1832](https://github.com/abiggerhammer/phil/issues/1832): XIAO ESP32-C3 RV32 toolchain, triple/data-layout/ABI/provider inventory and real compile/link probe | Pinned vendor toolchain and link evidence; real Phil path only to extent supported, with gaps clearly recorded |

**PH2-S progression (planned, not yet authorized for implementation):**

- S01: bytes/text, deterministic collections, diagnostics, canonical encoding, hashing and narrowly qualified I/O;
- S02: Phil-native Grammar-v1 recognizer/parser with positions and explicit rejection semantics;
- S03: elaborator and source-to-Core preservation, then Core checker;
- S04: assurance/certificate checking, Systems/lowering, hosted LLVM and minimal host I/O;
- S05: reproducible Phil-compiled `philc`, comparison to bootstrap, independently reviewed production authority/TCB cutover.

First bootstrap targets do **not** require networking, JSON, concurrency or regex. The separate [continuation-spine decision sugar commitment](surface-continuation-spine-sugar.md) remains an explicit future Phase 2 surface feature; it does not extend Phase 1 grammar or S00 semantics.

**PH2-G progression (planned, not yet authorized for implementation):**

- G00: prove toolchain/ABI **feasibility**, not hardware correctness;
- G01–G08: small RV32 realizations, checked provider boundaries, real physical execution, resource/environment envelopes and portable witness testing; the eventual weather-station witness can drive the examples;
- **G09/G10:** after independent Phil-native `philc` bootstrap/correspondence review, rebuild/re-certify the embedded path with that compiler. Early G00–G08 results receive **no final closure credit** until those later gates.
- Later candidates: web/phone server, Android SDK/FFI, OTA, FPGA hardware IR, Solana/EVM and richer stdlib. None are bootstrap gates.

The ESP32-C3 is a **RISC-V** target, not a generic Xtensa ESP32. The official ESP-IDF tool inventory names both `riscv32-esp-elf` GCC and optional `esp-clang`; G00 must *measure* selected target triple, data layout, ABI, linker assumptions, versions/digests, and real object/link compatibility instead of asserting them in advance. Flashing a board and collecting serial/runtime traces is a separate explicit gate.

## Development containment and CI

1. No modification to normative Phase 1 grammar, accepted semantics, final authority producers, StageContracts or existing required CI rules solely under this kickoff. Proposed language/TCB changes receive separate review and authorization.
2. A Phase 2 slice must define its one semantic owner, exact files/paths, baseline and source claims, expected behavior, accepted and rejected tests, named trust assumptions and STOP condition before code.
3. **One first PR maximum per S00/G00**. No silent expansion from feasibility work to full compiler, backend or hardware certification. If blocked by an unadmitted feature, stop and report its exact missing contract.
4. Do **not** activate seven workers or widen auto-PR/auto-merge lanes. [MHB-ATC #1602](https://github.com/abiggerhammer/phil/issues/1602) has manual single-slot admission foundations but live commissioning is outstanding; Phase 2 must use existing protected exact-head checks and avoid concurrent full CI fanout until its own policy is independently admitted.
5. Keep Phase 2 results distinguishable as `Experimental`, `Mechanized conditional`, `Native checked`, `Hardware observed`, or `Certified` with explicit evidence for each transition. Absence, skip, cancellation or stale checks is never green evidence.

## Exit matrix (per stage)

| Gate | Necessary evidence | Not enough by itself |
| --- | --- | --- |
| S00 accepted operation | Actual accepted source, checked Core path, explicit success and rejected counterpart | A Haskell-only function or a parser success |
| S00 host realization | Reproducible exact-source execution trace, target/toolchain identity, bounded semantics and failures | A screenshot or differential match with Haskell |
| G00 feasibility | Checked target identity, tool/SDK versions and digests, ABI/layout inventory, genuine compile **and link** output | An LLVM IR file or unrelated vendor hello-world |
| G01+ hardware execution | Checked source-to-artifact correspondence, exact firmware, board/environment record and physical trace | Compilable ELF without a flash/observe trace |
| Native `philc` authority | Independent cross-stage correspondence, certificate checking, TCB inventory, reproducible build and explicit adoption decision | Self-compilation or 100% differential test agreement |
| Phase 1 freeze | Separate closed Phase 1 release/audit/independent-review gates | Any success recorded in Phase 2 |

## First review decision

Adopt this charter as a **non-normative engineering plan**, then implement exactly S00 and G00 under their own issues. Review the initial execution evidence and CI capacity before authorizing more slices or any new autonomous hamster lanes. The Phase 2 charter neither authorizes nor blocks completion of the still-open Phase 1 obligations.

## References

- [PH2-00 tracking issue](https://github.com/abiggerhammer/phil/issues/1830)
- [S00](https://github.com/abiggerhammer/phil/issues/1831) · [G00](https://github.com/abiggerhammer/phil/issues/1832)
- [MHB-ATC admission](https://github.com/abiggerhammer/phil/issues/1602)
- [Phase 1 final-authority audit](https://github.com/abiggerhammer/phil/issues/1584)
- [Phase 2 non-normative Highwire conformance candidate](https://github.com/abiggerhammer/phil/issues/1803)
- [ESP-IDF stable ESP32-C3 setup](https://docs.espressif.com/projects/esp-idf/en/stable/esp32c3/get-started/index.html) and [tool inventory](https://docs.espressif.com/projects/esp-idf/en/stable/esp32c3/api-guides/tools/idf-tools.html)
