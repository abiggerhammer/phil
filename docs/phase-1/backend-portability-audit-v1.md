# Phase 1 backend portability paper audit v1

## Status

Paper design audit, 2026-09-03. This is roadmap pressure, not a Phase 1 backend implementation requirement.

Targets examined:

- conventional `wasm32` WebAssembly, with host/WASI facilities treated as explicit imported environment rather than ambient language authority;
- EVM;
- Solana/SBF.

The audit asks whether one checked Phil Architecture/Core program can be realized through the current Systems/StageContract vocabulary without importing a target's programming model into Phil Core or silently weakening source semantics.

Status vocabulary:

- **green** — current abstraction already has the right shape; a target profile/refinement is sufficient;
- **yellow** — current architecture has a place for the fact, but a still-open Phase 1 semantic obligation or an explicit target-profile relation must close before a backend may certify;
- **red** — current Core/Systems abstraction cannot express the target faithfully without redesign.

## Result

**No red architectural blocker was found.**

One proof-layer target leak was found and generalized as part of this audit: `PHIL-SYS-RUNTIME-GRAPH-001` had imported LLVM linker-symbol identity as its SYS-016 primitive-identity predecessor. Production Haskell was already expressed in terms of `RuntimePrimitiveProfileRef`. The generalized proof predecessor is now `PHIL-TARGET-RUNTIME-PRIM-001`, in which a target-visible entry is derived from physical primitive/profile identity and may later refine to an LLVM symbol, WebAssembly import/function/table identity, EVM opcode/precompile/runtime entry, SBF syscall/CPI target, or another target-specific representation. `PHIL-LLVM-RUNTIME-SYM-001` remains the LLVM instantiation and additionally owns LLVM call-site multiplicity.

The remaining yellow items are mostly obligations already present in the Phase 1 roadmap rather than newly discovered architecture work.

## Cross-target audit matrix

| Concern | wasm32 | EVM | Solana/SBF | Phil authority / required closure |
| --- | --- | --- | --- | --- |
| Source semantic identity vs physical representation | green | green | green | Architecture/Core identity plus Systems realization already separate semantic identity from pointer/handle/storage/worker identity. |
| Runtime primitive / backend entry identity | green after this audit | green after this audit | green after this audit | `PHIL-TARGET-RUNTIME-PRIM-001`; target-specific entry refinement remains profile evidence. |
| Storage / memory realization | green/yellow | green/yellow | yellow | MEM realization already makes physical storage strategy nonsemantic. Target layout/capacity/failure facts remain profile/partiality obligations. Solana additionally needs explicit runtime account-graph binding discipline. |
| Sequential evaluation order | yellow | yellow | yellow | `PHIL-EXEC-ORDER-001` must be complete before backend translation can claim source-order preservation. |
| Fixed-width arithmetic | yellow | **yellow, high pressure** | yellow | `PHIL-EXEC-ARITH-001`. Plain Phil arithmetic must not inherit WebAssembly/SBF machine overflow or EVM modulo-2^256 behavior. |
| Target trap / UB / capacity failure | **yellow, high pressure** | **yellow, high pressure** | **yellow, high pressure** | `PHIL-SYS-PARTIALITY-001`. Bounds traps, gas/CU exhaustion, stack/call-depth limits, memory/account capacity, and other target-only failure must be mapped, proved unreachable, runtime-bound, assumed/exported explicitly, or reject realization. |
| Ambient environment / nondeterminism | green/yellow | **yellow, high pressure** | yellow | `PHIL-EXEC-AMBIENT-001`. Wasm core has no ambient host access, but imports still need explicit provider/authority binding. EVM environment opcodes and Solana sysvars/invocation context may not become implicit Phil observations. |
| Effect subject preservation | yellow | yellow | yellow | `PHIL-EFFECT-SUBJECT-001` and `PHIL-EFFECT-POLY-001` remain open. Target calls/imports/storage effects must retain exact semantic subjects. |
| Host/external calls | green/yellow | yellow | yellow | Providers/boundaries/callables plus StageContract can represent target calls. Backend-specific call semantics must not add authority/effects/failures silently. |
| Reentrancy / nested external invocation | not inherent to base profile | **yellow target-profile obligation** | yellow target-profile obligation | EVM external calls can permit reentrant invocation; certification must either model the nested invocation relation or establish a target obligation that excludes/unobservably contains it. Solana CPI has its own bounded invocation/privilege rules. No implicit peer/process transition is allowed. |
| Authority / capability | green/yellow | yellow | green/yellow | Existing explicit authority/provider/deployment relations fit. Wasm imports, EVM caller/value/context, and Solana signer/writable/owner/PDA facts need exact profile bindings; mere target availability is not Phil authority. |
| Physical concurrency / scheduling | green for initial single-threaded profile | green at one execution-frame level | green/yellow | `PHIL-CONC-LOWER-001` already separates ProcessKey from worker/task identity. Solana account locking/transaction scheduling is realization/platform behavior unless explicitly promoted into source semantics. |
| Persistent target state | green | green/yellow | green/yellow | Semantic storage resources can lower to target storage strategies. EVM storage-slot addressing and Solana data-account mapping remain representation/profile facts, not semantic identity by coincidence. |
| Cost / metering | green/yellow | green/yellow | green/yellow | Existing contribution→charge lineage and profile-selected cost shapes can host Wasm fuel/operation models, EVM gas, or Solana CUs. Exact numeric/profile truth remains target evidence. |
| Target strengthening | green | green | green | SYS-014 already converts target-only stronger facts into explicit derived obligations instead of retroactive source assurance. |
| Backend competence export | green | green | green | SYS-019 `NextStageRequirement` already forbids replacing exact requirements with “native ABI”, platform defaults, or compiler folklore. |
| Artifact/deployment qualification | green/yellow | green/yellow | green/yellow | Existing StageContract plus deployment qualification is structurally sufficient; concrete engine/chain/runtime/toolchain evidence remains target-specific. |

## WebAssembly paper realization

### Proposed mapping

- A Phil `ProcessOccurrence` maps to one or more WebAssembly function executions under the existing execution-realization relation. Function index or physical worker identity never becomes `ProcessKey`.
- Phil semantic storage/resources map to selected WebAssembly linear-memory regions, globals, tables, host-managed objects, or explicit imported storage providers. Byte offsets and memory indices are representation metadata unless an exact source contract makes them semantic.
- A reusable runtime primitive maps through `PHIL-TARGET-RUNTIME-PRIM-001` to an exact WebAssembly target entry: e.g. an imported function identity, defined function identity, table/reference entry, or other selected profile object.
- Host interaction is an explicit provider/boundary/authority relation. Core WebAssembly's lack of ambient host access is a particularly clean fit: imports do not acquire Phil authority merely because the embedder supplies them.
- Bounds checks, invalid indirect calls, explicit traps, `memory.grow`/table growth failure, engine/profile capacity, and analogous lower-level partiality are handled by `PHIL-SYS-PARTIALITY-001` rather than becoming source failure accidentally.
- Target cost uses ordinary Systems cost contribution/charge lineage. A profile may supply fuel or another accounting model, but no universal Wasm cost model is assumed.

### Remaining yellow conditions

1. complete `PHIL-SYS-PARTIALITY-001`;
2. complete source arithmetic/order semantics before selecting WebAssembly integer instructions;
3. define a first `wasm32` profile for linear-memory representation, bounds/alignment, target entry identity, import/export capability binding, tables/references, memory growth, and cost;
4. require all host/WASI functions used by lowering to be exact provider/authority/effect bindings rather than ambient imports.

No Core redesign is indicated.

## EVM paper realization

### Proposed mapping

- One source process execution maps to one EVM execution frame or an explicitly related set of frames. EVM program counter, stack slot, memory offset, storage slot, code address, and call-frame identity remain target representation unless explicitly tied to a Phil semantic subject.
- Persistent Phil storage can realize into contract storage; transient values can realize into stack/memory/calldata-compatible target representations. Storage-key/address mapping is an explicit target representation relation, not semantic identity by equal 256-bit value.
- Runtime primitives can refine to EVM opcodes, precompiles, generated helper sequences, or explicitly called runtime contracts through `PHIL-TARGET-RUNTIME-PRIM-001`.
- Gas cost fits the existing contribution/charge graph structurally. Dynamic gas truth and gas schedule revision are target-profile evidence.
- External calls are explicit provider/boundary/callable effects with exact failure/authority/cost lineage.

### Remaining yellow conditions

1. **Exact arithmetic must land before serious EVM lowering.** EVM's native 256-bit word arithmetic must never define plain Phil overflow/wrap semantics. Checked or proved range obligations remain Phil authority.
2. **General partiality must land.** Out-of-gas and every other reachable target exceptional halt must be explicitly accounted for.
3. **Ambient environment must be closed.** Caller, call value, block/transaction environment and similar EVM observations may enter only through explicit Phil entry/provider/capability relations.
4. **Reentrancy requires an explicit profile rule.** An external call may permit a nested invocation before the original source call returns. A certified lowering must either represent the nested invocation in an admitted source/architecture relation or establish an exact target obligation preventing it from changing Phil-visible behavior. Treating the EVM call as an ordinary atomic source call without such evidence is invalid.
5. Storage layout and external-call ABI details remain `NextStageRequirement`/target-profile facts.

No Core redesign is indicated; the reentrancy issue is a realization obligation, not a reason to import EVM call semantics into Phil Core.

## Solana/SBF paper realization

### Proposed mapping

- A Phil process invocation maps to one SBF program instruction execution or an explicit many-to-many physical realization. Validator scheduling/thread identity remains nonsemantic.
- Program code is separate from mutable state; Phil semantic storage/resources map to explicit data-account relations or provider-backed account operations.
- Account pubkeys, owners, signer/writable flags, PDA derivation facts and account data are exact invocation/realization facts. Equal addresses or handles do not by themselves collapse Phil semantic subjects.
- Signer/writable privilege fits Phil's explicit authority model. CPI must retain exact passed authority and may not manufacture stronger authority from target convention.
- Syscalls and CPI targets refine `PHIL-TARGET-RUNTIME-PRIM-001` entries; claim sets and assurance revisions do not rename them.
- Compute units and account/data costs fit the profile-selected contribution/charge model.

### Remaining yellow conditions

1. complete `PHIL-SYS-PARTIALITY-001` for compute-budget exhaustion, call-depth/invocation limits, account/data capacity failures and other target-only failure;
2. complete arithmetic and effect-subject semantics before relying on SBF machine operations;
3. define an **account-graph binding profile** that clearly separates:
   - compile-time Architecture/Realization identity;
   - runtime-supplied account addresses and account-data subjects;
   - signer/writable/owner/PDA evidence;
   - explicit source semantic identity.
   A runtime account pubkey must not accidentally become `ArchitectureRealization` identity merely because it is physically selected for one invocation, unless the source contract actually makes that account identity semantic;
4. define CPI preservation for authority, effects, failures, cost and nested invocation depth;
5. keep account locking and validator scheduling at the realization/platform layer unless a source assurance claim explicitly depends on them.

No Core redesign is indicated. The account-graph distinction is the main Solana-specific profile pressure discovered by the audit.

## Required Phase 1 closures before backend implementation

This audit does **not** add new Exit cases. It raises the portability importance of already-open obligations:

1. `PHIL-EXEC-ARITH-001` / EXEC-007–009;
2. `PHIL-EXEC-AMBIENT-001` / EXEC-011;
3. `PHIL-SYS-PARTIALITY-001` / EXEC-012–013;
4. `PHIL-EFFECT-SUBJECT-001` and `PHIL-EFFECT-POLY-001` / EFF-001–005;
5. completion of deterministic sequential execution/binding semantics where backend translation depends on them.

The new `PHIL-TARGET-RUNTIME-PRIM-001` seam should be re-certified together with the existing Systems runtime graph before Phase 1 freeze. Target-specific WASM/EVM/Solana refinements remain later-backend work and do not expand the Phase 1 exit-gate matrix.

## Conclusion

The current Architecture/Core/Systems split survives all three paper realizations. The important property is that target awkwardness consistently lands in **realization, target strengthening, next-stage requirements, partiality, authority/effect binding, or profile evidence** rather than forcing target concepts into Core.

The only concrete target leak found in an already-Certified generic proof was LLVM linker-symbol identity inside the Systems runtime graph. This audit removes that leak by interposing the target-neutral runtime primitive identity relation.

Freeze criterion from this audit: no Phase 1 semantic rule should require native pointers, linker symbols, an unrestricted/native address space, ambient host/chain authority, target-native wraparound arithmetic, or undeclared target traps in order to state ordinary Phil semantics.
