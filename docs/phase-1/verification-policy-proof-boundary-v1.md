# Verification policy proof boundary v1

`PHIL-VERIFY-POLICY-001` certifies the policy-controlled disposition layer that follows intrinsic acceptance and proof-production attempts.

The proof composes two already-Certified predecessor boundaries:

- `PHIL-VERIFY-WORKFLOW-001`: intrinsic rejection is terminal, intrinsic acceptance fixes the verification workflow and policy input, and the canonical obligation graph supplies exact semantic targets.
- `PHIL-VERIFY-PRODUCER-001`: replaceable proof production is not evidence authority, and timeout/failure/unknown/refusal/checker rejection remain unresolved rather than changing proposition truth.

## RuntimeBound

VER-007 admits `RuntimeBound` only after independent gates establish:

1. the exact obligation revision exists and is inside certification scope;
2. the obligation acceptance rule admits `RuntimeEnforced` under the exact evidence role;
3. the runtime mechanism is complete;
4. failure/resource residue is explicit and nonempty;
5. cost references are present and known;
6. the competent runtime-evidence authority accepts the candidate; and
7. the selected assurance policy explicitly permits `RuntimeBound`.

Policy is therefore a closure-stage gate, not a repair mechanism. A policy that rejects `RuntimeBound` leaves the same exact semantic target open for another closure path. Changing only policy identity does not re-key the source/obligation target.

The imported workflow theorem also makes the stronger boundary explicit: no runtime disposition can turn intrinsic source rejection into acceptance.

## AssumptionDependent

VER-008 admits an assumption boundary only for an explicit proposal whose:

- obligation revision is exact and in certification scope;
- role is the exact assumption-boundary role accepted by the obligation rule;
- ADR-010 assumption record is content-bound;
- assumption identity is explicitly permitted by the verification context;
- declared validity dimensions match the effective context; and
- selected assurance policy permits `AssumptionDependent`.

Missing proof evidence by itself is never an assumption proposal.

## Exported

VER-008 represents export structurally through ADR-010 `ExportEntry`, rather than inventing an assurance kind for export. An export proposal is admissible only when:

- it names the exact obligation revision;
- that obligation is outside the certification scope being closed locally;
- the export entry is content-bound;
- the destination boundary is present and explicitly permitted;
- declared validity dimensions match the effective context; and
- selected assurance policy permits `Exported`.

An in-scope obligation cannot silently become an export.

## No silent disposition

The decisive no-inference rule is independent of policy permissiveness: **no explicit boundary proposal means the missing proof remains unresolved**. This remains true after a replaceable producer fails. Assumption and export paths begin only from explicit boundary proposals and then pass their own competence gates.

## Executable correspondence

`VerificationPolicyImplementation.v` reflects the finite VER-007/008 boolean/equality gates into the semantic predicates in `VerificationPolicy.v`:

- runtime target/scope/acceptance/mechanism/residue/cost/authority/policy gates;
- assumption target/scope/role/acceptance/content/permission/validity/policy gates;
- export target/scope/content/destination/validity/policy gates; and
- the policy-independent unresolved result for the no-proposal case.

The dedicated workflow compiles the Rocq semantic and implementation proofs, rebuilds the complete Haskell substrate, strict-typechecks the two production modules and each VER-007/008 test executable separately, replays the unchanged VER-007 and VER-008 corpora, and reruns predecessor verification/assurance controls.

## Explicit TCB and representation boundaries

This proof does **not** re-prove concrete Haskell representations. The following remain explicit predecessor or trusted representation boundaries:

- `Text`, `Digest`, `RevisionId`, `Data.Map`, and `Data.Set` representation and ordering;
- canonical obligation-graph hashing and revision identity;
- ADR-010 `Assumption` / `ExportEntry` digest derivation and validity-map representation;
- concrete `RuntimeMechanism` field representation;
- the extracted runtime-evidence authority kernel and its extraction/toolchain correctness;
- GHC/runtime correctness; and
- the correspondence from concrete Haskell equality/membership checks to the normalized facts reflected by the Rocq implementation proof.

Cache layout, proof-search scheduling, and the choice of replaceable proof producer remain nonsemantic.
