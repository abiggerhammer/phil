# PHIL-DATA-ID-001 — nominal data identity and non-inference proof

This proof certifies the Phase 1 nominal-identity boundary over the already implemented DATA-010 and DATA-011 slices.

## Certified semantic core

`proof/Phil/Core/DataIdentity.v` proves:

- two nominal declarations with the same checked shape remain distinct when their stable nominal keys differ;
- a nominal type is definitionally equal to itself;
- a transparent alias is definitionally identical only through resolution to its exact target;
- alias chains resolve transitively;
- alias presentation names do not create a new nominal identity;
- an empty data-operation contract grants none of equality, ordering, hashing, clone/default, serialization/deserialization, memcpy safety, or ABI compatibility;
- checked shape alone grants no operation;
- even definitional type equality does not itself grant any semantic or representation operation; and
- an explicit operation grant confers only that operation plus whatever the pre-existing contract already granted, so equality does not imply hashing/serialization and serialization does not imply ABI compatibility.

`PHIL-ARCH-ID-001` supplies the already Certified stable-declaration-key principle. This file treats the exact nominal key abstractly and proves the data-specific distinction/alias/operation layer rather than duplicating architecture revision semantics.

## Correspondence gate

The dedicated `Phase 1 Data Identity Proofs` workflow compiles the theorem under Rocq 9.2.0, records exact source and `.vo` identities, typechecks the unchanged implementation paths under `-Wall -Werror`, and reruns the unchanged eight-case DATA-010/011 correspondence corpus:

- `Phase1DataIdentityMain.hs` — five nominal/alias identity cases;
- `Phase1DataOperationContractMain.hs` — three explicit-operation/non-inference cases.

Production paths remain unchanged:

- `src/Phil/Core/DataIdentity.hs`;
- `src/Phil/Core/DataOperationContract.hs`.

## Residual assumptions / non-claims

This is semantic certification, not implementation refinement. The following remain explicit correspondence or trust boundaries:

- concrete Haskell `String` nominal-key and alias representation;
- source declaration-to-stable-key correspondence;
- source record/sum shape elaboration;
- concrete `Set DataOperation` representation and diagnostics;
- truth/competence of any explicit provider/prelude contract that grants an operation;
- Haskell implementation equivalence; and
- Rocq kernel/toolchain correctness.

The theorem deliberately does not infer equality, hashing, serialization, ABI, or raw-memory safety from structural shape, nominal identity, or transparent aliasing.
