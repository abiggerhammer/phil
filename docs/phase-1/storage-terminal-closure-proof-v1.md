# Storage terminal closure proof boundary (PHIL-MEM-CLOSURE-001)

This proof certifies the Phase 1 distinction between **semantic storage ownership** and **physical storage reclamation**.

## Certified semantic boundary

`proof/Phil/Core/StorageTerminalClosure.v` composes the already-certified storage-realization, Systems stage-closure, and concurrency terminal-closure layers.

An explicit semantic storage resource participates in terminal safety. A semantic storage owner is closed only when it is:

- explicitly released; or
- assigned an exact terminal disposition that is permitted for that exact semantic storage resource.

A live semantic storage owner therefore blocks both process-level memory closure and root-level closure for the static process that owns it. Duplicate semantic-storage owner identities are rejected by the normalized closure relation.

The process-level theorem reuses the certified `CertifiedProcessTerminalFact`; it does not replace the ordinary resource/loan/endpoint/obligation closure rules. Root closure likewise reuses the exact static `ProcessOccurrence` population certified by the concurrency tranche.

## Physical reclamation is a separate realization obligation

Physical storage objects do **not** become Phil semantic owners merely because they back a semantic value or resource. The physical reclamation relation separately accepts:

- actual reclamation; or
- retention under the exact profile revision that explicitly permits that retention.

A physical leak fails a profile that requires reclamation, and retention under the wrong profile fails. However, physical reclamation state is intentionally absent from `CertifiedMemoryRootClosure`. Consequently, a physical reclamation failure can invalidate realization/provider/profile certification without retroactively changing an already-established Phil semantic terminal fact.

This is the formal counterpart of MEM-005's existing implementation fixture: **“physical leak does not rewrite semantic terminal closure.”** It is not a claim that leaks are acceptable.

## Correspondence boundary

The dedicated workflow keeps the proof tied to the existing implementation by:

- strict-typechecking `src/Phil/Systems/Storage.hs`;
- rerunning the unchanged MEM-001--006 storage realization corpus, including MEM-004/005;
- rerunning the unchanged process terminal-closure corpus; and
- compiling the certified predecessor theorem chain before `StorageTerminalClosure.v`.

Concrete `Text`/`Map`/`Set` representation, exact source-to-storage-owner extraction, provider truth, and profile-specific physical reclamation mechanisms remain implementation/correspondence boundaries.

## Explicit non-claims

This proof does not certify `PHIL-MEM-FAIL-001` or `PHIL-MEM-COST-001`. Allocation-failure widening remains blocked on Systems partiality, and physical storage cost attribution remains a separate obligation.
