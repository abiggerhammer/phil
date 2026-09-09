# Portable callable lifecycle negatives v1

This corpus migrates constructor-only CALL-007, CALL-008, and CALL-009 negative conformance to implementation-independent competent-boundary data.

- `manifest.tsv` owns stable fixture identity, expected rejection class, competent layer, exact Matrix/Certified authority, and portable rejection coordinates.
- `occurrences-v1.tsv` declares callable occurrence identity, public interface revision, callee lifecycle transition, declared replacement interface/state, current state, and initial availability.
- `captures-v1.tsv` declares closure capture identity, transfer, and structural mode independently from Haskell constructors.
- `actions-v1.tsv` is an ordered invocation trace. Every pre-final step must succeed; the final step must reject exactly as recorded. This is how stale-predecessor fixtures demonstrate a real successful consume/replace before forbidden reuse.
- `authority-registry-v1.tsv` resolves every used semantic authority. `PHIL-CALL-LIFE-001` is backed by `proof/Phil/Core/CallableLifecycle.v`.

The Haskell replay program is only an adapter from this portable vocabulary to the current callable lifecycle checker. Fixture IDs, Haskell exception constructors, diagnostic text, and file paths are not semantic conformance authority.
