# Systems subject/authority production binding v1

This closes the implementation-refinement binding for `PHIL-SYS-SUBJECT-AUTH-001` after staging in PR #502.

The exact Rocq-extracted `SystemsSubjectAuthorityKernel.hs` is checked in at `src/SystemsSubjectAuthorityKernel.hs` with SHA-256 `f03b1e98aeb54e271c4a66204593bea9c8f8b1090cd3013300c7ade48b79043d`.

Production keeps concrete Haskell representation work explicit: `Text` and revision construction, `Map`/`Set` traversal and lookup, Systems value enumeration, provider/evidence construction, canonical stage revision construction, and detailed diagnostic payloads remain native correspondence boundaries.

The normalized semantic decisions are kernel-owned:

- SYS-004 reflects the complete concrete subject-correspondence graph into checked-vs-runtime basis, nonempty Systems sets, value existence, global exclusive subject binding, and exact validity-scope facts. The extracted classifier selects the failure class; native code recovers the exact offending subject/value payload.
- SYS-005 preserves native selection construction/integrity checks, then reflects exact provider-call binding basis, selected admission, interface, operation, implementation entry, and call-site domain facts into the extracted classifier. Native code recovers the exact mechanism/provider payload for the selected failure class.
- SYS-006 uses the extracted authority/effect stage classifier for exact surface/use-domain and public/internal assignment gates, and uses the extracted per-effect and per-authority decisions at every concrete Systems provider use.

Runtime representation coincidence and runtime-symbol-only provider inference remain rejected. Source-observable effect widening remains rejected. Target-internal effect widening requires a nonempty checked realization-refinement revision. Public and qualified-internal authority exercises remain exact to their declared/qualified surfaces and dispositions.

The closeout workflow fresh-extracts under Rocq 9.2, requires the staged SHA-256 and byte-for-byte equality with the checked-in kernel, strict-typechecks the bound production chain, executes all 32 direct extracted-kernel controls, and reruns the unchanged 31-case SYS-004--006 correspondence corpus.
