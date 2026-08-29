# Authority confinement implementation refinement v1

This staging tranche begins `PHIL-AUTH-CONFINE-IMPL-001`, mechanically connecting production AUTH-004 closure confinement and PROV-009/AUTH-006 provider-authority qualification to the already-Certified `PHIL-AUTH-CONFINE-001` semantics. Production behavior is unchanged in this tranche.

## Executable semantic seam

The Rocq-extracted kernel owns representation-neutral decisions over exact Boolean facts and constructor kinds:

1. **Closure confinement** — public authority is reachable, exercised authority is reachable, and exercised authority stays within the public mediated surface.
2. **Negative authority claims** — a negative claim is accepted only when the exact subject/operation authority is absent from the reachable set.
3. **Provider semantic subject** — pure-Phil provider authority is tied to the exact accepted interface and definition revisions; opaque foreign subjects remain explicitly distinct.
4. **Provider inventory basis** — pure Phil requires checked pure-Phil inventory; opaque foreign authority requires evidence, assumption, or TCB basis; ABI shape is never an inventory proof.
5. **Extra authority** — internal-but-not-client-visible membership is computed as exact Boolean difference.
6. **Static provider summaries** — static reachability stays within declared internal authority, while static public/exercised authority stays within the client-visible surface.
7. **Extra-authority disposition** — pure static confinement requires reachable-but-not-public-and-not-exercised authority; opaque foreign code cannot claim static Phil confinement; external evidence, assumptions, and TCB boundaries remain explicit conditional dispositions; ABI absence is rejected.
8. **Provider qualification** — final acceptance conjoins exact subject, inventory, static-summary, disposition-domain, and per-disposition acceptance facts.

The correspondence theorems are sound and complete for the corresponding Certified propositions under explicit reflection hypotheses connecting finite native facts to the representation-neutral relations.

## Explicit representation boundary

Production continues to own the concrete finite representations and diagnostics:

- `AuthoritySubjectKey` / `AuthorityOperationKey`, interface/definition revision, boundary, evidence, assumption, TCB, and ABI key equality;
- `Data.Set` union, equality, difference, intersection, membership, subset witnesses, and canonicalization;
- `Data.Map.Strict` disposition-domain keys and deterministic traversal;
- finite captured-grant and provider-confinement list traversal;
- exact reachability-origin reconstruction for failed negative claims;
- provider evidence/assumption/TCB payload preservation; and
- exact rejection precedence, diagnostic payloads, and accepted checked-value construction.

These facts must be reflected exactly. Handwritten bridge/diagnostic code may reject on disagreement but may not turn an extracted-kernel rejection into success. Coq `bool` is extracted directly to Haskell `Prelude.Bool`.

## Validation

The dedicated workflow recompiles the Certified authority proof chain and the new executable correspondence under Rocq 9.2.0, fresh-extracts `AuthorityConfinementKernel.hs`, typechecks the fresh kernel under GHC 9.6.7 with `-Wall -Werror`, typechecks the unchanged production confinement/provider-authority modules, and reruns the existing authority attenuation, AUTH-004 confinement, provider semantic qualification, and PROV-009/AUTH-006 provider-authority corpora.

On an all-green exact head, harvest the exact kernel/proof artifact, record `PHIL-AUTH-CONFINE-IMPL-001` as `Active / Mechanized`, merge this staging tranche, then production-bind final acceptance through the checked-in exact extracted kernel with fail-closed native Set/Map/list/equality bridges.
