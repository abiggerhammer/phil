# Authority confinement implementation refinement v1

`PHIL-AUTH-CONFINE-IMPL-001` mechanically connects production AUTH-004 closure confinement and PROV-009/AUTH-006 provider-authority qualification to the already-Certified `PHIL-AUTH-CONFINE-001` semantics. The exact Rocq-extracted kernel is checked in and production final acceptance is bound through it.

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

## Production binding

`Phil.Core.AuthorityConfinement` reflects the native Set facts for public/reachable/exercised confinement into `decideClosureAuthorityConfinement`. Existing rejection precedence and checked-value construction remain native, but success requires the extracted decision to accept the same three facts. Negative-authority claims are decided by `decideNegativeAuthorityClaim` from the canonical checked reachable set; the retained reachability-origin diagnostics must agree with that set or the bridge fails closed.

`Phil.Core.ProviderAuthorityQualification` maps native provider-subject, inventory-basis, and extra-authority-disposition constructors to the corresponding extracted kinds. It routes subject acceptance, inventory-basis acceptance, static-summary acceptance, per-extra disposition acceptance, and the final qualification conjunction through the kernel. The native `internal \\ clientVisible` set is additionally checked pointwise against `decideProviderExtraAuthority` before disposition-domain validation, so Set representation disagreement cannot silently reach a successful qualification.

Both modules use explicit bridge-mismatch errors for impossible native/kernel disagreement. Handwritten code may therefore reject more conservatively on representation failure, but cannot turn an extracted-kernel rejection into success.

## Explicit representation boundary

Production continues to own the concrete finite representations and diagnostics:

- `AuthoritySubjectKey` / `AuthorityOperationKey`, interface/definition revision, boundary, evidence, assumption, TCB, and ABI key equality;
- `Data.Set` union, equality, difference, intersection, membership, subset witnesses, and canonicalization;
- `Data.Map.Strict` disposition-domain keys and deterministic traversal;
- finite captured-grant and provider-confinement list traversal;
- exact reachability-origin reconstruction for failed negative claims;
- provider evidence/assumption/TCB payload preservation; and
- exact rejection precedence, diagnostic payloads, and accepted checked-value construction.

These facts must be reflected exactly. Coq `bool` is extracted directly to Haskell `Prelude.Bool`, so there is no separate Boolean representation bridge.

## Validation

The dedicated workflow recompiles the Certified authority proof chain and executable correspondence under Rocq 9.2.0, fresh-extracts `AuthorityConfinementKernel.hs`, and requires byte-for-byte identity with the checked-in kernel. An exact mismatch prints a unified diff and fails.

The production-binding job then typechecks the exact kernel, both bound production modules, and the direct binding corpus under GHC 9.6.7 with `-Wall -Werror`. It reruns the unchanged authority attenuation, AUTH-004 confinement, provider semantic qualification, and PROV-009/AUTH-006 provider-authority corpora, plus direct binding cases for closure acceptance/rejection, negative claims, semantic and foreign provider acceptance, revision mismatch, ABI rejection, and exact extra-disposition coverage. Final production correspondence hashes are uploaded as a separate closeout artifact.

An all-green exact head closes `PHIL-AUTH-CONFINE-IMPL-001` as `Discharged / Implementation Refined`.
