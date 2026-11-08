# FSEM-01 — source product elimination with restored affine and linear owners

> **Status:** bounded, non-normative production source fragment and conditional
> abstract Rocq proof. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).
> This is not a universal Haskell-to-Rocq refinement theorem or an independent
> proof of source nominal lifecycle admission.

## Source fragment and explicit authority

The positive source witness is:

~~~phil
data Permit mode affine = Permit(U64);
fn unpack(packet : (Permit, Bytes[8])) -> Bytes[8] satisfies C {
  let (permit, payload) = packet;
  return payload;
}
~~~

The source declaration's Affine mode is checked by the existing nominal mode
checker only when an **externally admitted** lifecycle/resource justification
is supplied. Source spelling alone is never treated as permission to strengthen
the U64 payload. The source product parameter is checked by the exact opt-in
named-flat-product resolver introduced in #1669, preserving both elements'
ordered checked modes and the affine member's GenericTypeKind, DeclarationKey
and InterfaceRevision provenance. The aggregate product is Linear because it
contains a Linear Bytes element.

The declaration-rooted function parameter and each tuple-let successor are
allocated by the real Grammar-v1 lexical binder/scope machinery. The
initializing expression is resolved in the pre-let scope, preventing a new
successor from being its own initializer. The source binder checker rejects
duplicate names/shadowing, while unsupported nested patterns, arbitrary
control flow, generic/recursive functions and unmatched source shapes remain
explicit non-competence.

## Actual production operation, not simulated destructuring

[The bounded source adapter](../../src/Phil/Surface/GrammarV1/SourceProductElimination.hs)
sets **one exact opt-in product elimination contract** in the existing Surface
environment, keyed by the resolved product owner's semantic name. It projects
the parsed tuple-let pattern and initializer into real Surface statements,
preserving the newly allocated successor names.

[The production Surface checker](../../src/Phil/Surface/Check/Engine.hs) now
recognizes an opted-in tuple pattern bound from the exact matching product
owner and invokes the established certified native
[Core.DataMode.eliminateProductBinding](../../src/Phil/Core/DataMode.hs):

- The original product's mode and type must exactly match the checked source
  contract before it is touched.
- The Core operation consumes the Linear TyProduct owner once; checks
  arity, distinct successor identities and mode agreement; and installs
  each successor in its exact unrestricted/affine/linear structural zone.
- New Surface metadata reflects those exact native inserts; Bytes shapes
  are rebound to the new semantic name. The original product metadata is
  removed.
- All other tuple lets and old surface paths retain their prior behavior:
  the new capability is opt-in, not a generic assumption that every
  RuntimeScalar TyProduct is a RuntimeTuple.
- The finite [production trace API](../../src/Phil/Surface/Check/Engine.hs)
  records **actual** pre/post-elimination native Core contexts and the ordinary
  checker outcome, without inventing a post-error state. The source adapter
  checks regular and traced checker outcome parity.

The accepted source returns the Linear Bytes successor, leaving the affine
Permit unconsumed but legally discardable. An additional positive source
returns both restored members as (Permit, Bytes[8]), consuming both exactly
once and validating the source-checked ordered TyProduct contract.

## Regression witnesses

[The source conformance driver](../../test/Phase1FSEM01SourceProductEliminationMain.hs)
parses 15 real source files in
[the fixtures](../../test/fixtures/fsem01-source-product-elimination-v1/)
and tests the following paths:

- **accepted / return-both:** real product elimination restores exact
  Affine Permit and Linear Bytes bindings, removes the original product,
  and the final checked return discharges the appropriate obligations.
- **return-affine / return-unit:** exact production LinearCompletion errors;
  an unused Linear Bytes successor is not silently discarded.
- **return-product-owner:** the consumed product cannot be used again;
  the production checker reports StructuralUse.
- **reversed-return / duplicate-return:** exact product contract mismatch
  or duplicate restricted use during the ordinary production return path.
- **wrong-arity:** the native Core product elimination reports the exact
  2-to-3 arity error, with no fabricated post-elimination context.
- **duplicate-successor:** source semantic binder identity rejects the
  duplicate name before production.
- **unjustified / weakened:** missing or unadmitted external nominal lifecycle
  evidence and declared structural-mode weakening remain exact nominal
  authority failures.
- **wrong-parameter-order / wrong-result-width / wrong-initializer /
  nested-pattern:** unsupported shapes fail closed, without an opaque
  product/type/scope fallback.

For each admitted two-element fixture, tests compare the production
checkpoints with an **independent call** to native Core elimination and
specific Core consumption, reuse and completion errors. This is executable
finite conformance, not general universal implementation refinement.

## Conditional Rocq model

[SurfaceSourceProductEliminationBridge.v](../../proof/Phil/Surface/SurfaceSourceProductEliminationBridge.v)
specializes the established DataProduct model to a two-element affine/linear
contract. It proves aggregate Linear mode, exact ordered positional
restoration, distinct-successor requirements, wrong-arity rejection,
two-element accepted arity, the external affine-admission premise, linear
one-shot consumption, and prohibition against silent linear discard.
There are no new axioms or admitted lemmas.

The Rocq Source.Name is String and its Ty is abstract; native Haskell uses
Text, concrete Ty, Map, Set and additional error constructors. The theorem
does not prove all those carriers are semantically identical. Native
Haskell/Core elimination and source parsing are checked by running finite
witnesses, **not** by extracting or proving a universal simulation.

## Verification and remaining obligations

The [early preflight](../../.github/workflows/fsem01-product-elimination-preflight.yml)
checks a warning-free strict production Haskell build, relevant SURF-008
and prior FSEM-01 source/product regressions, the new source driver and
Rocq 9.2 proof compilation (including Print Assumptions and an explicit
no-new-admissions check). The full exact-PR-head CI and FSEM claim guard
must pass before merge; no passing evidence is claimed in this document
without an exact checked head.

**Still open:** general recursive/nested product elimination, arbitrary
multi-product syntax, captures/joins/loops, runtime product payload
representation beyond ownership/type discipline, explicit affine disposal
effects and external lifecycle soundness, general Haskell-to-Rocq
refinement and exact error simulation, complete satisfies-C assurance
authority, whole-compiler soundness, and the independently executable
full-language Rocq interpreter required for FSEM-05.
