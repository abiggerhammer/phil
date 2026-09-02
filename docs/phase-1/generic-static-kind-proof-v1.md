# PHIL-GEN-KIND-001 — generic static kind proof v1

This proof certifies the bounded GEN-013 static-actual kind rule already implemented by `Phil.Core.Generic.StaticActual`.

A static actual is interpreted against the exact declared generic parameter kind. Direct actuals must carry that same kind. A name-shaped static reference is parsed once and resolved only among candidates of the expected kind; candidates from another semantic category cannot be retried as a fallback merely because doing so would make the application succeed.

The proof establishes that every successful reference resolution selects an exact candidate with the declared kind, unresolved references reject, wrong-kind references cannot fall back, and multiple same-kind candidates reject as ambiguous. Successful checking preserves the exact parameter key and declared kind in the checked result. Telescope acceptance preserves exact parameter/actual/result arity and the complete ordered parameter-key/kind shape.

The dedicated workflow recompiles `proof/Phil/Core/GenericStaticKind.v` under Rocq 9.2.0, strictly typechecks the production checker and unchanged GEN-013 corpus under `-Wall -Werror`, and reruns all seven focused cases.

## Boundary

Concrete Haskell `Text`, `SemanticForm`, `GenericStaticParameterKey`, list/Set representation and equality, parser-to-static-actual correspondence, name-resolution candidate construction, and the semantic truth/competence of each kind-specific value remain explicit correspondence boundaries. The theorem proves exact kind selection and no fallback reinterpretation; it does not claim the full Grammar-v1 elaboration theorem or the category-specific semantics of Type, Session, Message, Effects, provider, callable, boundary, or architecture values.
