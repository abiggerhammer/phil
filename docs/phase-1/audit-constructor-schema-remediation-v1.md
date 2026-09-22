# Phase 1 constructor-schema audit remediation

**Finding:** `PHIL-AUD-CONSTRUCTOR-SCHEMA-001`  
**Audit event:** `PHIL-AUDIT-20260921-EXPR-CONSTRUCT`  
**Original review pin:** `1d6f8463942253664bed5b911ffa3170ab928069`

## Defect

The operational Surface `construct Hello` / `construct Begin` path previously turned the source assignment list into a `Map` before validating it and then synthesized each output `FieldInfo` from the supplied value itself.

That had three manifestations of one schema-checking omission:

- a refinement-visible but schema-incompatible value such as `true` could define the apparent type of `Hello.versions`;
- duplicate field assignments were collapsed before either occurrence was validated; and
- extra fields were ignored because only required names were traversed.

The returned record shape was therefore candidate-derived rather than independently checked against `recordShape`.

## Repair

`constructValue` now treats `recordShape` as the independent constructor schema.

Before any assignment map is built, it rejects duplicate names, unknown fields and missing fields against the schema's exact field-name set. Each surviving candidate is then checked for unrestricted mode and compatibility with the schema field type and refinement sort.

Ordinary exact types use Phil's existing definitional type equality. Sorted opaque fields use their declared refinement sort as the semantic compatibility boundary so the established `supported_versions()` result remains compatible with Hello even though its internal display name is `SupportedVersions` while the record schema uses `Versions`.

After validation, the result keeps the candidate field type so valid refinements such as the non-empty supported-version refinement are not erased, while the field sort comes from the independent schema and the optional alias comes from the checked source expression.

## Permanent replay

`test/Phase1AuditConstructorSchemaMain.hs` replays Astra's c01-c08 corpus through both `checkSurfaceComponent` and the public `verifySurfaceApplication` intrinsic boundary. The two boundaries must agree on acceptance/rejection class.

The corpus preserves the real supported-version positive, missing/unknown-constructor controls, rejects the Boolean field, duplicate and extra-field cases, rejects the record-shaped borrowed-view candidate, and preserves an independently safe record returned from a borrow.

The dedicated workflow also replays the established intrinsic-invalidity and frozen Surface conformance suites, including the ordinary Upload client that constructs both Hello and Begin.

## Assurance boundary

This closes only the implementation/public-consumer constructor-schema slice. It does not establish a general Grammar-v1 record-construction theorem, close the separate borrow-local or typed-adapter provenance findings, change native lowering, or promote any proof or Certified status.
