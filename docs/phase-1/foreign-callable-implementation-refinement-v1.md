# CALL-015 implementation refinement v1

`PHIL-CALL-FOREIGN-IMPL-001` mechanically links the bounded CALL-015 production admission gate to the already-certified foreign-callable semantics.

The extracted first-stage kernel decides only finite qualification structure:

- qualification presence;
- exact artifact binding;
- exact qualified/observed semantic-surface binding; and
- presence of all five independently required evidence dimensions.

The production adapter supplies those exact predicates. When the extracted gate accepts, the already `Implementation Refined` CALL-012 production checker decides semantic callable substitution. Thus foreign qualification cannot bypass the extracted CALL-012 non-widening path.

Rocq proves that extracted admission acceptance is equivalent to the exact finite qualification projection and that, given the concrete equality/evidence bridge plus CALL-012 refinement, an accepted production decision refines the existing `ForeignQualificationAccepts` relation.

Production is now bound to the exact checked-in extraction in `src/ForeignCallableQualificationKernel.hs`. `checkForeignCallableQualification` uses the extracted gate as the owner of first-stage acceptance, reconstructs the existing concrete diagnostics only for rejected decisions, and treats any disagreement between the extracted result and the concrete projection as a representation-bridge failure. Evidence maps are projected with `Map.toAscList`, reconstructed with `Map.fromList`, and checked against their canonical key set before the extracted evidence predicates are supplied.

After first-stage acceptance, the production path invokes the already production-bound CALL-012 checker. CI regenerates the CALL-015 kernel and requires byte-identical equality with the checked-in module, typechecks the production adapter, and runs both CALL-012 and CALL-015 behavior corpora. An exact-head green run therefore closes the mechanical production correspondence required for `Implementation Refined`.

The semantic truth and competence of external evidence references remain an explicit assurance boundary; this implementation refinement proves the admission discipline, not arbitrary foreign code.
