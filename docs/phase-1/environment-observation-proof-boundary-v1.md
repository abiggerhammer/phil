# PHIL-EXEC-AMBIENT-001 proof boundary

This slice certifies the Phase-1 environmental-observation competence boundary
without introducing ambient host APIs into Phil semantics.

## Certified semantic surface

- ordinary computation cannot observe clock time, randomness, environment
  variables, locale, host/process/thread/worker identity, scheduler state,
  filesystem/device state, or any open-ended equivalent through an ambient
  source form;
- runtime handles, backend symbols, and ambient registry entries are
  non-authoritative representations and cannot become semantic observation
  relations by name matching;
- an observation must use an explicit relation identity already admitted by a
  competent source/architecture boundary;
- the requested observation kind must match the relation exactly;
- provider-backed observation composes Certified
  `PHIL-PROV-QUAL-001`: the exact operation must exist in the qualified public
  provider contract, and every implementation outcome remains mapped to an
  explicit contract outcome with exact residue;
- capability-backed observation composes Certified
  `PHIL-AUTH-POSSESS-001`: the exact possessed contract/subject/operation
  relation must already authorize the exercise;
- entry, protocol, boundary, assumption, and deployment routes remain explicit
  identity-bearing relations;
- duplicate relation identity registration rejects rather than silently
  replacing prior meaning.

A provider may therefore be intentionally nondeterministic only inside the
outcome/value space admitted by its exact qualified public contract.

## Production authorities retained

Concrete production authority remains:

- `Phil.Core.EnvironmentObservation`;
- `Phil.Core.ProviderQualification` for provider operation competence;
- `Phil.Core.Authority` for capability exercise competence; and
- the existing architecture/source boundary construction that supplies explicit
  entry/protocol/boundary/assumption/deployment relation identities.

The Rocq correspondence proof does not replace concrete Text/Map/Set lookup,
provider qualification, authority-state lookup, source elaboration, or target
runtime representation.

## Explicit boundaries / TCB

Still explicit:

- concrete relation-key and observation-kind Text identity;
- truth and construction of entry/protocol/boundary/assumption/deployment
  identities;
- concrete provider and capability correspondence already retained by their
  predecessor proofs;
- Haskell Map/Set behavior and finite traversal;
- GHC/runtime correctness;
- Rocq/toolchain correctness; and
- target/backend behavior behind qualified providers and declared boundaries.

Standard clock/random/environment provider APIs remain deferred.  The proof fixes
their admission boundary now without inventing those APIs.
