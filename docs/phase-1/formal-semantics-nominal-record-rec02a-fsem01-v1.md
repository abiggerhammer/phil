# FSEM-01 REC-02A nominal record origin and elimination

This evidence covers a closed Grammar-v1 record and a function with one
parameter, one flat record let, and a final Linear Bytes return. The sidecar
is a separate format for this fragment. The original REC-01 input remains a
single UTF-8 file with its multiline function intact.

## Selected original source

A host supplies the independently selected path, original source bytes, and
manifest bytes. The caller must ground the selection independently of the
presented pair. The fixture test pins each input by a separate SHA-256
commitment in the test code. The association checker compares the actual pair
byte-for-byte to the selected pair. The internal SHA-256 field binds the
manifest to the source, under the collision-resistance assumption for SHA-256.
A caller controlling the expected pair can choose different source or lineage.
The checker returns a conditional association and confers no hosting authority.

The canonical v1 sidecar is UTF-8 with TAB field separators and LF row
terminators. The header is `phil-record-origin-v1`, `grammar-v1`, the exact
parser file identifier, and the lowercase source SHA-256. Then come the
`record` and `fn` rows in that order, each with a persisted site ID, persisted
declaration key, inclusive start and exclusive end. Offsets are zero-based
Unicode code-point offsets from Grammar-v1, not UTF-8 byte offsets. IDs and keys
use nonempty lowercase ASCII letters, digits, dots and hyphens. IDs and keys
must be distinct within their respective namespaces. The two rows must match
the two top-level spans and declaration kinds. No row contains source text.

The closed scope has one record target for both the named parameter type and
the record pattern constructor. The REC-01 lexical and field checker validates
the original body, checked field types and modes, and the one-shot return.
REC-02A uses its checked fields and binder identities as inputs. REC-01's
internal opaque carrier supplies no nominal authority. The function key is the
root of its parameter and let destinations. The record key and its
interface revision come from the selected record site and the ordered
public schema, respectively. The revision uses the existing declaration
identity machinery with a tagged ordered schema and separate definition
revision. It excludes display spelling of the record and local binders.
The function descriptor records the checked parameter/result interface and
the original source as definition evidence for this bounded adapter. It does
not certify the `satisfies` clause.

## Core consumer audit

| Path | Treatment |
|---|---|
| `Core.Syntax`, `Core.IdentityKeys`, `Core.Static` | Nominal constructor stores typed K and I. The type-only module breaks the import cycle and Static re-exports the same types. |
| `Core.Value` | `equalTy` matches both nominal components. The definedness walker treats the closed nominal leaf as term-free. |
| `Core.Session` | `substituteTyTerm` and `tyNames` handle an inert closed leaf. `substituteTy` already returns unchanged leaf types. |
| `Core.SortCheck` | `refSortOfTy` gives no logical sort. `checkTypeSortsWith` has no embedded terms to sort at this leaf. |
| `Surface.GrammarV1.CheckedType` | A bare nominal type supplies no structural mode. |
| `Core.DataDestruction` | Native use retrieves the actual owner type and mode. The typed path recomputes I from declared field labels, order, types and modes before comparing actual K/I and Linear mode. The legacy route rejects nominal records, including a refined nominal base. |
| `Surface.GrammarV1.ProtocolGuardChecking` | The guard binder treats absent message mode as outside its checked fragment. |
| `Core.DataMode` | Product elimination already requires an actual product. |
| `Core.Protocol.MessageAdmissibility` | Nominal records obtain no intrinsic Message fact. Explicit boundary evidence remains subject to the existing authority contract. |
| `Surface.Check.Engine` and `Surface.Check.Support` | Legacy aliases and receive/offer payload admission reject nominal and refined-nominal types when deriving a structural mode. Existing leaf defaults introduce no term subjects or field projections. REC-02B integration remains a separate gate. |

Native Core checks the requested owner name, active loans, destination
freshness and exact successor bindings. Pure schema and disposition validation precedes the owner lookup. A malformed plan can therefore determine the diagnostic even when the owner is wrong. Failure returns no successor context.
The supplied context must be the current checked native context. Because
`ResourceContext` is a pure value, the API cannot invalidate retained copies
of a pre-transition context. The replay regression supplies the actual
post-transition state.

The Rocq model proves its gate is exact in the modeled K/I pair, produces no
successor on key/revision, mode or loan failure, and preserves the existing
conditional native owner-removal and Linear disposition facts. Source
authentication, parser fidelity, schema encoding, and correspondence between
the native implementation and the Rocq model remain separate obligations.
The two imported native facts retain the existing Core parameter `Ty : Type`.
The three nominal-gate theorems are closed under the global context.
