# Phil Phase 1 keyword lexicon

This is the explanatory lexicon for the **reserved words of canonical Grammar v1**. It is a reference aid, not a second syntax specification: `grammar/phase1-surface.ebnf` is the Phase 1 concrete-syntax authority, and `grammarV1ReservedWords` in `src/Phil/Surface/GrammarV1/Lexer.hs` is the executable reserved-word inventory.

The current inventory contains **132 reserved words**. Every reserved word appears exactly once in the grouped tables below. Some words have more than one grammatical role; their entry mentions the important roles rather than pretending each spelling has only one use.

## How to use this lexicon

- Read the [Phase 1 Tour](../tutorials/tour-phase1.md) for first-use explanations in context.
- Use this file when you encounter a spelling and want to know what category it belongs to.
- A reserved word cannot be used as an ordinary identifier.
- Semantic acceptance is still decided by the competent checker. Recognizing a keyword never grants authority, evidence, ownership, or validity.

## Built-in kinds, types, and literals

| Word | Meaning |
| --- | --- |
| `Bool` | Built-in Boolean value type. |
| `Bytes` | Built-in length-indexed byte-sequence type constructor, as in `Bytes[n]`. |
| `Effects` | Generic kind for effect-set parameters. |
| `Frame` | Built-in framed-input type constructor parameterized by a boundary/framing contract. |
| `Message` | Generic kind for protocol-message parameters. |
| `Nat` | Generic kind for natural-number/static index parameters. |
| `Proof` | Evidence type constructor `Proof[P]` for a proposition `P`. |
| `Session` | Generic kind for session/protocol-state parameters. |
| `Type` | Generic kind for ordinary value-type parameters. |
| `Unit` | Built-in one-value type. |
| `Validated` | Evidence-bearing validated-value type constructor. |
| `true` | Boolean/static proposition literal for truth. |
| `false` | Boolean/static proposition literal for falsehood. |
| `unit` | The sole ordinary value of `Unit`. |

## Source organization and declaration forms

| Word | Meaning |
| --- | --- |
| `module` | Declares the source file's module name. |
| `import` | Imports names from another module, optionally with an explicit name list. |
| `record` | Declares a product/record type with named fields. |
| `data` | Declares a sum/variant type. |
| `type` | Declares a type alias. |
| `claim` | Declares a named proposition, optionally with parameters and a transparent body. |
| `callable` | Declares a callable contract; also appears as a generic kind/requirement category. |
| `fn` | Declares a named function that explicitly satisfies a callable contract. |
| `component` | Declares an executable Phil component. |
| `protocol` | Declares a two-role protocol family. |
| `provider` | Declares a provider contract or participates in provider implementation/requirements. |
| `implementation` | Marks a concrete provider implementation declaration. |
| `opaque` | Marks a provider implementation whose body is outside ordinary Phil source. |
| `capability` | Declares an authority-bearing capability contract. |
| `boundary` | Declares a boundary contract; also names boundary generic kinds/requirements. |
| `architecture` | Declares an architecture; also names architecture generic kinds/requirements. |
| `program` | Declares the selected root program. |

## Structural modes, generics, and requirements

| Word | Meaning |
| --- | --- |
| `mode` | Introduces an explicit structural mode on a declaration or closure. |
| `unrestricted` | Structural mode permitting both duplication and discard. |
| `affine` | Structural mode permitting discard but not duplication. |
| `linear` | Structural mode permitting neither duplication nor silent discard. |
| `requires` | Introduces generic prerequisites or a callable/capability proposition requirement, depending on context. |
| `structural` | Introduces a generic copy/drop permission requirement for an abstract value parameter. |
| `proposition` | Introduces a logical generic requirement. |
| `effects` | Introduces an effect set/bound, or an effect-set generic requirement. |
| `authority` | Introduces required authority in callable/generic/architecture contexts. |
| `representation` | Introduces representation-related generic requirements, including `boundary representation ...`. |
| `placement` | Introduces a placement-related generic proposition requirement. |
| `cost` | Introduces a cost requirement or callable cost expression. |
| `environment` | Introduces an environment-related generic proposition requirement. |
| `within` | Introduces an effect upper bound (`effects E within ...`) or scopes an architecture assumption (`assume ... within ...`). |

## Callable contracts and outcomes

| Word | Meaning |
| --- | --- |
| `captures` | Lists the lexical values explicitly carried by a closure. |
| `closure` | Constructs a first-class function value. |
| `satisfies` | Names the contract a function, closure, or provider implementation claims to implement; checking still establishes the claim. |
| `provides` | Names the public value type presented by a component. |
| `consumes` | Lists caller-visible resources consumed by a callable contract. |
| `borrows` | Lists caller-visible resources borrowed by a callable contract. |
| `outcomes` | Declares the public set of possible callable outcome classes. |
| `outcome` | Introduces branch-specific residue/state facts for one callable outcome. |
| `success` | Callable outcome class for ordinary successful completion. |
| `negative` | Callable outcome class for typed negative/non-success completion. |
| `terminal` | Callable outcome class for declared terminal completion. |
| `fatal` | Callable outcome class for fatal completion. |
| `state` | Introduces explicit successor-state slots in callable outcomes or loop/join state. |
| `callee` | Introduces what happens to the callable value itself across an outcome. |
| `preserve` | Callee transition that leaves the callable available. |
| `consume` | Callee transition that consumes the callable value. |
| `replace` | Callee transition that replaces the current callable with a named successor contract. |
| `with` | Connective in `replace with ...`. |
| `ensures` | Introduces a callable/outcome postcondition. |
| `obligation` | Introduces an explicit residual proof/verification obligation. |
| `assumes` | Introduces an explicit callable assumption. |

## Providers, capabilities, and boundary contracts

| Word | Meaning |
| --- | --- |
| `operation` | Declares or implements a provider operation. |
| `law` | Declares a provider/capability/boundary law or supplies an implementation proposition. |
| `lifecycle` | Declares or supplies a provider lifecycle proposition. |
| `permits` | Lists an operation/contract permitted by a capability. |
| `canonical` | Marks a boundary representation/encoding as canonical in the boundary contract. |
| `failure` | Declares the boundary's failure type. |
| `correspondence` | Introduces the proposition relating boundary-side and semantic representations. |

## Protocols and session communication

| Word | Meaning |
| --- | --- |
| `role` | Declares a protocol role or binds a protocol role to an architecture participant. |
| `send` | In a session declaration, describes a send transition; in term code, sends a value on a live endpoint and advances it. |
| `receive` | In a session declaration, describes a receive transition; in term code, receives a typed value from a live endpoint and advances it. |
| `select` | Declares/executes active protocol branch selection. |
| `offer` | Declares/executes passive protocol branch handling. |
| `end` | Declares a terminal session state with a terminal label. |
| `recursive` | Introduces guarded session recursion; on a named function, it is the required declaration marker that makes self/mutual recursion eligible for stabilized-contract checking. An unmarked recursive `fn` does not typecheck. |
| `continue` | In sessions, jumps to a named recursion variable; in term loops, supplies the next loop-state actuals. |
| `then` | Connects a protocol send/receive action to its successor session state. |
| `using` | Supplies an explicit contract/evidence value to a protocol, boundary, validation, transport, or exact-I/O form. |
| `when` | Introduces a proposition guarding a protocol action/branch. |
| `send_exact` | Uses the exact byte-oriented send form on an endpoint. |
| `receive_exact` | Receives an exact requested amount/message representation, optionally using evidence. |
| `receive_frame` | Receives a raw frame from an endpoint for later recognition/validation. |
| `commit_receive` | Commits a previously validated/pending receive using its evidence. |
| `close` | Closes a live endpoint that is already at a terminal `end` state. |

## Architecture and program wiring

| Word | Meaning |
| --- | --- |
| `instance` | Creates a concrete architecture occurrence from a reusable declaration. |
| `ref` | Creates an explicit reference to an already-existing architecture occurrence rather than a new occurrence. |
| `process` | Activates an already-created executable occurrence in the static Phil process network. |
| `bind` | Declares an explicit architecture wiring/binding edge between named semantic ports/resources. |
| `external` | Marks a protocol role as outside the Phil process population. |
| `entry` | Declares a value/resource supplied at an architecture or program entry boundary. |
| `grant` | Declares an explicit architecture authority/value grant. |
| `originates` | Introduces the architecture occurrence at which an authority originates. |
| `observable` | Marks an architecture/program value or event as externally observable. |
| `constraint` | Introduces an architecture-level proposition that must hold. |
| `assume` | Introduces an explicit architecture/program assumption. |
| `export` | Exports an obligation to a named external/architectural target. |
| `instantiate` | Creates/selects the root architecture occurrence of a `program`. |

## Term expressions, control flow, and resource operations

| Word | Meaning |
| --- | --- |
| `let` | Binds the result of an expression to a pattern. |
| `return` | Returns a value from the current component/function/closure block. |
| `construct` | Constructs a record/sum value with explicit field assignments. |
| `borrow` | Opens a scoped borrow of a value. |
| `as` | Introduces the borrow binder or the target type of `accept ... as ...`. |
| `if` | Introduces conditional control flow. |
| `else` | Introduces the false branch of an `if`. |
| `match` | Pattern-matches a value, optionally with an explicit join contract. |
| `decide` | Branches on a checked decision value/certificate. |
| `loop` | Introduces an explicit loop with optional state and invariant. |
| `invariant` | Introduces the logical invariant for a loop or join. |
| `join` | Introduces an explicit post-branch state/invariant contract. |
| `break` | Exits a loop and optionally supplies exit-state values. |
| `release` | Consumes a resource through its unique competent declared release transition; it is not generic `free`. |
| `accept` | Explicitly accepts/checks a value as a target type at the competent type/refinement boundary. |
| `prove` | Introduces explicit proof/evidence production/checking for a proposition. |
| `transport` | Transports a value to a target type using explicit equality evidence. |
| `recognize` | Recognizes a structured semantic value from raw/framed input using a named recognizer. |
| `validate` | Validates a value/input using a named validator, optionally at an explicit position/context. |
| `reject` | Produces typed-negative control flow. |
| `fail` | Produces fatal control flow. |

## Logic and relation words

| Word | Meaning |
| --- | --- |
| `and` | Logical conjunction in propositions. |
| `or` | Logical disjunction in propositions; also introduces expression fallback (`or fail` / `or reject`). |
| `not` | Logical negation in propositions. |
| `in` | Finite-collection membership relation in propositions. |
| `disjoint` | Finite-collection disjointness relation in propositions. |

## Context/connective words

| Word | Meaning |
| --- | --- |
| `at` | Connective used for authority origin (`originates at`) and validation position/context (`validate ... at ...`). |
| `from` | Connective in recognition (`recognize ... from ...`). |
| `on` | Connective naming the endpoint/resource acted on by protocol I/O and failure forms. |
| `to` | Connective naming a transport target type or exported-obligation destination. |

## Language-defined names that are not reserved keywords

A few spellings have language-defined meaning without being lexer keywords. They remain syntactic identifiers and are interpreted only in the competent semantic context.

| Name | Context | Meaning |
| --- | --- | --- |
| `discard` | `structural T : discard;` | The admitted structural permission name for weakening: generic code may omit a value of `T`. |
| `duplicate` | `structural T : duplicate;` | The admitted structural permission name for contraction: generic code may make a value of `T` available to more than one use. |
| `key` | `@key("...")` | The currently admitted semantic attribute name for stable top-level declaration lineage. The attribute name is an identifier following `@`, not a reserved keyword. |

Unknown structural-permission names and unknown semantic attribute names fail closed at their competent semantic layers; being lexically an identifier is not an extensibility promise.