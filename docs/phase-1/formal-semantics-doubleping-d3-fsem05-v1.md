# FSEM-05 DoublePing D3 reference execution

D3 is a bounded source reference execution under [#2007](https://github.com/abiggerhammer/phil/issues/2007). It starts from the independently selected original DoublePing packet and stops with both source PCs at the original Close expressions. Both native Done endpoints and their owners remain live at S2.

## Selected bytes and admission

| Input | Immutable commit | Git blob | SHA-256 |
| --- | --- | --- | --- |
| Original source | 2fc0c4abe970f398b516a2bdff2000ac4d09333f | 76f1d238407397ec09d358a42ff9ebaac4c44909 | 33687d0c4320dda4d136fa16038f4fad043d14e1367729b8db43044e2d5c51e7 |
| Adopted sidecar | 31d0e3909b3e4341b58d7387b036cf0996e971bd | d172f4456dbb0ef2cb0e548e45273829b63c6906 | 4e58ba944ceb0ee6b0356de7d314b7977e1271d715df42d4d05c8789bfdffeb2 |

The pure whole-run function takes the original source bytes, sidecar bytes, and a list of raw entry names and integers. Its private byte literals reproduce the independently adopted packet exactly. It compares the complete inputs before calling the existing static checker and checks exactly one each of the two entries before conversion to U8. Entry order is immaterial. Each value keeps its own assignment and process-qualified lexical binder identity. [Packet adoption](https://github.com/abiggerhammer/phil/issues/2010#issuecomment-7134143196)

Admission checks the original component bodies with the existing lexical chain checkers, resolves the checked action occurrences and binds their exact lexical keys to the certified process network and protocol endpoints. The initial resource contexts come from certified activation. The two U8 values enter the source store through the checked architecture entry binds.

## Source and native prefixes

| Prefix | Source PCs | Native endpoint generations | Server store | History |
| --- | --- | --- | --- | --- |
| S0 | First Send and Receive | Initial | Empty | Empty |
| S1 | Second Send and Receive | Middle | First receive binder holds the first entry | First event |
| S2 | Original Close operands | Done | Both receive binders hold their respective entries | Both events |

The first step uses native rendezvous certification with the precise initial activated contexts. The second uses the same activation and the untouched opaque first result. The receiver value lives in the source store. Its native Receive advances the endpoint and does not insert a U8 resource. Native Message evidence describes the intrinsic U8 type and its boundary contract. The source step supplies the concrete U8 selected by the checked Send operand.

Both PCs, fresh receiving key, source value, native endpoint and ownership relation, exact transition, event occurrence and causal order qualify before commit. A failed step retains the complete previous prefix. Each event retains its exact action pair, lexical binders, native before-state and successful native result. Both process sequences derive from those native causality records. The public observers accept only the opaque observations and cannot author execution inputs.

## Evidence and limits

The focused workflow checks both pinned files, compiles the unsuppressed library with GHC 9.6.7, tests the installed package from an independent client, compiles a separate source test executable and replays the static source and native correspondence checks. The CPP flag exposes only a fixed test runner in the separate source build.

Admission negatives exercise selected bytes and input assignment. The test-only controls exercise later gates from valid S0 or S1 and compare complete retained state, including both resource contexts, the owner index, source store and events. Equal-value binder substitution is tested by identity. The separate installed-package compilation checks reject constructors, record updates, continuation splicing, authoring access and the private test runner.

The Rocq model quantifies over bounded entries, states exact source PC, endpoint generation and receive-store relations, ties both event observations to distinct commit constructors and checks both process sequences. Its premises include correspondence of the selected source and native certificates to the explicit gate facts. The named assumptions and recursive object check support this conditional model. Universal Haskell/Rocq refinement, cross-invocation replay protection, physical communication, global stuckness and fairness, D4 Close and terminality, and FSEM-06 lie outside its scope.
