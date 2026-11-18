# FSEM-02: typed sender resource before receiver-slot collision

**Non-normative bounded source/native test and separate conditional Rocq evidence.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613); extends the owner/head/binder/resource diagnostic chain in #1891 and #1893.

## Typed admission and transition boundary

The accepted complete Grammar-v1 restricted `Bytes[8]` Send/Receive source is parsed and checked by the **production** source adapter, with externally supplied binary protocol instance/roles, message boundary certificate, activated process/owner occurrence, projected endpoint predecessors and separately authorized message binder. None of those authorities is inferred from the program's spelling.

Let `sourceOK`, `priorOK` and `binderOK` denote the independently checked gates, and let `senderPresent`, `senderTyped` and `receiverVacant` describe *actual* native linear resources. For this bounded transfer, after all three source/external gates the native checker must consume the sender's present resource and compare its **actual `Ty`** with the authorized message `Ty` before inserting at the receiver. A mismatch returns `RestrictedMessageTransferTypeMismatch` with no successor; a correctly typed sender and occupied receiver returns `RestrictedMessageReceiverResourceError ... (DuplicateBinding ...)`, also with no successor. A properly typed sender and vacant receiver permit the exact source-derived endpoint successors, payload move and affine spectator frame.

The executable negative for the actual production checker retains the source, protocol, owner index and both endpoint heads but forges the sender's linear payload to `U8` (instead of `Bytes[8]`) *and* inserts an occupied receiver binding. It must report exact `RestrictedMessageTransferTypeMismatch (Bytes[8]) (U8)` first. Repairing only the receiver cannot suppress that error. Repairing **only sender type** exposes the receiver's exact duplicate-binding error. Restoring both admits the independently authorized original transfer with exact owner/endpoint and spectator checks. Duplicate error probes are deterministic. These hostile resource maps violate the supplied activation consistency; they are not legitimate new activations.

A minimally changed *complete source* uses `close endpoint;` in place of `close done;`. It must reject with the exact `GrammarV1ComponentSendCloseCloseMismatch` **before** any externally forged resource errors. This is a source refusal, not a manufactured authority judgment.

The [native accepted/rejected executable](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) checks production Core/state behavior. [Six Rocq 9.2 model laws](../../proof/Phil/Core/FSEM02SenderResourceTypePriority.v) independently establish bounded decision ordering, refusal without a successor, exact modeled resource changes and spectator flag preservation. The Rocq booleans abstract native `Ty`, `Map` and endpoint identities; they are **not** a proof of general Haskell-to-Rocq refinement, global atomicity, source-to-target simulation, termination, fairness or disposal authority.

The [unprivileged two-job work-branch preflight](../../.github/workflows/fsem02-sender-type-priority-preflight.yml) must pass GHC 9.6.7 `-Werror`, accepted/rejected production source execution, Rocq 9.2 compilation and no-new-admissions check **before** opening a draft PR; broad exact-head protection and post-ready claim guard remain mandatory.

**Open:** universal native/resource-model refinement; external activation, selected-root, terminal/disposal and assurance authority; full FSEM-02 coverage and normative graduation.
