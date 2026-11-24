# FSEM-03 DoublePing origin candidate

Gate 1 under [#2010](https://github.com/abiggerhammer/phil/issues/2010) prepares a
conditional source association for independent review. Every key and revision in
[candidate.tsv](../../test/fixtures/fsem03-doubleping-origin-v1/candidate.tsv) is
proposed and unissued. The proposed sidecar is 33,714 bytes and its SHA-256 is
`4e58ba944ceb0ee6b0356de7d314b7977e1271d715df42d4d05c8789bfdffeb2`.
The maintainer independently selects the Git object,
source bytes and exact sidecar bytes and decides the lineage and the profile
fields. A positive fixture test exercises a test selection.

The reviewed source is commit `2fc0c4abe970f398b516a2bdff2000ac4d09333f`, blob
`76f1d238407397ec09d358a42ff9ebaac4c44909`, path
`test/fixtures/fsem02-two-step-source-chain-v1/accepted.phil`, SHA-256
`33687d0c4320dda4d136fa16038f4fad043d14e1367729b8db43044e2d5c51e7`.
The literal Grammar-v1 revision is
`sha256:c352ccc31cd264af42ee7408426fabea871710d4905baef22c4cc209971ac1c5`.

## Carrier

The sidecar is UTF-8, tab-separated, and LF-terminated. The five header lines
are the version `FSEM03-DOUBLEPING-ORIGIN-V1`, repository/commit/blob/path
tuple, source SHA-256, canonical grammar revision, and offset coordinates.
The subsequent records have fixed order and columns.

| Row | Columns after the row tag |
| --- | --- |
| `decl` × 5 | source label, kind, site ID, declaration key, start, end, full canonical I, full canonical D |
| `root` | program label, derived root instance key, architecture label |
| `child` × 2 | instance label, slot key, architecture label, component label, start, end |
| `process` × 2 | process label, process-site key, root key, child slot key, start, end |

Offsets come from the production parser as zero-based Unicode code-point
offsets with exclusive ends. The four token families use `site:`, `decl:`,
`slot:`, and `process:` followed by a nonempty lowercase ASCII
letter/digit/hyphen sequence. Labels identify exact source obligations and
are checked along with spans, tags, row count, order, key uniqueness, and
recomputed revisions. Distinct slot and process-site keys bind to their
specific source declaration sites. The root uses the closed whole-source
program instance key rule with the program declaration key.

The caller supplies the independent anchor and selected byte pair. The checker
compares the actual byte pair to that selection, and hashes, decodes and parses
the same actual source buffer. The check of Git commit/path/blob resolution
happens at selection time. The focused workflow independently checks the
pinned Git object and complete original bytes. The producer returns an opaque
conditional result with the exact manifest, declaration identities, graph,
derived process population, sites and activation contracts.

## Five revision profiles for review

In the projections below, `A` is `SemanticAtom` and `tag(t,xs)` is
`SemanticOrdered (A(t) : xs)`. `U8 = tag("uint",[A("8")])`. All I/D values
are computed by `deriveDeclarationIdentity` from K, F and G. An
`identity` field is `tag("identity", [A(K), A(I), A(D)])`.
Full computed revisions for all five profiles appear in the last two columns
of the immutable declaration rows, including their canonical constructor
prefixes.

- **DoublePing.** `F = tag("phil.protocol.closed-binary-interface.v1",
  [tag("generic-parameters",[]),tag("requirements",[]),tag("roles",
  [tag("role",[A("Client"), N(client)]),tag("role",[A("Server"),N(server)])])])`.
  `N` maps a checked Send or Receive to `tag("send" or "receive",[U8,N(next)])`
  and a checked end to `tag("end",[A(outcome)])`.
  `G = tag("phil.protocol.closed-binary-definition.v1",[F])`.
  The production role checker owns duality. The profile requires the ordered
  Client Send/Send and Server Receive/Receive U8/Done templates. Nondependent
  message binder spelling is erased. K is carried independently of I/D.
- **ClientWorker.** `F = tag("phil.component.doubleping-interface.v1",
  [tag("parameters", ordered parameters),tag("provides",[])])`. Each parameter
  is `tag("parameter",[A(label),A(mode),type])`, with ordered public labels
  endpoint, first and second. The exact endpoint type field is
  `tag("endpoint",[A(protocol K),A(protocol I),A("Client"),N(client)])`.
  The two remaining parameters use unrestricted U8. The endpoint is linear.
  `G = tag("phil.component.doubleping-definition.v1",[F,tag("body",steps)])`.
  Each send step is `tag("send",[U8,A(input endpoint ordinal),A(successor
  ordinal),A(payload parameter ordinal)])`, followed by
  `tag("close",[A(final endpoint ordinal)])`. Decimal ordinals come from
  checked lexical resolution. A payload-parameter substitution changes D
  and preserves I.
- **ServerWorker.** The same component tags are used with a single linear
  endpoint label, `A("Server")` and `N(server)`. Each receive step is
  `tag("receive",[U8,A(input endpoint ordinal),A(successor ordinal),A(value
  result ordinal)])`, followed by the same Close field. Values are lexical
  binder descriptions. Both components require checked endpoint projection,
  both typed action generations, fresh result binding and Close operand.
  Local result binder renames preserve I/D when these relationships are
  preserved. Public parameter labels are wiring facts.
- **LocalDoublePing.** `F = tag("phil.architecture.doubleping-interface.v1",
  [tag("entries",[tag("entry",[A("first"),A("unrestricted"),U8]),
  tag("entry",[A("second"),A("unrestricted"),U8])]),tag("external-contracts",[])])`.
  `G = tag("phil.architecture.doubleping-definition.v1",
  [F,children,processes,protocol-occurrence,roles,bindings])`.
  Children are the ordered two `tag("child",[A(slot), component identity])`
  under `children`. Processes are the ordered two
  `tag("root-owned-process",[A(site),A(target slot)])` under `processes`.
  The occurrence is `tag("protocol-occurrence",[A("ping"),protocol identity])`.
  Roles are the ordered two `tag("internal-role",[A(role),A(slot)])` under
  `roles`. Bindings are the ordered four `tag("bind",[A(slot),A(parameter),rhs])`
  under `bindings`. The RHS is either `tag("entry-ref",[A(entry)])` or
  `tag("protocol-role-ref",[A("ping"),A(role)])`. Every fact is gated by
  exact equality with the exhaustive ordered checked inventory and both
  provisioning and activation-contract checks. Changing a stable slot/site
  changes D while preserving I. Extra, missing, reordered or retargeted
  architecture items exit this profile.
- **main.** `F = tag("phil.program.doubleping-interface.v1",
  [tag("entries",[]),tag("exports",[]),tag("observables",[]),
  tag("assumptions",[])])` is the empty explicit program-item contract.
  `G = tag("phil.program.doubleping-definition.v1",
  [F,tag("instantiate",[architecture identity,A(root instance key)])])`.
  This encodes the checked selected target and exact root occurrence relation.

The maintainer must review the classification of architecture entries versus
explicit program entries, the closed absence of provides and external
contracts, the relevancy of the slot/site and nominal dependency fields, and
the order and local-alpha equivalences. The project-wide equivalence laws and
the exact Gate 2 adoption of these profiles remain open.

## Evidence boundary

The executable control verifies all five I/D pairs, isolated origin
substitutions, stale digests and wrong coordinate units, declaration and
occurrence row mutations, protocol/nominal substitution, target and
architecture inventory edits, and both generations of typed pattern and body
validation. It also exercises equivalent source under separate test selections
and a definition-only body change. Qualified runtime activation requires
independent runtime entry evidence. The two derived process occurrences remain
unactivated. This packet establishes finite candidate correspondence only.
