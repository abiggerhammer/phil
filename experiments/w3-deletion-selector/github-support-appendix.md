# W3 GitHub support inquiry appendix

**Draft for owner and independent review.** The requested clarification
concerns GitHub's authorization contract and documented event semantics.
The original attempt remains stopped, and no repeat operation or
credential expansion is proposed.

## Recorded observation

The original source was Phil commit
`1a2f93a2cc752b3fc9bc5f58c13a0b36d75a3496` and probe blob
`e93144234a88bde006156dbcd6648be1449ab6c4`. The intended credential
was a repository-scoped fine-grained PAT with Contents write, Actions
read and Metadata read, without Workflows write. The target commit
contained four workflow blobs different from the default tree. The
create-reference request used `X-GitHub-Api-Version: 2022-11-28` and
returned HTTP 403. The original response body
and diagnostic headers were not retained. The delayed bounded Actions
inventory observed zero CREATE, DELETE and PUSH runs. Independent
original-file verification accepted the STOP record. That review
established neither the cause of the 403 nor successful CREATE.
[Commissioning ledger](https://github.com/abiggerhammer/phil/issues/2000)
· [STOP receipt](https://github.com/abiggerhammer/phil/issues/2000#issuecomment-7135730461)
· [Delayed census](https://github.com/abiggerhammer/phil/issues/2000#issuecomment-7137160025)
· [Original-file audit](https://github.com/abiggerhammer/phil/issues/2000#issuecomment-7137883419)

## Published contract and open questions

| Published source | What it establishes | What we need clarified |
|---|---|---|
| [Create a reference](https://docs.github.com/en/rest/git/refs#create-a-reference) and [published REST description](https://github.com/github/rest-api-description) | The REST operation identifies a repository, ref and target SHA. The endpoint documentation describes supported fine-grained token permission sets. | Which permission set applies separately to a fine-grained PAT, a GitHub App installation token, and a GitHub App user access token when a ref would expose workflow blobs differing from the default tree? Which documented error fields distinguish a workflow permission refusal from ruleset, repository, rate-limit or credential policy enforcement? |
| [OAuth app scopes](https://docs.github.com/en/apps/oauth-apps/building-oauth-apps/scopes-for-oauth-apps) | The classic OAuth `workflow` scope documentation describes a same-path, same-content exception for committing workflow files already present on another branch. | Does GitHub document any equivalent rule for fine-grained PAT authorization on the REST ref endpoint? Do not infer an equivalent rule from the OAuth text. |
| [Events that trigger workflows](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows) | The create and delete entries describe their respective ref/SHA contexts. Delete uses default-branch context, while create reports the created branch or tag and its last commit. The push documentation also describes a default-branch SHA fallback when a branch is deleted. | How do the documented event-associated SHA/ref and deletion-related fallback relate to the commit used to load each workflow definition? Which SHA/ref and workflow ref should a visible deletion-related push run report? For REST ref deletion, what ref, if any, do `push.branches` and `push.branches-ignore` evaluate, and is that filtering separate from the documented fallback? Can another ref sharing the target commit affect workflow selection or delivery? |

A request ID, when available in a separately authorized future incident,
would support GitHub's investigation. The original record cannot supply
one. A status code alone cannot attribute the refusal. A visible Actions
inventory only reports observations within the queried bounds.

The ordinary-T-branch topology is a conditional design candidate.
Its presence could alter authorization, workflow selection, or both.
The original record establishes no equivalence between that topology
and production Phil. It also establishes no equivalence between a PAT
and production worker or publisher Apps. Phase C, production
quarantine and activation remain on HOLD, and the
[G2 residual-authority audit](https://github.com/abiggerhammer/phil/issues/1935)
remains separate.
