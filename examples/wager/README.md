# Wager round: a commit-reveal protocol with an external referee

**Status: non-normative example.** It changes no grammar, semantics, proof or CI. Its evidence is
`test/ExampleWagerRoundMain.hs`. It is an example of the protocol-shape, role-duality and record-mode checks, not a
checked implementation of the Solana referee or of a player endpoint.

`round.phil` is one player's side of a round of The Line, a two-player game played between AI agents, in its wager
mode. Each round both players secretly choose a pull from 0 to 30, and the bigger pull moves a shared node one place
toward its player. In wager mode the referee is a Solana program that holds both players' stakes. Today that runs as
practice on Solana's devnet, with worthless SOL. The program's design is in
[docs/wager-mode.md](https://github.com/HigherMaestro/highwire/blob/main/docs/wager-mode.md), sections 4.2 and 7.2
to 7.3.

## What it states

| Rule of the real protocol | In the example |
| --- | --- |
| Commit, wait for both commits, reveal, learn the result, every round | `WagerRound`, a recursive protocol |
| Before revealing, a player learns that the other side committed, never what | `BothCommitted` carries no payload |
| A move's nonce is used once, and losing it forfeits the match | `Move` must be linear: a record-mode obligation only |
| The referee is a program outside Phil | `role round.Program = external` |

The linear `Move` connects to the running protocol only outside what this example verifies. `WagerRound` sends tuples,
not `Move`, and `WagerPlayer` returns `unit`, so nothing here checks that a nonce is consumed once across commit and
reveal, or that losing it forfeits the match.

The first draft declared `Move` as `mode affine`, so that a forfeited match could drop it. The record checker refused
it with `DeclaredModeWeakensDerived Linear Affine`: `Bytes[32]` makes the record linear. Linear is the right rule for a
nonce, which should only ever be revealed or deliberately discarded.

## Evidence

```sh
cabal exec -- runghc -Wall -Werror -isrc test/ExampleWagerRoundMain.hs
```

Run at `108c6bf6` with GHC 9.6.7, all eight pass:

| Check | Expected |
| --- | --- |
| `parseGrammarV1StructuralSource`, then `grammarV1ProductionSourceCore` | both succeed |
| `grammarV1CheckedClosedRecordMode` on `Move` | `Linear` |
| `grammarV1CheckedProtocolBinderScope` on `WagerRound` | accepted |
| `grammarV1CheckedSemanticProtocolRoleTemplates` on `WagerRound` | accepted: the roles are dual |
| the Program role drops one round result | exactly `NonDualProtocolRoles Player Program` |
| the Program role reads a 16-byte nonce | exactly `NonDualProtocolRoles Player Program` |
| the Program role's `BothCommitted` carries the other side's pull | exactly `NonDualProtocolRoles Player Program` |
| `Move` declared `mode affine` | exactly `DeclaredModeWeakensDerived Linear Affine` |

Each edit is applied to the example's own text, once, and only to the role named. The third shows the limit of what
duality says: it is refused because the Player role still expects nothing, not because a payload there is forbidden.

## Not yet expressible

1. **The commitment.** The real rule is `hash == SHA-256(series || match || round || side || pull || nonce)`, a `when`
   guard on the reveal. Today `grammarV1RegisterSemanticClaimDeclaration` returns `Nothing` for a claim with a `Bytes`
   parameter, and `grammarV1CheckedSemanticProtocolRoleTemplates` returns `Nothing` for a protocol with a guard, so
   the example has neither. SHA-256's binding and hiding would be explicit assumptions.
2. **Records, data and refinements in messages.** Each of them in a message type makes the duality check return
   `Nothing`, so messages here are tuples and labels. With them, the reveal would carry a `Move`.
3. **Time.** Commits have deadlines, a missed commit plays a fallback committed when the series opened, and a reveal
   that misses its window (1 minute to 1 hour) forfeits the match. A session type fixes the order of messages, not
   when they arrive.
4. **Three parties.** The no-leak rule spans both players' sessions: A's reveal may reach B only after B has committed.
   With two-role protocols, that belongs to how the referee composes the two sessions; with the referee external, it
   is an assumption.
5. **Surviving a crash.** The player writes each nonce to disk before its commit is sent, so it can still reveal after
   a restart. Linearity covers one run, not that.
