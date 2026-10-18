# Alpenglow: How It Works and What You Need to Prove

A study guide for formalizing Solana's Alpenglow consensus in Lean.
Reference: the Alpenglow whitepaper v1.1 and SIMD-0326. When this guide and the
whitepaper disagree, the whitepaper wins. Check every rule below against it
before you encode it.

---

## 1. The big picture

Alpenglow replaces Solana's TowerBFT voting, Proof of History, and gossip-based
vote propagation. It has two parts:

- **Rotor** gets the leader's block to everyone. The leader erasure-codes the
  block into shreds, sends each shred to a relay, and each relay broadcasts it
  to all validators. Any sufficiently large subset of shreds reconstructs the
  block.
- **Votor** decides which blocks are final. Validators vote directly to each
  other; there are no vote transactions on-chain.

Time is divided into **slots** (about 400 ms). Consecutive slots are grouped
into **leader windows** (4 slots), and one leader produces all blocks in its
window. There is no global clock, only local timeouts.

For formal proofs, **Votor is where safety lives**. Rotor matters for liveness
and performance, and you can usually treat it as an abstract "blocks eventually
arrive" assumption.

---

## 2. System model and assumptions

| Assumption | Meaning |
|---|---|
| Stake-weighted validators | Every threshold is a fraction of total stake, not a count of nodes |
| Byzantine stake < 20% | Faulty validators may do anything: equivocate, lie, stay silent |
| Plus up to 20% crashed | Extra validators may be offline but not malicious (the "20+20" model) |
| Authenticated messages | Votes are signed; nobody can forge a correct node's vote |
| Partial synchrony | Messages can be delayed arbitrarily, but after some unknown time (GST) they arrive within a bound Δ |

**Safety needs only the first four.** It must hold even if the network is
completely asynchronous. **Liveness needs partial synchrony**, because no
protocol can make progress while messages never arrive.

---

## 3. Votes

In each slot `s`, a validator can cast these votes:

| Vote | When a correct node casts it |
|---|---|
| `NotarVote(s, b)` | It received block `b` for slot `s` and `b`'s parent is ready (see §5) |
| `SkipVote(s)` | Its timeout for slot `s` fired before it voted |
| `NotarFallbackVote(s, b)` | The `SafeToNotar` condition holds for `b` (see §6) |
| `SkipFallbackVote(s)` | The `SafeToSkip` condition holds (see §6) |
| `FinalVote(s)` | It saw `b` notarized, it notar-voted `b`, and it cast no fallback or skip vote in the window |

**The key per-node rule:** a correct node casts **exactly one** initial vote per
slot, either one `NotarVote` or one `SkipVote`. Fallback votes are added on top
of the initial vote, never instead of it.

---

## 4. Certificates

A certificate is a set of votes whose stake crosses a threshold.

| Certificate | Built from | Threshold | Meaning |
|---|---|---|---|
| Fast-finalization | `NotarVote(b)` | ≥ 80% | `b` is final after one round |
| Notarization | `NotarVote(b)` | ≥ 60% | `b` is locked in; can become final |
| Notar-fallback | `NotarVote(b)` or `NotarFallbackVote(b)` | ≥ 60% | `b` can be built on, but is not final |
| Skip | `SkipVote` or `SkipFallbackVote` | ≥ 60% | slot `s` produced no block |
| Finalization | `FinalVote(s)` | ≥ 60% | with a notarization of `b`, `b` is final |

A block `b` in slot `s` is **finalized** if either:

- **Fast path:** a fast-finalization certificate exists for `b`, or
- **Slow path:** a notarization certificate for `b` and a finalization
  certificate for `s` both exist.

The two paths run concurrently. The fast path finishes in one round when 80% is
responsive; otherwise the slow path finishes in two rounds with 60%.

---

## 5. Parents and chains

Blocks form a chain. Each block names a parent block in an earlier slot.
A correct node only notar-votes block `b` in slot `s` if its parent is safe to
build on:

- **First slot of a window:** the node must have seen `ParentReady(s, p)`. This
  holds when parent `p` has a notarization or notar-fallback certificate, and
  **every slot between `p` and `s` has a skip certificate**.
- **Later slots in a window:** the parent must be the block from the previous
  slot of the same window, and the node must have notar-voted it.

This rule is what connects slots together, and it is the heart of the
cross-slot safety proof.

---

## 6. The unhappy path: timeouts and fallbacks

**Timeouts.** When a node gets `ParentReady` for the first slot of a window, it
starts one timeout per slot in the window. If a slot's timeout fires before the
node voted in it, the node casts `SkipVote` for every slot in the window it has
not voted in yet, and marks the window as bad (`BadWindow`).

**Why fallbacks exist.** Suppose a Byzantine leader sends block `b` to half the
validators and block `b′` to the other half. Nothing reaches 60%, and without
extra rules the slot could stall forever. Fallback votes let correct nodes
converge on *some* certificate, either for one block or for a skip.

**`SafeToNotar(s, b)`.** A node that already voted in slot `s`, but not for `b`,
may add a `NotarFallbackVote(b)` when either:

- `notar(b) ≥ 40%`, or
- `skip(s) + notar(b) ≥ 60%` and `notar(b) ≥ 20%`.

Intuition: enough stake supports `b` that no *other* block could still reach the
80% fast-finalization threshold.

**`SafeToSkip(s)`.** A node that already voted in slot `s`, but not to skip,
may add a `SkipFallbackVote` when:

- `skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%`

Intuition: support has scattered away from the leading block enough that it
can no longer be fast-finalized.

A node that has cast `FinalVote` in a slot never casts fallback votes there, and
a node that cast any fallback or skip vote never casts `FinalVote`.

---

## 7. What you need to prove

### 7.1 Safety (the main goal)

> **Theorem (Safety).** If block `b` is finalized in slot `s`, then every block
> that is finalized in any later slot descends from `b`.
>
> Consequence: two conflicting blocks are never both finalized.

This must hold under Byzantine stake < 20% with **no timing assumptions**.

Break it into these lemmas, roughly in this order:

**Lemma 1: at most one notarized block per slot.**
Two notarization certificates for `b ≠ b′` in slot `s` need 60% + 60% = 120% of
stake, so their voters overlap in at least 20%. Byzantine stake is below 20%,
so a correct node is in the overlap and cast two `NotarVote`s in one slot. That
breaks the one-initial-vote rule.

*Proof technique:* quorum intersection. This is the single most important
counting argument; every later lemma reuses it.

**Lemma 2: slow finalization blocks every rival certificate in its slot.**
If a finalization certificate exists for `s` and `b` is notarized, then:

- no skip certificate exists for `s`, and
- no notarization or notar-fallback certificate exists for any `b′ ≠ b`.

*Why:* correct `FinalVote` voters hold more than 40% of stake. They never cast
skip or fallback votes, and they notar-voted only `b`. So any rival certificate
must come from the remaining stake, which is less than 60%.

**Lemma 3: fast finalization blocks every rival certificate in its slot.**
Same conclusion as Lemma 2, starting from a fast-finalization certificate.

*Why:* correct `NotarVote(b)` voters hold more than 60%. This is where you must
use the exact `SafeToNotar` and `SafeToSkip` conditions, to show those voters
never add fallback votes for rivals and the remaining stake cannot trigger them.

**Lemma 4: a finalized slot is never skipped, and its block is the only
certified block there.** Combines Lemmas 2 and 3.

**Lemma 5 (cross-slot): every certified block in a later slot descends from `b`.**
By induction on the later slot `s′`:

- A correct node only notar-votes a block whose parent is certified and whose
  gap slots are all skip-certified (§5).
- Every certificate contains at least one correct voter, since 60% > 20%.
- So every certified block's ancestry is a chain of certified blocks bridged by
  skip-certified slots.
- Slot `s` cannot be skipped (Lemma 4), so the chain cannot jump over it.
  The only certified block in `s` is `b`, so the chain passes through `b`.

Watch out for the within-window case: a later slot of the same window uses the
previous slot's block as parent, not a `ParentReady` certificate, so your
induction must handle both parent rules.

**Safety theorem** then follows: a finalized block is certified, so by Lemma 5
it descends from `b`.

### 7.2 Liveness (the harder, optional second goal)

> **Theorem (Liveness).** After GST, if the leader of a window is correct, all
> correct nodes finalize the leader's blocks for that window.

Supporting results you will need:

- **No stall:** every slot eventually gets either a notarization or notar-fallback
  certificate, or a skip certificate. Fallback votes exist to guarantee this.
- **ParentReady propagates:** if correct nodes get `ParentReady` for a window,
  they eventually all get it, so they all start timeouts.
- **Timeouts are long enough:** after GST, a correct leader's blocks reach
  correct nodes before their timeouts fire.
- **Enough responsive stake:** with at most 20% Byzantine and 20% crashed, at
  least 60% is correct and online, so the slow path can always complete.

Liveness needs a model of **time and message delivery**, which is much more
work in Lean than the safety model. Do safety first.

### 7.3 Rotor (optional)

- **Resilience:** if a relay set with enough correct stake receives the shreds,
  every correct node can reconstruct the block.
- This is a probabilistic / combinatorial claim and usually stated separately
  from consensus safety. Most formalizations assume it.

---

## 8. Modeling decisions you must make in Lean

These choices shape everything that follows. Decide them before writing proofs.

1. **Vote-level or message-level model?**
   *Vote-level:* record only which votes each validator cast, and constrain
   correct validators by the rules. Enough for safety, much simpler.
   *Message-level:* model sending, receiving, local state, and events. Needed for
   liveness.

2. **How to represent stake.** A finite list of validators with weights, and
   sets of validators as Boolean predicates, keeps you independent of Mathlib.
   Mathlib's `Finset.sum` gives more library support but a heavier setup.

3. **How to state thresholds.** Integer inequalities avoid fractions:
   `5 * x ≥ 3 * T` for 60%, `5 * x ≥ 4 * T` for 80%, `5 * x ≥ 2 * T` for 40%,
   `5 * x ≥ T` for 20%, and `5 * byz < T` for the fault bound. Then the
   `omega` tactic can close the arithmetic.

4. **How to model Byzantine behavior.** Simplest: Byzantine validators may have
   cast any set of votes, and only correct validators are constrained.

5. **How faithful the fallback rules are.** Simplified conditions are easier but
   may not match the real protocol. If you simplify, prove that the real
   condition implies your simplified one, otherwise your theorem may not apply
   to Alpenglow.

---

## 9. Suggested build order in Lean

| Step | Build | New Lean skills |
|---|---|---|
| 1 | Stake function over a list of validators | Recursive definitions |
| 2 | Stake ≤ total | Induction, `by_cases`, `omega` |
| 3 | Inclusion–exclusion, disjoint-sets bound, honest/Byzantine split, "positive stake ⇒ someone is in the set" | Harder induction |
| 4 | `Vote` type, the model structure, certificate definitions, honesty rules | `inductive`, `structure` |
| 5 | Lemma 1 | Combining lemmas, extracting a witness |
| 6 | Lemmas 2–4 | Disjointness arguments |
| 7 | Parent relation, `ParentReady`, Lemma 5, Safety theorem | Induction over slots, chains |
| 8 | (Optional) State machine, time, Liveness | Transition systems, invariants |

Steps 1–6 prove same-slot safety. Step 7 is full safety. Step 8 is a research
project in its own right.

---

## 10. References

- Alpenglow whitepaper v1.1 (Anza): full protocol, proofs of safety and liveness
- SIMD-0326: the Solana improvement proposal specifying Alpenglow
- Quint specification of Alpenglow Votor (quint.sh blog): an executable model,
  useful for checking your understanding of the state machine
- *Theorem Proving in Lean 4* and the Natural Number Game: for the Lean side
