import AlpenglowProver.Votor
import AlpenglowProver.Node

/-!
# Alpenglow (Votor) — notarization safety

Self-contained: the model section mirrors your `Node` / `Vote` / `VoteKind`
with the changes the proofs need:

* notar-type votes carry the `BlockId` they vote for,
* votes name their voter by `pubkey` (stake is looked up from the node list),
* stake that "voted X" is counted once per node (filter the nodes), never per vote,
* types derive `DecidableEq` (not just `BEq`).

Main result: `notar_unique` — with < 20% Byzantine stake and honest nodes
notar-voting at most once per slot, two different blocks can never both be
notarized in the same slot.
-/

/-- Total stake of a list of nodes (recursive, so induction follows it). -/
def sumStake : List Node → Nat
  | []      => 0
  | n :: ns => n.stake + sumStake ns

/-- Did node `n` cast a notar vote for block `b` in `slot`? -/
def votedNotar (votes : List Vote) (slot : Slot) (b : BlockId) (n : Node) : Bool :=
  votes.any fun v => v.slot == slot && v.node.pubkey == n.pubkey && v.kind == VoteKind.notar && v.blockId == b

/-- Block `b` is notarized in `slot`: nodes that notar-voted for it hold ≥ 60% of stake. -/
def Notarized (votes : List Vote) (ns : List Node) (slot : Slot) (b : BlockId) : Prop :=
  sumStake (ns.filter (votedNotar votes slot b)) * bpDenom
    ≥ VoteThresholds.notarization * sumStake ns

/-- Byzantine nodes hold strictly less than 20% of stake. -/
def ByzantineBound (ns : List Node) : Prop :=
  sumStake (ns.filter (·.isByzantine)) * bpDenom < maxByzantineStakeBp * sumStake ns

/-- Honest behavior: a correct node notar-votes for at most one block per slot. -/
def HonestVotesOnce (votes : List Vote) (ns : List Node) : Prop :=
  ∀ n ∈ ns, n.isByzantine = false →
    ∀ slot b₁ b₂, votedNotar votes slot b₁ n = true → votedNotar votes slot b₂ n = true →
      b₁ = b₂

/-! ## 1. Thresholds -/

/-- A fast-finalization quorum (≥ 80%) is also a notarization quorum (≥ 60%). -/
theorem fast_implies_notar (stake : Nat) :
    meetsThreshold stake VoteThresholds.fastFinalization = true →
    meetsThreshold stake VoteThresholds.notarization = true := by
  intro h
  simp only [meetsThreshold, VoteThresholds.fastFinalization,
    VoteThresholds.notarization, bpDenom, ge_iff_le, decide_eq_true_eq] at h ⊢
  omega

/-! ## 2. Stake accounting -/

/-- Voters for A + voters for B ≤ everyone + voters for both. -/
theorem sumStake_incl_excl (p q : Node → Bool) (ns : List Node) :
    sumStake (ns.filter p) + sumStake (ns.filter q)
      ≤ sumStake ns + sumStake (ns.filter fun n => p n && q n) := by
  induction ns with
  | nil => simp [sumStake]
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;>
      simp [hp, hq, sumStake] <;> omega

/-- Any group's stake ≤ its honest part + all Byzantine stake. -/
theorem sumStake_le_honest_add_byz (s : Node → Bool) (ns : List Node) :
    sumStake (ns.filter s)
      ≤ sumStake (ns.filter fun n => s n && !n.isByzantine)
        + sumStake (ns.filter (·.isByzantine)) := by
  induction ns with
  | nil => simp [sumStake]
  | cons x xs ih =>
    cases hs : s x <;> cases hb : x.isByzantine <;>
      simp [hs, hb, sumStake] <;> omega

/-- If a group has positive stake, some node in the list belongs to it. -/
theorem exists_of_sumStake_pos (p : Node → Bool) (ns : List Node)
    (h : sumStake (ns.filter p) > 0) : ∃ n ∈ ns, p n = true := by
  induction ns with
  | nil => simp [sumStake] at h
  | cons x xs ih =>
    by_cases hp : p x = true
    · exact ⟨x, by simp, hp⟩
    · have h' : sumStake (xs.filter p) > 0 := by
        simpa [List.filter_cons, hp, sumStake] using h
      obtain ⟨n, hn, hpn⟩ := ih h'
      exact ⟨n, by simp [hn], hpn⟩

/-! ## 3. Quorum intersection -/

-- omega's proof term grows with the bp-sized coefficients; raise the depth limit.
set_option maxRecDepth 100000 in
/-- Two 60% quorums overlap in at least 20% of stake. -/
theorem quorum_intersection (p q : Node → Bool) (ns : List Node)
    (hp : sumStake (ns.filter p) * bpDenom ≥ VoteThresholds.notarization * sumStake ns)
    (hq : sumStake (ns.filter q) * bpDenom ≥ VoteThresholds.notarization * sumStake ns) :
    sumStake (ns.filter fun n => p n && q n) * bpDenom ≥ 2000 * sumStake ns := by
  have h := sumStake_incl_excl p q ns
  simp only [bpDenom, VoteThresholds.notarization] at hp hq ⊢
  omega

/-! ## 4. Honest node in the overlap -/

set_option maxRecDepth 100000 in
/-- With < 20% Byzantine stake, two 60% quorums share an honest node. -/
theorem honest_in_overlap (p q : Node → Bool) (ns : List Node)
    (hp : sumStake (ns.filter p) * bpDenom ≥ VoteThresholds.notarization * sumStake ns)
    (hq : sumStake (ns.filter q) * bpDenom ≥ VoteThresholds.notarization * sumStake ns)
    (hbyz : ByzantineBound ns) :
    ∃ n ∈ ns, p n = true ∧ q n = true ∧ n.isByzantine = false := by
  have hboth  := quorum_intersection p q ns hp hq
  have hsplit := sumStake_le_honest_add_byz (fun n => p n && q n) ns
  unfold ByzantineBound at hbyz
  have hpos : sumStake (ns.filter fun n => (p n && q n) && !n.isByzantine) > 0 := by
    simp only [bpDenom, maxByzantineStakeBp] at hboth hbyz
    omega
  obtain ⟨n, hn, h⟩ := exists_of_sumStake_pos _ ns hpos
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨n, hn, h.1.1, h.1.2, h.2⟩

/-! ## 5. Notarization uniqueness -/

/-- At most one block per slot can be notarized. -/
theorem notar_unique (votes : List Vote) (ns : List Node) (slot : Slot) (b₁ b₂ : BlockId)
    (hbyz : ByzantineBound ns) (hhonest : HonestVotesOnce votes ns)
    (h₁ : Notarized votes ns slot b₁) (h₂ : Notarized votes ns slot b₂) :
    b₁ = b₂ := by
  obtain ⟨n, hn, hv₁, hv₂, hhon⟩ := honest_in_overlap _ _ ns h₁ h₂ hbyz
  exact hhonest n hn hhon slot b₁ b₂ hv₁ hv₂



#print axioms fast_implies_notar
#print axioms sumStake_incl_excl
#print axioms sumStake_le_honest_add_byz
#print axioms exists_of_sumStake_pos
#print axioms quorum_intersection
#print axioms honest_in_overlap
#print axioms notar_unique
