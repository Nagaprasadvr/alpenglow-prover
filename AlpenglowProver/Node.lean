import AlpenglowProver.Misc

/-!
# Nodes

Network nodes, their stake, and a random generator for test networks.
-/

/-- Total stake in the network (approximately Solana's). -/
def totalStake : Nat := 500_000_000

/-- Denominator for fractions expressed in basis points (1 bp = 0.01%). -/
def bpDenom : Nat := 10_000

/-- Maximum allowed Byzantine stake (20% of total stake), in bp. -/
def maxByzantineStakeBp : Nat := 2000

/-- Length of a public key, in bytes. -/
def pubkeyLength : Nat := 32

/-- A fixed-length public key identifying a node. -/
structure Pubkey where
  bytes : Vector UInt8 pubkeyLength
  deriving BEq

/-- Base58 representation of a public key. -/
def Pubkey.toString (pk : Pubkey) : String :=
  Base58.encode pk.bytes.toList

instance : ToString Pubkey := ⟨Pubkey.toString⟩

instance : Repr Pubkey where
  reprPrec pk _ := .text pk.toString

/-- A node in the network, identified by its pubkey, with its stake. -/
structure Node where
  pubkey : Pubkey
  stake : Nat
  isByzantine : Bool
  deriving Repr, BEq

/-- Stake as a percentage of total stake (`Float`, for display only). -/
def stakePct (stake : Nat) : Float :=
  stake.toFloat * 100 / totalStake.toFloat

namespace NodesGenerator

/-- Generate `n` nodes (some Byzantine) with random stakes summing to `totalStake`,
no node holding ≥ 50%. Returns `[]` when `n < 3`, since then some node must hold ≥ 50%. -/
def genRandomNodes (n : Nat) (g : StdGen) : List Node := Id.run do
  if n < 3 then return []

  -- 1%–10% below the bound, so Byzantine stake is 10%–19%
  let (marginBp, g) := randNat g 100 1000
  let mut g := g
  let byzantineStakeBp := maxByzantineStakeBp - marginBp
  dbg_trace s!"Byzantine stake % = {byzantineStakeBp / 100}%"
  let byzantineStake := byzantineStakeBp * totalStake / bpDenom

  -- 1. heavy-tailed random weights: digit × 10^mag
  let mut ws : Array Nat := #[]
  for _ in [0:n] do
    let (mag, g2) := randNat g 0 4
    let (d, g3) := randNat g2 1 9
    g := g3
    ws := ws.push (d * 10 ^ mag)

  -- 2. if the largest weight ≥ sum of the rest, cap it below (→ share < 50%)
  let m := ws.foldl max 0
  let rest := ws.foldl (· + ·) 0 - m
  if m ≥ rest then
    ws := ws.map fun w => if w = m then rest - 1 else w

  -- 3. scale weights to `totalStake` (multiply before dividing)
  let sumW := ws.foldl (· + ·) 0
  let mut stakes := ws.map fun w => w * totalStake / sumW

  -- 4. the rounding leftover goes to the smallest node, so the sum is exact
  let leftover := totalStake - stakes.foldl (· + ·) 0
  let mut minIdx := 0
  for i in [0:n] do
    if ws[i]! < ws[minIdx]! then minIdx := i
  stakes := stakes.modify minIdx (· + leftover)

  let mut currentByzantineStake := 0
  let mut out : Array Node := #[]
  for i in [0:n] do
    let pubkey := Pubkey.mk (Vector.replicate pubkeyLength (UInt8.ofNat i))
    let stake := stakes[i]!
    let mut isByzantine := false
    if currentByzantineStake + stake ≤ byzantineStake then
      let (maybeByzantine, g') := randBool g
      g := g'
      if maybeByzantine then
        isByzantine := true
        currentByzantineStake := currentByzantineStake + stake
    out := out.push { pubkey, stake, isByzantine }
  return out.toList

end NodesGenerator

/-- Print each node with its stake and Byzantine flag. -/
def printNodes (nodes : List Node) : IO Unit := do
  for node in nodes do
    IO.println s!"Generated node: {node.pubkey}, Stake: {node.stake}, \
      Stake %: {stakePct node.stake}, isByzantine: {node.isByzantine}"
