import AlpenglowProver.Node

/-!
# Votor

Votes, certificates, vote tallies, and a random vote generator.
-/

/-! Thresholds for the different vote and certificate kinds, in bp of total stake. -/
namespace VoteThresholds

def fastFinalization : Nat := 8000
def notarization : Nat := 6000
def notarFallback : Nat := 6000
def skip : Nat := 6000
def finalization : Nat := 6000

end VoteThresholds

/-- Whether `stake` is at least `threshold` basis points of total stake (exact, no division). -/
def meetsThreshold (stake threshold : Nat) : Bool :=
  stake * bpDenom ≥ threshold * totalStake

/-- A slot in the blockchain, identified by its number. -/
structure Slot where
  number : Nat
  deriving Repr, BEq

/-- A block identifier, represented by its hash. -/
structure BlockId where
  hash : List UInt8
  deriving Repr, BEq

/-- Base58 representation of a block id. -/
def BlockId.toString (blockId : BlockId) : String :=
  Base58.encode blockId.hash

instance : ToString BlockId := ⟨BlockId.toString⟩

/-- A deterministic 32-byte block id derived from `seed`. -/
def BlockId.ofSeed (seed : Nat) : BlockId :=
  { hash := (List.range 32).map fun i => ((seed + i) % 256).toUInt8 }

/-- The kinds of votes nodes can cast. -/
inductive VoteKind where
  | notar
  | skip
  | notarFallback
  | skipFallback
  | final
  deriving Repr, BEq

def VoteKind.toString : VoteKind → String
  | .notar => "Notar"
  | .skip => "Skip"
  | .notarFallback => "NotarFallback"
  | .skipFallback => "SkipFallback"
  | .final => "Final"

instance : ToString VoteKind := ⟨VoteKind.toString⟩

def VoteKind.all : List VoteKind :=
  [.notar, .skip, .notarFallback, .skipFallback, .final]

/-- The kinds of certificates that can be formed from votes. -/
inductive CertKind where
  | notarization
  | fastFinalization
  | notarFallback
  | skip
  | skipFallback
  | finalization
  | invalid
  deriving Repr, BEq

def CertKind.toString : CertKind → String
  | .notarization => "Notarization"
  | .fastFinalization => "FastFinalization"
  | .notarFallback => "NotarFallback"
  | .skip => "Skip"
  | .skipFallback => "SkipFallback"
  | .finalization => "Finalization"
  | .invalid => "Invalid"

instance : ToString CertKind := ⟨CertKind.toString⟩

def CertKind.all : List CertKind :=
  [.notarization, .fastFinalization, .notarFallback, .skip, .skipFallback, .finalization,
    .invalid]

/-- The stake threshold (in bp) needed to form a certificate of this kind. -/
def CertKind.toVoteThreshold : CertKind → Nat
  | .fastFinalization => VoteThresholds.fastFinalization
  | .notarization => VoteThresholds.notarization
  | .notarFallback => VoteThresholds.notarFallback
  | .skip => VoteThresholds.skip
  | .skipFallback => VoteThresholds.skip
  | .finalization => VoteThresholds.finalization
  | .invalid => 0

/-- The vote kind that primarily contributes to a certificate of this kind. -/
def CertKind.toVoteKind : CertKind → VoteKind
  | .notarization => .notar
  | .fastFinalization => .notar
  | .notarFallback => .notarFallback
  | .skip => .skip
  | .skipFallback => .skipFallback
  | .finalization => .final
  | .invalid => .notar

/-- A vote cast by a node for a specific slot and block. -/
structure Vote where
  slot : Slot
  node : Node
  kind : VoteKind
  blockId : BlockId
  deriving Repr, BEq

/-- Stake voted, by vote kind. -/
structure VotesTally where
  notar : Nat := 0
  notarFallback : Nat := 0
  skip : Nat := 0
  skipFallback : Nat := 0
  final : Nat := 0
  deriving Repr, BEq

namespace VotesTally

def empty : VotesTally := {}

/-- Add a vote's stake to the matching bucket. -/
def addVote (t : VotesTally) (vote : Vote) : VotesTally :=
  let s := vote.node.stake
  match vote.kind with
  | .notar => { t with notar := t.notar + s }
  | .notarFallback => { t with notarFallback := t.notarFallback + s }
  | .skip => { t with skip := t.skip + s }
  | .skipFallback => { t with skipFallback := t.skipFallback + s }
  | .final => { t with final := t.final + s }

/-- Total stake that has voted. -/
def total (t : VotesTally) : Nat :=
  t.notar + t.notarFallback + t.skip + t.skipFallback + t.final

/-- Stake that has not voted. -/
def missing (t : VotesTally) : Nat :=
  totalStake - t.total

/-- Aggregate a list of votes into a single tally. -/
def aggregate (votes : List Vote) : VotesTally :=
  votes.foldl addVote empty

/-- Compute the certificate formed by a tally. -/
def computeCert (vt : VotesTally) : CertKind :=
  -- fast finalization: notar ≥ 80%
  if meetsThreshold vt.notar VoteThresholds.fastFinalization then
    .fastFinalization
  -- notarization: notar ≥ 60%
  else if meetsThreshold vt.notar VoteThresholds.notarization then
    .notarization
  -- notar fallback: notar + notar-fallback ≥ 60%
  else if meetsThreshold (vt.notar + vt.notarFallback) VoteThresholds.notarFallback then
    .notarFallback
  -- skip fallback: skip + skip-fallback ≥ 60%
  else if meetsThreshold (vt.skip + vt.skipFallback) VoteThresholds.skip then
    .skipFallback
  -- finalization: final ≥ 60% (given notarization was already achieved)
  else if meetsThreshold vt.final VoteThresholds.finalization then
    .finalization
  else
    .invalid

end VotesTally

namespace VotesGenerator

/-- Generate a random vote for `slot` and `node`, never of kind `excludeKind`.
Returns the vote and the advanced generator. -/
def generateRandomVote (slot : Slot) (node : Node) (blockId : BlockId) (g : StdGen)
    (excludeKind : VoteKind) : Vote × StdGen :=
  let kinds := VoteKind.all.filter (· != excludeKind)
  let (idx, g') := randNat g 0 (kinds.length - 1)
  let kind := kinds[idx]?.getD .notar
  ({ slot, node, blockId, kind }, g')

/-- Generate votes for `slot` such that the tally yields `expectedCert`: the heaviest nodes vote
for it until its threshold is reached, the rest vote randomly for other kinds. -/
def generateRandomVotes (slot : Slot) (nodes : List Node) (expectedCert : CertKind)
    (blockId : BlockId) (g : StdGen) : List Vote := Id.run do
  let mut g := g
  let mut votes : Array Vote := #[]
  let nodesStake := nodes.foldl (fun acc n => acc + n.stake) 0
  let expectedThreshold := expectedCert.toVoteThreshold * nodesStake / bpDenom
  let mut currentStakeAcc := 0
  let nodesOrdByStake := nodes.toArray.qsort (fun a b => a.stake > b.stake)
  for node in nodesOrdByStake do
    let mut kind := expectedCert.toVoteKind
    if currentStakeAcc ≤ expectedThreshold then
      if expectedCert == .notarFallback then
        let (choice, g') := randBool g
        g := g'
        kind := if choice then .notar else .notarFallback
      if expectedCert == .skipFallback then
        let (choice, g') := randBool g
        g := g'
        kind := if choice then .skip else .skipFallback
      votes := votes.push { slot, node, blockId, kind }
    else
      let (vote, g') := generateRandomVote slot node blockId g expectedCert.toVoteKind
      g := g'
      votes := votes.push vote
    currentStakeAcc := currentStakeAcc + node.stake
  return votes.toList

end VotesGenerator

/-- Print a tally as percentages of total stake, and the certificate it forms. -/
def printVotesTally (tally : VotesTally) : IO Unit := do
  IO.println s!"Votes tally (% of stake): Notar: {stakePct tally.notar}, \
    Notar Fallback: {stakePct tally.notarFallback}, Skip: {stakePct tally.skip}, \
    Skip Fallback: {stakePct tally.skipFallback}, Final: {stakePct tally.final}"
  IO.println s!"Computed cert: {tally.computeCert}"

/-- Print each vote's slot, node and kind. -/
def printVotes (votes : List Vote) : IO Unit := do
  for vote in votes do
    IO.println s!"Generated vote for slot {vote.slot.number}: Node {vote.node.pubkey}, \
      Kind: {vote.kind}"
