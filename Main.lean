import AlpenglowProver

def main : IO Unit := do
  let seed ← IO.monoNanosNow

  IO.println s!"Total stake: {totalStake} (~500 million)"

  let nodeCount := 50
  IO.println s!"Generating {nodeCount} nodes..."
  let nodes := NodesGenerator.genRandomNodes nodeCount (mkStdGen seed)
  -- printNodes nodes

  let slot : Slot := { number := 1 }
  let blockId := BlockId.ofSeed (seed + 1)
  let expectedCert := CertKind.skipFallback
  IO.println s!"Generating votes for slot {slot.number} with expected cert: {expectedCert}"
  let votes :=
    VotesGenerator.generateRandomVotes slot nodes expectedCert blockId (mkStdGen (seed + 1))
  -- printVotes votes
  IO.println s!"Block ID: {blockId}"

  let tally := VotesTally.aggregate votes
  printVotesTally tally
