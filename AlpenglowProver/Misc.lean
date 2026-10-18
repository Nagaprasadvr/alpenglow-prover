/-!
# Miscellaneous helpers

Base58 encoding and decoding (Bitcoin/Solana alphabet).
-/

namespace Base58

/-- The Base58 alphabet (no `0`, `O`, `I` or `l`). -/
def alphabet : List Char :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList

/-- Interpret bytes as a big-endian natural number. -/
def bytesToNat (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Convert a natural number to its Base58 digits, prepended to `acc`. -/
def natToBase58 (n : Nat) (acc : List Char := []) : List Char :=
  if h : n = 0 then acc
  else natToBase58 (n / 58) (alphabet[n % 58]! :: acc)
termination_by n
decreasing_by omega

/-- Convert a natural number to big-endian bytes, prepended to `acc`. -/
def natToBytes (n : Nat) (acc : List UInt8 := []) : List UInt8 :=
  if h : n = 0 then acc
  else natToBytes (n / 256) ((n % 256).toUInt8 :: acc)
termination_by n
decreasing_by omega

/-- Encode bytes as a Base58 string. Each leading `0x00` byte becomes a `'1'`. -/
def encode (bs : List UInt8) : String :=
  let zeros := (bs.takeWhile (· == 0)).length
  String.ofList (List.replicate zeros '1' ++ natToBase58 (bytesToNat bs))

/-- Decode a Base58 string into bytes, or `none` if it contains an invalid character. -/
def decode (s : String) : Option (List UInt8) := do
  let cs := s.toList
  let zeros := (cs.takeWhile (· == '1')).length
  let n ← cs.foldlM (init := 0) fun (acc : Nat) c => do
    let d ← alphabet.findIdx? (· == c)
    pure (acc * 58 + d)
  pure (List.replicate zeros 0 ++ natToBytes n)

#guard encode "Hello World!".toUTF8.toList == "2NEpo7TZRRrLZSi2U"
#guard decode "2NEpo7TZRRrLZSi2U" == some "Hello World!".toUTF8.toList

end Base58
