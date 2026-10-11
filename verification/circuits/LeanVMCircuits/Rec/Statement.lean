module

public import LeanVMCircuits.Rec.Merkle

@[expose] public section

/-!
The hash of a list of 64-bit words in rows, and a tree statement's digest.

`Builder::chain` hashes `n` words as RFC 7693's BLAKE2s-256 of their `8n` little-endian bytes: one hash row per
64-byte block from the parameter IV, the words zero-padded to whole blocks, at least one block. A tree statement's
digest is that hash of a header of its kind's tag and item count, zeros to a block, and then its items' words; the
statement holds it as two `E` words, each two of its 64-bit words and a zero top limb.
-/

namespace LeanVMCircuits.Rec

open LeanVMCircuits.Blake2s Rfc7693

attribute [local irreducible] program

/-- Word `n` of a message, zero past its end. -/
def wordAt (ws : List (BitVec 64)) (n : ℕ) : BitVec 64 := ws.getD n 0

/-- Block `j` of a message's little-endian bytes, zero-padded: 32-bit word `r` is half `r % 2` of 64-bit word
`8j + r / 2`. -/
def block (ws : List (BitVec 64)) (j : ℕ) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun r => half (wordAt ws (8 * j + r.val / 2)) (r.val % 2)

/-- RFC 7693's block count `dd` of an `8n`-byte message: at least one. -/
def nBlocks (n : ℕ) : ℕ := max 1 ((n + 7) / 8)

/-- RFC 7693's BLAKE2s-256 of the `8n` little-endian bytes of `n` 64-bit words. -/
def hashWords (ws : List (BitVec 64)) : Vector (BitVec 32) 8 :=
  blake2s256 (BitVec.ofNat 64 (8 * ws.length)) (block ws 0)
    ((List.range (nBlocks ws.length - 1)).map fun j => block ws (j + 1))

/-- A tree statement's digest of `items` under the kind with tag `tag`: the hash of the header block, the tag and
the item count, and then the items' words. -/
def treeDigest (tag : BitVec 64) (items : List (Fin 4 → BitVec 64)) : Vector (BitVec 32) 8 :=
  hashWords ([tag, BitVec.ofNat 64 items.length, 0, 0, 0, 0, 0, 0] ++ items.flatMap fun d => List.ofFn d)

/-- A row whose message columns hold block `j`'s words hashes block `j`. -/
theorem msg_block (row : ℕ → K) (ws : List (BitVec 64)) (j : ℕ)
    (hm : ∀ i : Fin 8, columnWord row (hashM + i) = wordAt ws (8 * j + i)) : msg row = block ws j := by
  apply Vector.ext
  intro r hr
  simp only [msg, mWords, block, Vector.getElem_ofFn]
  have := hm ⟨r / 2, by omega⟩
  simp only [hashM] at this
  rw [this]

/-- `Builder::chain` in rows: hash rows chained from the parameter IV, one per block of the message, each one's
message columns its block's words, at RFC 7693's byte counts, output RFC 7693's hash of the message. -/
theorem chain_rows (ws : List (BitVec 64)) (row : ℕ → K) (rest : List (ℕ → K))
    (hlen : rest.length + 1 = nBlocks ws.length)
    (hc : ChainFrom (BitVec.ofNat 64 (8 * ws.length)) 0 row rest)
    (hiv : ∀ k : Fin 4, columnWord row (hashH + k) = digest paramIV k)
    (hm : ∀ j (hj : j < (row :: rest).length) (i : Fin 8),
      columnWord (row :: rest)[j] (hashM + i) = wordAt ws (8 * j + i)) :
    outWords (lastRow row rest) = digest (hashWords ws) := by
  have h0 : msg row = block ws 0 := msg_block row ws 0 (hm 0 (by simp))
  have hr : rest.map msg = (List.range (nBlocks ws.length - 1)).map fun j => block ws (j + 1) := by
    apply List.ext_getElem
    · simp; omega
    · intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact msg_block _ ws (j + 1) (hm (j + 1) (by simp only [List.length_map] at h1; simp; omega))
  rw [chain_digest _ 0 row rest paramIV hc hiv, hashWords, blake2s256, h0, hr]

/-- A tree statement's digest in rows: the chain's output is RFC 7693's hash of the header and the items, whose
words the rows' message columns hold. -/
theorem statement_digest (tag : BitVec 64) (items : List (Fin 4 → BitVec 64)) (row : ℕ → K)
    (rest : List (ℕ → K))
    (hlen : rest.length + 1 = nBlocks (8 + 4 * items.length))
    (hc : ChainFrom (BitVec.ofNat 64 (8 * (8 + 4 * items.length))) 0 row rest)
    (hiv : ∀ k : Fin 4, columnWord row (hashH + k) = digest paramIV k)
    (hm : ∀ j (hj : j < (row :: rest).length) (i : Fin 8),
      columnWord (row :: rest)[j] (hashM + i) =
        wordAt ([tag, BitVec.ofNat 64 items.length, 0, 0, 0, 0, 0, 0] ++ items.flatMap fun d => List.ofFn d)
          (8 * j + i)) :
    outWords (lastRow row rest) = digest (treeDigest tag items) := by
  have hn : ([tag, BitVec.ofNat 64 items.length, 0, 0, 0, 0, 0, 0] ++ items.flatMap fun d => List.ofFn d).length =
      8 + 4 * items.length := by
    simp [List.length_flatMap]
    omega
  apply chain_rows _ row rest _ _ hiv hm
  · rw [hn]; exact hlen
  · rw [hn]; exact hc

end LeanVMCircuits.Rec
