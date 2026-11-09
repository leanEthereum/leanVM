/-
  LeanVM.Guest.B1.Sig.SphincsAdrs

  FIPS 205's 32-byte address as the guest's two cells (leanVM main 40f877dc,
  `lean_ethereum.py:483-500`, `crates/signatures/src/lean_sphincs/hash.rs:28-79`).
-/

module

public import LeanVM.Guest.B1.Sig.Interface

/-!
# The address as two cells

FIPS 205's address (`Adrs`, `hash.rs:28-79`) is 32 bytes, eight big-endian 32-bit words: the
layer (bytes `0..4`), the tree (`4..16`, its high word zero here), the type (`16..20`), then the
key pair, the chain index or tree height, and the hash address or tree index. A hash input
`PK.seed | ADRS | M` is cells' bytes (each cell 16 bytes, little-endian), so the address is two
cells: `A0`, bytes `0..16`, and `A1`, bytes `16..32` (`lean_ethereum.py:483-500`). In a cell a
big-endian word's low byte is its last byte: `beWordAt k w` is the number the word `w` at word slot
`k` of a half adds to its cell.

* `adrsCell0 layer tree`, `adrsCell1 type keyPair word2 word3`: the two cells;
* `keyAdrsCells layer tree leaf`: the address of a one-time key, type `WOTS_HASH` (`0`), its leaf
  the key pair (`OtsKey::adrs`, `wots.rs:41-44`): the `(a0, a1)` `sp_wots` takes;
* the types (`hash.rs:20-27`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest

@[expose] public section

/-- The address types (`hash.rs:20-27`). -/
def adrsWotsHash : Nat := 0
def adrsWotsPk : Nat := 1
def adrsTree : Nat := 2
def adrsForsTree : Nat := 3
def adrsForsRoots : Nat := 4
def adrsWotsEnc : Nat := 7

/-- **A big-endian 32-bit word at word slot `k` of a 16-byte half**, as the number it adds to the
half's cell: its bytes reversed, the low byte at the slot's last byte. -/
def beWordAt (k w : Nat) : Nat :=
  2 ^ (32 * k) * (w / 2 ^ 24 % 256 + 2 ^ 8 * (w / 2 ^ 16 % 256) + 2 ^ 16 * (w / 2 ^ 8 % 256) +
    2 ^ 24 * (w % 256))

/-- **The address's first cell**, bytes `0..16`: the layer (word `0`), the tree (words `2`, `3`;
word `1`, the tree's high bytes, zero). -/
def adrsCell0 (layer tree : Nat) : E :=
  cellOf128 (BitVec.ofNat 128 (beWordAt 0 layer + beWordAt 2 (tree / 2 ^ 32) + beWordAt 3 tree))

/-- **The address's second cell**, bytes `16..32`: the type, the key pair, the chain index or tree
height, the hash address or tree index. -/
def adrsCell1 (type keyPair word2 word3 : Nat) : E :=
  cellOf128 (BitVec.ofNat 128
    (beWordAt 0 type + beWordAt 1 keyPair + beWordAt 2 word2 + beWordAt 3 word3))

/-- **The address of the one-time key `(layer, tree, leaf)`**, type `WOTS_HASH`, its leaf the key
pair: `sp_wots`'s `(a0, a1)`. -/
def keyAdrsCells (layer tree leaf : Nat) : E × E :=
  (adrsCell0 layer tree, adrsCell1 adrsWotsHash leaf 0 0)

end
end LeanVM.Guest.B1.Sig
