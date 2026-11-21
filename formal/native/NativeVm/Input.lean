module

public import Native.QM
public import LeanVM.Wire.Encoding

/-!
# The leanVM verifier's memory

The verifier takes one argument, in `rdi`: a context of 64-bit words. Its first words point to the
inputs and to the working areas; the caller fills the inputs and allocates the working areas at the
sizes `WorkSizes` asks for, every area 8-byte aligned and the areas pairwise disjoint.

| word of the context | holds |
|---|---|
| `0`, `1` | the proof's wire bytes: their address and their byte count `L` (the bytes packed little-endian into words, the last word's bytes past `L` zero) |
| `2`, `3` | the bytecode: the address of its `K` words, one word each, and their count |
| `4 .. 7` | the public input's digest, its four words |
| `8`, `9` | the decoded proof's area (`Decoded`) and its size in words |
| `10`, `11` | the working area and its size in words |
| `16 .. 21` | the save area: `rbx`, `rbp`, `r12`, `r13`, `r14`, `r15` |
| `32 ..` | scratch, `Keccak.scratchWords` words of it first |

The decoded proof (`Decoded`) is written by the wire decoder and read by the rest:

* an `E` element is two words, limb `0` then limb `1`; a `K` element one word; a digest four;
* the stream: its count `n` at word `0`, its elements from word `1` (`2 n` words);
* the openings, from word `streamEnd = 1 + 2 · maxStream`: the phase count `p ≤ wireMaxPhases` at
  word `streamEnd`, then for each phase `k < p`, at `phaseBase k`, its query count `q ≤
  wireMaxQueries`, height `h ≤ wireMaxHeight` and leaf width `w ≤ wireMaxLeafWords` in three
  words, then its openings, opening `j` at `phaseBase k + 3 + j · openingWords`: the leaf index,
  the leaf's `w` words (of the `wireMaxLeafWords` reserved), then the path's `h` digests (of the
  `wireMaxHeight` reserved).
-/

@[expose] public section

namespace NativeVm

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- The most stream elements a proof of `L` bytes can carry: each takes 16 bytes on the wire. -/
def maxStream (L : Nat) : Nat := L / 16

/-- The words of one opening: its leaf index, `wireMaxLeafWords` leaf words, `wireMaxHeight`
digests of four words. -/
def openingWords : Nat := 1 + wireMaxLeafWords + 4 * wireMaxHeight

/-- The words of one phase: its three counts, then `wireMaxQueries` openings. -/
def phaseWords : Nat := 3 + wireMaxQueries * openingWords

/-- Where the openings start, after the stream. -/
def streamEnd (L : Nat) : Nat := 1 + 2 * maxStream L

/-- Where phase `k` starts. -/
def phaseBase (L k : Nat) : Nat := streamEnd L + 1 + k * phaseWords

/-- The decoded area's words for a proof of `L` bytes. -/
def decodedWords (L : Nat) : Nat := phaseBase L wireMaxPhases

/-- The two words of an `E` element, limb `0` first. -/
def eWords (x : E) : List UInt64 := [(x.limb 0).lane, (x.limb 1).lane]

/-- The memory `mem` holds the decoded proof `π` at `a`, for a proof of `L` bytes: word `i` of the
area at `a + 8 i`. -/
def Decoded (mem : UInt64 → Option UInt64) (a : UInt64) (L : Nat) (π : Proof) : Prop :=
  let w (i : Nat) := mem (a + (8 * i).toUInt64)
  π.stream.length ≤ maxStream L ∧ w 0 = some π.stream.length.toUInt64 ∧
  (∀ i (h : i < π.stream.length), ∀ l < 2,
    w (1 + 2 * i + l) = some ((eWords π.stream[i]).getD l 0)) ∧
  π.openings.length ≤ wireMaxPhases ∧ w (streamEnd L) = some π.openings.length.toUInt64 ∧
  ∀ k (hk : k < π.openings.length),
    let phase := π.openings[k]
    let base := phaseBase L k
    ∃ h width, h ≤ wireMaxHeight ∧ width ≤ wireMaxLeafWords ∧ phase.length ≤ wireMaxQueries ∧
      w base = some phase.length.toUInt64 ∧ w (base + 1) = some h.toUInt64 ∧
      w (base + 2) = some width.toUInt64 ∧
      ∀ j (hj : j < phase.length),
        let o := phase[j]
        let ob := base + 3 + j * openingWords
        o.leaf.length = width ∧ o.path.length = h ∧ o.leafIndex < 2 ^ 32 ∧
        w ob = some o.leafIndex.toUInt64 ∧
        (∀ t (ht : t < width), w (ob + 1 + t) = some (o.leaf.getD t 0).lane) ∧
        (∀ d (hd : d < h), ∀ l < 4,
          w (ob + 1 + wireMaxLeafWords + 4 * d + l) = some ((o.path.getD d default).toList.getD l 0))

end NativeVm
