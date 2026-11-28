module

public import NativeRustcVm.Mem
public import NativeVm.Input
public import NativeVm.Model.Transcript

/-!
# The transcript's state in memory

The crate's `TState` (`rustc/vm/src/transcript.rs`, `#[repr(C)]`, 760 bytes) represents the
model's `NativeVm.Model.TState` (`TStateAt`):

| offset | field | holds |
|---|---|---|
| `0` | `sponge.state` | the 25 lanes |
| `200 + 24 i` | `sponge.pending[i]` | scalar `i < n_pending` waiting: its `EW`, its tag word |
| `296` | `sponge.n_pending` | the waiting scalars' count, at most `rateScalars` |
| `304`, `312` | `sponge.ground` | `Option<EW>`: tag word `0` or `1` (`Some`), the `EW` |
| `328` to `351` | `dec` | `Decoded { words: &[u64], l }`: the area's address, words, `L` |
| `352` | `cursor` | the stream's cursor |
| `360` | `phase` | the openings' cursor |
| `368 + 48 i` | `roots[i]` | root `i`: its digest's four words, height, width, for `i < n_roots` |
| `752` | `n_roots` | the roots' count, at most `8` |

The decoded area (`DecArea`: address, word count, wire length) holds the model's stream and
openings in the layout of `NativeVm.Decoded` (`DecodedAt`): the stream's count at word `0`,
element `i` at words `1 + 2 i`, `2 + 2 i`; the phase count at word `streamEnd L`, phase `k` at
`phaseBase L k` (`PhaseAt`). The transcript's functions write the `TState`'s bytes and read the
decoded area's; the two are apart (`TStateAt.footprint`).
-/

namespace NativeRustcVm.Transcript

open NativeVm NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Compile

@[expose] public section

/-- The address `off` bytes past `a`. -/
abbrev off (a : BitVec 64) (n : Nat) : BitVec 64 := a + BitVec.ofNat 64 n

/-! ## The sponge -/

/-- Waiting scalar `x` with its tag at `a` (`Pending`, 24 bytes). -/
def PendingAt (d : Mem 64) (a : BitVec 64) (p : EW × UInt64) : Prop :=
  EWAt d a p.1 ∧ WordAt d (off a 16) p.2

/-- The `Option<EW>` at `a` (24 bytes: the ground challenge, `stream_element`'s and
`next_scalar`'s results): tag word `0`, or tag word `1` and the element. -/
def OptEWAt (d : Mem 64) (a : BitVec 64) : Option EW → Prop
  | none => WordAt d a 0
  | some c => WordAt d a 1 ∧ EWAt d (off a 8) c

/-- The sponge at `p` (`SpongeW`, 328 bytes) represents `sp`: the lanes, the first `n_pending`
slots the waiting scalars, at most `rateScalars` of them, and the ground challenge. -/
structure SpongeAt (d : Mem 64) (p : BitVec 64) (sp : SpongeW) : Prop where
  state : WordsAt d p sp.state.toList
  pending_le : sp.pending.size ≤ rateScalars
  n_pending : WordAt d (off p 296) sp.pending.size.toUInt64
  pending : ∀ i (h : i < sp.pending.size), PendingAt d (off p (200 + 24 * i)) sp.pending[i]
  ground : OptEWAt d (off p 304) sp.ground

/-- The sponge's bytes. -/
def spongeBytes : Nat := 328

/-! ## The decoded area -/

/-- The decoded area: its address, its word count (`words.len()`), and the wire's byte count `L`
(`Decoded.l`). -/
structure DecArea where
  words : BitVec 64
  len : Nat
  l : Nat

/-- The decoded area's bytes. -/
def DecArea.region (a : DecArea) : Region := ⟨a.words, 8 * a.len⟩

/-- Word `i` of the decoded area. -/
abbrev DecArea.word (a : DecArea) (i : Nat) : BitVec 64 := off a.words (8 * i)

/-- The `Decoded` struct at `p` (24 bytes) names the area: `words`'s address and length, `l`. -/
def DecFieldsAt (d : Mem 64) (p : BitVec 64) (a : DecArea) : Prop :=
  WordAt d p (UInt64.ofBitVec a.words) ∧ WordAt d (off p 8) a.len.toUInt64 ∧
    WordAt d (off p 16) a.l.toUInt64

/-- Opening `o` at `b` (`openingWords` words), its leaf `width` words and its path `h` digests:
the leaf index (below `2 ^ 32`), the leaf's words from word `1`, the path's digests from word
`1 + wireMaxLeafWords`. -/
def OpeningAt (d : Mem 64) (b : BitVec 64) (h width : Nat) (o : OpeningW) : Prop :=
  o.leaf.size = width ∧ o.path.size = h ∧ o.leafIndex.toNat < 2 ^ 32 ∧
    WordAt d b o.leafIndex ∧ WordsAt d (off b 8) o.leaf.toList ∧
    WordsAt d (off b (8 * (1 + wireMaxLeafWords))) (o.path.toList.flatMap (·.toList))

/-- Phase `ph` at `b` (`phaseWords` words): its query count, height `h` and leaf width `width`,
then opening `j` at word `3 + j · openingWords`. -/
def PhaseAt (d : Mem 64) (b : BitVec 64) (ph : Array OpeningW) : Prop :=
  ∃ h width, h ≤ wireMaxHeight ∧ width ≤ wireMaxLeafWords ∧ ph.size ≤ wireMaxQueries ∧
    WordAt d b ph.size.toUInt64 ∧ WordAt d (off b 8) h.toUInt64 ∧
    WordAt d (off b 16) width.toUInt64 ∧
    ∀ j (hj : j < ph.size), OpeningAt d (off b (8 * (3 + j * openingWords))) h width ph[j]

/-- **The decoded area** `a` holds the stream and the openings (`NativeVm.Decoded`'s layout): at
least `decodedWords L` words, the stream's count and elements, the phase count and phases. -/
structure DecodedAt (d : Mem 64) (a : DecArea) (stream : Array EW)
    (openings : Array (Array OpeningW)) : Prop where
  l_lt : a.l < 2 ^ 64
  len : decodedWords a.l ≤ a.len
  stream_le : stream.size ≤ maxStream a.l
  stream_count : WordAt d (a.word 0) stream.size.toUInt64
  stream : ∀ i (h : i < stream.size), EWAt d (a.word (1 + 2 * i)) stream[i]
  phases_le : openings.size ≤ wireMaxPhases
  phase_count : WordAt d (a.word (streamEnd a.l)) openings.size.toUInt64
  phases : ∀ k (h : k < openings.size), PhaseAt d (a.word (phaseBase a.l k)) openings[k]

/-! ## The transcript's state -/

/-- The most roots (`MAX_ROOTS`). -/
def maxRoots : Nat := 8

/-- The `TState`'s bytes. -/
def tstateBytes : Nat := 760

/-- Root `r` at `b` (`RootW`, 48 bytes): its digest's four words, its height and width. -/
def RootAt (d : Mem 64) (b : BitVec 64) (r : RootW) : Prop :=
  r.height < 2 ^ 64 ∧ r.width < 2 ^ 64 ∧ WordsAt d b r.digest.toList ∧
    WordAt d (off b 32) r.height.toUInt64 ∧ WordAt d (off b 40) r.width.toUInt64

/-- The `TState`'s bytes and the decoded area: data memory, not wrapping, apart. -/
def Footprint (d : Mem 64) (t : BitVec 64) (a : DecArea) : Prop :=
  Region.Ok d ⟨t, tstateBytes⟩ ∧ Region.Ok d a.region ∧ Apart t tstateBytes a.words (8 * a.len)

/-- **The transcript's state** at `t`, reading the decoded area `a`, represents `s`. -/
structure TStateAt (d : Mem 64) (t : BitVec 64) (a : DecArea) (s : TState) : Prop where
  footprint : Footprint d t a
  sponge : SpongeAt d t s.sponge
  dec : DecFieldsAt d (off t 328) a
  decoded : DecodedAt d a s.stream s.openings
  cursor_le : s.cursor ≤ s.stream.size
  cursor : WordAt d (off t 352) s.cursor.toUInt64
  phase_le : s.phase ≤ s.openings.size
  phase : WordAt d (off t 360) s.phase.toUInt64
  roots_le : s.roots.size ≤ maxRoots
  n_roots : WordAt d (off t 752) s.roots.size.toUInt64
  roots : ∀ i (h : i < s.roots.size), RootAt d (off t (368 + 48 * i)) s.roots[i]

end

end NativeRustcVm.Transcript
