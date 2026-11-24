/-
  LeanVM.Guest.B1.Sig.Merkle

  A 64-byte `keccak` of four cells is their hash, and a Merkle path's forward fold is the schemes'
  fold.
-/

module

public import LeanVM.Guest.B1.Sig.WotsSound
public import LeanVM.Guest.B1.Sig.XmssScheme

/-!
# Merkle paths, sound

* `k64_sound`: `keccak([m0, m1], [m2, m3], out)` writes `hcell` of the four cells into `out`;
* `mFold`: a path's levels from a node, forward, level `l` hashing `P`, the level's address and
  the pair in the order of its bit (`bit = 0`: the node then its sibling); `mFold_eq_xFold`: it is
  the schemes' `xFold`;
* `IsBit`, `isBit_cases`: a bit pinned Boolean is `0` or `1`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A 64-byte `keccak` of four cells** writes their hash. -/
theorem k64_sound {pad : Nat} (hp : PadOK σ pad) {m0 m1 m2 m3 : V} {c o : Nat}
    (h : AtomsHold rd σ (k64 pad m0 m1 m2 m3 c o)) :
    σ (.n o) = (hcell [σ m0, σ m1, σ m2, σ m3]).1 := by
  rw [k64_eq] at h
  have := kMsg_sound (cells := [.cell m0, .cell m1, .cell m2, .cell m3]) (len := 64) (tailRun := false)
    (out := some o) hp (fun h => by simp at h) h (by simp) (fun j hj => by
      simp only [List.map, KC.val, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl)
  have ho : (kMsg pad [.cell m0, .cell m1, .cell m2, .cell m3] 64 false (some o) c).2.2 = o := rfl
  rw [ho] at this
  rw [this]
  simp only [hcell, List.map, KC.val, cellsBytes_eq_flatMap]
  congr 2

/-! ## Merkle paths -/

/-- The levels `l ..< l + m` of a path from `x`, forward: level `l` hashes `P`, its address `A l`
and the pair in the order of bit `l`. -/
def mFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → Nat → E → E
  | 0, _, x => x
  | m + 1, l, x => mFold pp A bits sibs m (l + 1)
      (hcell [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l]).1

theorem mFold_succ (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), mFold pp A bits sibs (m + 1) l x =
      (hcell [pp, A (l + m), if bits (l + m) then sibs (l + m) else mFold pp A bits sibs m l x,
        if bits (l + m) then mFold pp A bits sibs m l x else sibs (l + m)]).1
  | 0, l, x => by simp [mFold]
  | m + 1, l, x => by
      rw [mFold, mFold_succ pp A bits sibs m (l + 1), show l + 1 + m = l + (m + 1) by omega]
      rfl

/-- **The forward fold is the schemes' fold.** -/
theorem mFold_eq_xFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m : Nat) (x : E), mFold pp A bits sibs m 0 x = xFold pp A bits sibs m x
  | 0, x => rfl
  | m + 1, x => by
      rw [mFold_succ, mFold_eq_xFold pp A bits sibs m x, Nat.zero_add]
      rfl

/-- A bit pinned Boolean. -/
def IsBit (x : E) : Prop := x * x = x

theorem isBit_cases {x : E} (h : IsBit x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

end
end LeanVM.Guest.B1.Sig
