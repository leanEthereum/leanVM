module

public import NativeVm.Math.Keccak.Facts

/-!
# `linear_transpose`'s loops compute `keccakLinearTranspose`

The Rust (`keccak_gkr.rs`) fills `g` lane by lane (`gW`), sums its columns into `columns` (`colW`,
in the loop's order), then each output element from `g` and two columns. Entry by entry, that is
`keccakLinearTranspose` (`linearTranspose_getD`).
-/

namespace NativeRustcVm.KeccakGkr

open NativeVm.Model LeanVM.Parameters NativeVm.Math.Keccak
open LeanVM.Protocol.Verifier (keccakBits)

@[expose] public section

/-- `g[64 lane + z]`: position `z` of lane `lane` after ρ and π. -/
def gW (ws : Array EW) (lane z : Nat) : EW :=
  ws.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0

/-- `columns[64 x + z]`: the column's five lanes summed in order. -/
def colW (ws : Array EW) (x z : Nat) : EW :=
  gW ws x z + gW ws (x + 5) z + gW ws (x + 10) z + gW ws (x + 15) z + gW ws (x + 20) z

/-- `out[64 lane + z]`. -/
def outW (ws : Array EW) (lane z : Nat) : EW :=
  gW ws lane z + colW ws ((lane % 5 + 1) % 5) z + colW ws ((lane % 5 + 4) % 5) ((z + 1) % 64)

end

public section

theorem zero_add_ew (x : EW) : (0 : EW) + x = x := by
  obtain ⟨a, b⟩ := x
  show EW.mk ((0 : UInt64) ^^^ a) ((0 : UInt64) ^^^ b) = _
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;> simp

theorem sumE_five (f : Nat → EW) :
    sumE ((Array.range 5).map f) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [sumE, ← Array.foldl_toList, Array.toList_map, Array.toList_range,
    show List.range 5 = [0, 1, 2, 3, 4] from rfl]
  simp [zero_add_ew]

theorem linearTranspose_size' (w : Array EW) : (keccakLinearTranspose w).size = 1600 :=
  linearTranspose_size w

/-- **`keccakLinearTranspose` entry by entry**. -/
theorem linearTranspose_getD' (w : Array EW) {lane z : Nat} (hl : lane < 25) (hz : z < 64) :
    (keccakLinearTranspose w).getD (64 * lane + z) 0 = outW w lane z := by
  rw [keccakLinearTranspose]
  generalize hg : (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0) = g
  have hgv : ∀ l < 25, ∀ x < 64, g.getD (64 * l + x) 0 = gW w l x := fun l hl x hx ↦ by
    obtain ⟨-, hv⟩ := setLanes (fun lane z ↦
      w.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0) 25
      (Array.replicate keccakBits 0)
    have h1 : (64 * l + x) / 64 = l := by omega
    have h2 : (64 * l + x) % 64 = x := by omega
    have hin : 64 * l + x < 64 * 25 ∧ 64 * l + x < (Array.replicate keccakBits (0 : EW)).size := by
      rw [Array.size_replicate, show keccakBits = 1600 from rfl]; omega
    rw [← hg, Array.getD_eq_getD_getElem?, hv]
    simp only [hin, and_self, ↓reduceIte, Option.getD_some]
    rw [h1, h2, gW]
  have hcv : ∀ c < 5, ∀ x < 64,
      ((Array.range 5).flatMap fun c ↦ (Array.range 64).map fun x ↦
        sumE ((Array.range 5).map fun y ↦ g.getD (64 * (c + 5 * y) + x) 0)).getD (64 * c + x)
          0 = colW w c x := fun c hc x hx ↦ by
    rw [flatMap_range_getD 5 64 _ _ hc hx, sumE_five, colW]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    rw [hgv _ (by omega) x hx, hgv _ (by omega) x hx, hgv _ (by omega) x hx,
      hgv _ (by omega) x hx, hgv _ (by omega) x hx]
  rw [flatMap_range_getD 25 64 _ _ hl hz, hgv lane hl z hz, hcv _ (by omega) z hz,
    hcv _ (by omega) _ (Nat.mod_lt _ (by decide)), outW]

end

end NativeRustcVm.KeccakGkr
