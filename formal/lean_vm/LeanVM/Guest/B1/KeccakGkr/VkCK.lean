/-
  LeanVM.Guest.B1.KeccakGkr.VkCK

  `verify_keccak`'s honest oracle: the bits of `y`, the buffers' bases, the callees' returns; and
  the buffers' words in memory.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCJ
public import LeanVM.Guest.B1.KeccakGkr.FlatGI

/-!
# The oracle

`D.w B curE`: the values `Fwd.ev` takes from its oracle, honestly: the bits of `y = τ - 3`, the
seven buffers' bases from `B`, the layers' and the openings' rounds' returns (the cursors from
`curE`). `own_mem`: a memory holding the buffers holds each of them.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public noncomputable section

/-- Where step `s` ends. -/
def stepE (s : ℕ) : ℕ :=
  [531, 566, 600, 643, 684, 727, 760, 801, 839, 882, 923, 963].getD s 0

theorem stepE_eq : ∀ s < 12, stepT0 s (stepB s) + stepTailSz s = stepE s := by decide +kernel

namespace VkData

variable (D : VkData)

/-- **The oracle.** -/
def w (B curE : ℕ) (i : ℕ) : E :=
  if 20 ≤ i ∧ i < 25 then Value.bitE ((D.τ - 3).testBit (i - 20))
  else if i = 60 then ptr B
  else if i = 92 then ptr (B + (D.τ - 3))
  else if i = 203 then ptr (B + D.o201)
  else if i = 205 then ptr (B + D.τ + 288)
  else if i = 276 then ptr (B + D.o274)
  else if i = 384 then ptr (B + D.τ + 380)
  else if i = 1259 then ptr (B + D.τ + 382)
  else if 966 ≤ i ∧ i < 973 then (D.oRets curE).getD (i - 966) 0
  else if 1252 ≤ i ∧ i < 1259 then (D.iRets curE).getD (i - 1252) 0
  else if 1382 ≤ i ∧ i < 1389 then (D.sRets curE).getD (i - 1382) 0
  else match (List.range 12).find? (fun s ↦ stepE s - 6 ≤ i && i < stepE s) with
    | some s => ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD (i - (stepE s - 6)) 0
    | none => 0

variable {D} {B curE : ℕ}

theorem w_bits {j : ℕ} (hj : j < 5) : D.w B curE (20 + j) = Value.bitE ((D.τ - 3).testBit j) := by
  simp only [w, Nat.le_add_right, true_and, show 20 + j < 25 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]


theorem w_o {j : ℕ} (hj : j < 7) : D.w B curE (966 + j) = (D.oRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_i {j : ℕ} (hj : j < 7) : D.w B curE (1252 + j) = (D.iRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_s {j : ℕ} (hj : j < 7) : D.w B curE (1382 + j) = (D.sRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_layer {s : ℕ} (hs : s < 12) {j : ℕ} (hj : j < 6) :
    D.w B curE (stepE s - 6 + j) =
      ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD j 0 := by
  interval_cases s <;> interval_cases j <;> rfl

theorem bufL_eq (h3 : 3 ≤ D.τ) (B : ℕ) (ls : ℕ → ℕ) :
    bufL B D.sizes (D.own B ls) =
      [(B, D.c0.point), (B + (D.τ - 3), D.rl), (B + D.o201, D.claims B ls),
        (B + D.τ + 288, eqLevels (D.chis.take 4) 4), (B + D.o274, eqLevels D.rl 5),
        (B + D.τ + 380, eqKernel D.seg), (B + D.τ + 382, eqLevels D.I.1 4)] := by
  rw [bufL, bases_eq D B h3, own]
  simp

/-- **The buffers, each in memory.** -/
theorem own_mem (h3 : 3 ≤ D.τ) {rd : Reader} {B : ℕ} {ls : ℕ → ℕ}
    (hm : MemL rd (bufL B D.sizes (D.own B ls))) :
    ReadsAt rd (ptr B) D.c0.point ∧ ReadsAt rd (ptr (B + (D.τ - 3))) D.rl ∧
      ReadsAt rd (ptr (B + D.o201)) (D.claims B ls) ∧
      ReadsAt rd (ptr (B + D.τ + 288)) (eqLevels (D.chis.take 4) 4) ∧
      ReadsAt rd (ptr (B + D.o274)) (eqLevels D.rl 5) ∧
      ReadsAt rd (ptr (B + D.τ + 380)) (eqKernel D.seg) ∧
      ReadsAt rd (ptr (B + D.τ + 382)) (eqLevels D.I.1 4) := by
  rw [bufL_eq h3] at hm
  exact ⟨memL_entry hm (by simp), memL_entry hm (by simp), memL_entry hm (by simp),
    memL_entry hm (by simp), memL_entry hm (by simp), memL_entry hm (by simp),
    memL_entry hm (by simp)⟩

end VkData

end
end LeanVM.Guest.B1.VerifySub
