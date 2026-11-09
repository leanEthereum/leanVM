/-
  LeanVM.Guest.B1.KeccakGkr.VkCG

  `verify_keccak`'s honest layout: its buffers' words, the claim records pointing into the layers'
  buffers, where each layer reads.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCF
public import LeanVM.Guest.B1.KeccakGkr.VkCChain
public import LeanVM.Guest.B1.KeccakGkr.LayerCPlaced
public import LeanVM.Guest.B1.KeccakGkr.FlatG

/-!
# The honest layout

* `eqLevels rs n`: an equality tree's levels, `eqKernel` of the first `t` coordinates for
  `t = 1 … n`, as `eqtree` stores them (`eqLevels_getD`).
* For a `VkData` `D`, from the buffers' base `B` and the layers' buffers' bases `ls`: `D.sizes` and
  `D.own B ls`, the seven buffers' sizes and words (the first claim's point, the lane
  coordinates, the claim records, the instance, lane and segment trees, the low tree);
  `D.CL B ls s`, where claim `s`'s record and buffers are (`ClaimLay`); `D.lcur s`, where layer
  `s` reads past the cursor.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public noncomputable section

/-- An equality tree's levels: `eqKernel` of the first `t` coordinates, `t = 1 … n`. -/
def eqLevels (rs : List E) (n : ℕ) : List E :=
  ((List.range n).map fun t ↦ eqKernel (rs.take (t + 1))).flatten

theorem eqLevels_succ (rs : List E) (n : ℕ) :
    eqLevels rs (n + 1) = eqLevels rs n ++ eqKernel (rs.take (n + 1)) := by
  simp [eqLevels, List.range_succ]

theorem eqLevels_length {rs : List E} : ∀ {n : ℕ}, n ≤ rs.length →
    (eqLevels rs n).length = 2 ^ (n + 1) - 2
  | 0, _ => rfl
  | n + 1, h => by
    rw [eqLevels_succ, List.length_append, eqLevels_length (by omega), eqKernel_length,
      List.length_take, Nat.min_eq_left h, pow_succ 2 (n + 1)]
    have : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **An equality tree's levels**: level `t` from `2^t - 2`. -/
theorem eqLevels_getD {rs : List E} : ∀ {n : ℕ}, n ≤ rs.length → ∀ t, 1 ≤ t → t ≤ n →
    ∀ i < 2 ^ t, (eqLevels rs n).getD (2 ^ t - 2 + i) 0 = (eqKernel (rs.take t)).getD i 0
  | 0, _, t, h1, h2, _, _ => by omega
  | n + 1, h, t, h1, h2, i, hi => by
    rw [eqLevels_succ]
    have hl := eqLevels_length (rs := rs) (n := n) (by omega)
    rcases Nat.lt_or_ge t (n + 1) with ht | ht
    · have hlt : 2 ^ t - 2 + i < (eqLevels rs n).length := by
        have h2 : 2 ≤ 2 ^ t := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) h1
        rw [hl]
        have : 2 ^ (t + 1) ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega
      rw [List.getD_append _ _ _ _ hlt]
      exact eqLevels_getD (by omega) t h1 (by omega) i hi
    · obtain rfl : t = n + 1 := by omega
      have h2 : 2 ≤ 2 ^ (n + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [List.getD_append_right _ _ _ _ (by omega), hl]
      congr 1
      omega

/-- `ptr b · g^j` is `ptr (b + j)`. -/
theorem ptr_mul_gen (b j : ℕ) : ptr b * gen ^ j = ptr (b + j) := by
  rw [gen_pow_eq_ofK, ← ofK_mul]
  unfold Parameters.addressOfIndex
  rw [← pow_add]

namespace VkData

variable (D : VkData)

/-- Layer `s`'s specialization. -/
def lname (_D : VkData) (s : ℕ) : String := layerName (firstOf s)

/-- Where layer `s` reads, past the cursor. -/
def lcur (s : ℕ) : ℕ := 1 + s * (47 + 2 * (D.τ - 3) + 36)

/-- The buffers' sizes. -/
def sizes : List ℕ := [D.τ - 3, 5, 286, 30, 62, 2, 30]

/-- The claim records' buffer, past the buffers' base. -/
def o201 : ℕ := D.τ + 2

/-- The lane coordinates' tree, past the buffers' base. -/
def o274 : ℕ := D.τ + 318

/-- Layer `s`'s next claim's record, pointing into its buffers at `ls s`. -/
def outWs (ls : ℕ → ℕ) (s : ℕ) : List E :=
  (D.layer s).outW (firstOf s) (ptr (ls s)) (ptr (ls s + (D.layer s).y + 139))
    (ptr (ls s + (D.layer s).y + 128)) (ptr (ls s + (D.layer s).y + 164))

/-- The first claim's record. -/
def cw0 (B : ℕ) : List E :=
  [D.c0.value, 1, ptr B, ptr (B + D.o274 + 30), 0, 0] ++ D.c0.mu

/-- The claim records. -/
def claims (B : ℕ) (ls : ℕ → ℕ) : List E := D.cw0 B ++ (List.range 12).flatMap (D.outWs ls)

/-- **Where claim `s`'s record and buffers are.** -/
def CL (B : ℕ) (ls : ℕ → ℕ) : ℕ → ClaimLay
  | 0 => ⟨B + D.o201 + 22 * 0, D.cw0 B, B, B + D.o274 + 30, (eqKernel D.rl).take 25, 0, [], 0⟩
  | k + 1 => ⟨B + D.o201 + 22 * (k + 1), D.outWs ls k, ls k, ls k + (D.layer k).y + 139,
      lanesOut ((D.layer k).locPt (firstOf k)) ((D.layer k).beta (firstOf k)).1,
      ls k + (D.layer k).y + 128, (D.layer k).locPt (firstOf k), ls k + (D.layer k).y + 164⟩

/-- **The buffers' words.** -/
def own (B : ℕ) (ls : ℕ → ℕ) : List (List E) :=
  [D.c0.point, D.rl, D.claims B ls, eqLevels (D.chis.take 4) 4, eqLevels D.rl 5, eqKernel D.seg,
    eqLevels D.I.1 4]

theorem bases_eq (B : ℕ) (h : 3 ≤ D.τ) :
    bases B D.sizes = [B, B + (D.τ - 3), B + D.o201, B + D.τ + 288, B + D.o274, B + D.τ + 380,
      B + D.τ + 382] := by
  simp only [sizes, o201, o274, bases]
  simp only [List.cons.injEq, and_true, true_and]
  repeat' apply And.intro
  all_goals omega

end VkData

end
end LeanVM.Guest.B1.VerifySub
