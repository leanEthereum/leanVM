/-
  LeanVM.Guest.B1.Sig.SphincsGlue

  The message digest's fields as the hints `verify_sig_lean_sphincs` takes: the codeword bytes
  of the first cell, the index, children and unused bits of the second, and the bound they add
  up to; where the coordinates leave their outputs.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigest
public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.B1.Sig.SphincsCoordComplete

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Digits -/

theorem sBaseW_expand (w : Nat) : ∀ n x, x < 2 ^ (w * n) →
    ∑ k ∈ Finset.range n, x / 2 ^ (w * k) % 2 ^ w * 2 ^ (w * k) = x
  | 0, x, h => by simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at h; simp [h]
  | n + 1, x, h => by
      rw [Finset.sum_range_succ']
      have ih := sBaseW_expand w n (x / 2 ^ w) (by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show w * n + w = w * (n + 1) by ring]
        exact h)
      have hs : ∑ k ∈ Finset.range n, x / 2 ^ (w * (k + 1)) % 2 ^ w * 2 ^ (w * (k + 1)) =
          2 ^ w * ∑ k ∈ Finset.range n, x / 2 ^ w / 2 ^ (w * k) % 2 ^ w * 2 ^ (w * k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show w * (k + 1) = w + w * k by ring, pow_add, ← Nat.div_div_eq_div_mul]
        ring
      rw [hs, ih]
      simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.mul_one]
      exact Nat.div_add_mod x (2 ^ w)

/-- The second cell is the sum of its fields. -/
theorem digestHi_expand (x : Nat) :
    digestHi (x % 2 ^ 26) (x / 2 ^ 106) (fun c => x / 2 ^ (26 + 4 * c) % 2 ^ 4)
      (fun k => x / 2 ^ (58 + 3 * k) % 2 ^ 3) = x := by
  have hS : ∑ c ∈ Finset.range 8, x / 2 ^ (26 + 4 * c) % 2 ^ 4 * 2 ^ (4 * c) = x / 2 ^ 26 % 2 ^ 32 := by
    conv_rhs => rw [← sBaseW_expand 4 8 (x / 2 ^ 26 % 2 ^ 32) (Nat.mod_lt _ (by positivity))]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    rw [mod_div_mod (by omega), pow_add, ← Nat.div_div_eq_div_mul]
  have hA : ∑ k ∈ Finset.range 16, x / 2 ^ (58 + 3 * k) % 2 ^ 3 * 2 ^ (3 * k) = x / 2 ^ 58 % 2 ^ 48 := by
    conv_rhs => rw [← sBaseW_expand 3 16 (x / 2 ^ 58 % 2 ^ 48) (Nat.mod_lt _ (by positivity))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [mod_div_mod (by omega), pow_add, ← Nat.div_div_eq_div_mul]
  have e1 := Nat.mod_add_div x (2 ^ 26)
  have e2 := Nat.mod_add_div (x / 2 ^ 26) (2 ^ 32)
  have e3 := Nat.mod_add_div (x / 2 ^ 58) (2 ^ 48)
  have d1 : x / 2 ^ 26 / 2 ^ 32 = x / 2 ^ 58 := by rw [Nat.div_div_eq_div_mul, ← pow_add]
  have d2 : x / 2 ^ 58 / 2 ^ 48 = x / 2 ^ 106 := by rw [Nat.div_div_eq_div_mul, ← pow_add]
  rw [d1] at e2
  rw [d2] at e3
  unfold digestHi
  rw [hS, hA]
  omega

theorem lit_cellNat_of {x : E} (h : IsCanonical128 x) : lit (cellNat x) = x := by
  rw [← toNat_cellVal]
  exact (lit_toNat (cellVal x)).trans (cellOf_cellVal h)

/-! ## The message digest's fields -/

/-- The marks of the digest of cells `x0`, `x1`, numbered. -/
def dMarks (x0 x1 : Nat) (r : Nat) : Sphincs.CoordMark :=
  Sphincs.Concrete.digestMarks (BitVec.ofNat Sphincs.messageDigestBits (x0 + 2 ^ 128 * x1))
    ⟨r % 8, Nat.mod_lt _ (by norm_num)⟩

theorem dMarks_super {x0 x1 : Nat} (h0 : x0 < 2 ^ 128) {c : Nat} (hc : c < 8) :
    (dMarks x0 x1 c).super.val = x1 / 2 ^ (26 + 4 * c) % 2 ^ 4 := by
  rw [dMarks, digestMarks_super_val, show Sphincs.Concrete.superOffset ⟨c % 8, Nat.mod_lt _ (by norm_num)⟩ =
      128 + (26 + 4 * c) by simp [Sphincs.Concrete.superOffset, Nat.mod_eq_of_lt hc]; ring,
    digestField_ofNat h0 (by simp only [Sphincs.topHeight]; omega)]
  rfl

theorem dMarks_child {x0 x1 : Nat} (h0 : x0 < 2 ^ 128) {k : Nat} (hk : k < 16) :
    ((dMarks x0 x1 (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val = x1 / 2 ^ (58 + 3 * k) % 2 ^ 3 := by
  rw [dMarks, digestMarks_child_val, show Sphincs.Concrete.childOffset ⟨k / 2 % 8, Nat.mod_lt _ (by norm_num)⟩
      ⟨k % 2, Nat.mod_lt _ (by omega)⟩ = 128 + (58 + 3 * k) by
      simp [Sphincs.Concrete.childOffset, Nat.mod_eq_of_lt (show k / 2 < 8 by omega)]; omega,
    digestField_ofNat h0 (by simp only [Sphincs.subHeight]; omega)]
  rfl

theorem dMarks_word {x0 x1 : Nat} {k : Nat} (hk : k < 16) :
    ((dMarks x0 x1 (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val = x0 / 2 ^ (8 * k) % 2 ^ 8 := by
  rw [dMarks, digestMarks_word_val, show Sphincs.Concrete.wordOffset ⟨k / 2 % 8, Nat.mod_lt _ (by norm_num)⟩
      ⟨k % 2, Nat.mod_lt _ (by omega)⟩ = 8 * k by
      simp [Sphincs.Concrete.wordOffset, Nat.mod_eq_of_lt (show k / 2 < 8 by omega)]; omega,
    digestByte_ofNat (by omega)]

/-- The marks are the digest's. -/
theorem dMarks_eq (x0 x1 : Nat) : (fun c : Sphincs.Coord => dMarks x0 x1 c.val) =
    Sphincs.Concrete.digestMarks (BitVec.ofNat Sphincs.messageDigestBits (x0 + 2 ^ 128 * x1)) := by
  funext c
  exact congrArg _ (Fin.ext (Nat.mod_eq_of_lt c.isLt))

/-- **The bound is the second cell**. -/
theorem dMarks_bound {x0 : Nat} (x1 : Nat) (h0 : x0 < 2 ^ 128) :
    eOfNat (x1 % 2 ^ 26) + lit (x1 / 2 ^ 106 * 2 ^ 106) + ∑ r ∈ Finset.range 8, coordWeight r (dMarks x0 x1 r) =
      lit x1 := by
  have hs : ∀ c < 8, x1 / 2 ^ (26 + 4 * c) % 2 ^ 4 < 2 ^ 4 := fun c _ => Nat.mod_lt _ (by positivity)
  have ha : ∀ k < 16, x1 / 2 ^ (58 + 3 * k) % 2 ^ 3 < 2 ^ 3 := fun k _ => Nat.mod_lt _ (by positivity)
  have hN : x1 % 2 ^ 26 < 2 ^ 26 := Nat.mod_lt _ (by positivity)
  conv_rhs => rw [← digestHi_expand x1]
  rw [← lit_digestHi hN hs ha]
  refine congrArg (fun y => eOfNat (x1 % 2 ^ 26) + lit (x1 / 2 ^ 106 * 2 ^ 106) + y)
    (Finset.sum_congr rfl fun c hc => ?_)
  rw [Finset.mem_range] at hc
  have e0 := dMarks_child (x1 := x1) h0 (k := 2 * c) (by omega)
  have e1 := dMarks_child (x1 := x1) h0 (k := 2 * c + 1) (by omega)
  simp only [show 2 * c / 2 = c by omega, show (2 * c + 1) / 2 = c by omega, show 2 * c % 2 = 0 by omega,
    show (2 * c + 1) % 2 = 1 by omega] at e0 e1
  rw [coordWeight, dMarks_super h0 hc]
  exact congrArg₂ (fun u v => lit (u * 2 ^ (58 + 3 * (2 * c))) + lit (v * 2 ^ (58 + 3 * (2 * c + 1))) +
    lit (x1 / 2 ^ (26 + 4 * c) % 2 ^ 4 * 2 ^ (26 + 4 * c))) e0 e1

/-- **The codeword bytes are the first cell**. -/
theorem dMarks_lanes {x0 : Nat} (x1 : Nat) (h0 : x0 < 2 ^ 128) :
    lit (∑ k ∈ Finset.range 16, ((dMarks x0 x1 (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val * 2 ^ (8 * k)) =
      lit x0 := by
  conv_rhs => rw [← sBaseW_expand 8 16 x0 h0]
  exact congrArg lit (Finset.sum_congr rfl fun k hk => by rw [dMarks_word (List.mem_range.mp hk)])

/-! ## Where the coordinates leave their outputs -/

theorem sCoords_outs_lt : ∀ (m c : Nat) (bound : V) (b : Nat), NB b bound →
    NB (sCoords m c bound b).2.1 (sCoords m c bound b).2.2.2.2 ∧
    ∀ r < m, NB (sCoords m c bound b).2.1 ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).1 ∧
      NB (sCoords m c bound b).2.1 ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).2 ∧
      NB (sCoords m c bound b).2.1 ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1 ∧
      NB (sCoords m c bound b).2.1 ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2
  | 0, _, _, _, h => ⟨h, fun _ h => absurd h (by omega)⟩
  | m + 1, c, bound, b, _ => by
      simp only [sCoords]
      obtain ⟨b0, hb0, h1, h2, h3, h4⟩ := sCoord_outs c bound b
      have hge := sCoords_snd_ge m (c + 1) (sCoord c bound b).2.2.2.2 (sCoord c bound b).2.1
      obtain ⟨ihB, ih⟩ := sCoords_outs_lt m (c + 1) (sCoord c bound b).2.2.2.2 (sCoord c bound b).2.1
        ⟨b0 + 562, by omega, h4⟩
      refine ⟨ihB, fun r hr => ?_⟩
      rcases r with _ | r
      · simp only [List.getD_cons_zero, h2, h3]
        exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
      · simp only [List.getD_cons_succ]
        exact ih r (by omega)

/-- An address over the tree index `n142`. -/
theorem addr142_complete {σ : Val} {k : Nat} (hk : 143 ≤ k) (A : E) :
    Completes C rd k (k + 2) [cst k A, addS (.n (k + 1)) (.n 142) (.n k)] σ
      (fun σ' => σ' (.n (k + 1)) = σ (.n 142) + A ∧ AgreeBelow k σ σ') := by
  set σ' := upds σ [(k, A), (k + 1, σ (.n 142) + A)]
  have he : Ext k (k + 2) σ σ' := upds_ext σ _ (by simp)
  have hk' : ∀ j < k, σ' (.n j) = σ (.n j) := fun j hj => (he.agree j hj).symm
  have v0 : σ' (.n k) = A := by simp [σ', upds]
  have v1 : σ' (.n (k + 1)) = σ (.n 142) + A := by simp [σ', upds]
  refine ⟨σ', he, ⟨v1, he.agree⟩, fun next kret hn => ?_⟩
  simp only [cst, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
  rw [v0, v1, hk' 142 (by omega)]
  exact ⟨rfl, rfl, hn⟩

theorem addr142_below {k : Nat} (hk : 143 ≤ k) (A : E) :
    NumBelow (k + 2) (Stmt.valsList [cst k A, addS (.n (k + 1)) (.n 142) (.n k)]) := by
  simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
    List.nil_append]
  exact .cons ⟨k, by omega, rfl⟩ (.cons ⟨k + 1, by omega, rfl⟩ (.cons ⟨142, by omega, rfl⟩ (.cons ⟨k, by omega, rfl⟩
    (.nil _))))

end
end LeanVM.Guest.B1.Sig
