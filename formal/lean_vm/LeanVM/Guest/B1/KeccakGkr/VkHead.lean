/-
  LeanVM.Guest.B1.KeccakGkr.VkHead

  `verify_keccak`'s head (G:2934-2976): `pack_g`, `y`'s bits, `step_g`, `rem_g`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkT
public import LeanVM.Guest.B1.KeccakGkr.CopyLoop

/-!
# `y` in the exponent

With the table's height `τ` (`tau_g = g^τ`), `pack_g = g^(τ - 4)` and `y_g = g^(τ - 3)`; the
hinted bits of `y = τ - 3`, pinned boolean, give `step_g = g^(y / 8)` and `rem_g = g^(y % 8)`,
which `assert step_g⁸·rem_g = y_g` ties back to `y`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- `INV_GEN^4`, as the data writes it, is `g⁻⁴`. -/
theorem word_ginv4_mul : word 8070450532247928836 0 0 * gen ^ 4 = 1 := by
  rw [show gen ^ 4 = ofK (K.ofBits 16) by rw [← word_two_pow (a := 4) (by decide)]; exact word_eOfNat _,
    show word 8070450532247928836 0 0 = ofK (K.ofBits 8070450532247928836) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8070450532247928836 * K.ofBits 16 = 1 by decide +kernel, ofK_one]

theorem bool_of_mul_self {b : E} (h : b * b = b) : b = 0 ∨ b = 1 := by
  have h' : b * (b - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem word_3 : word 3 0 0 = gen ^ 2 ^ 0 + 1 := by
  rw [word_eOfNat, show (3 : ℕ) = 2 ^ 1 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one, ← word_eOfNat,
    word_two_pow (by decide)]; simp

theorem word_5 : word 5 0 0 = gen ^ 2 ^ 1 + 1 := by
  rw [word_eOfNat, show (5 : ℕ) = 2 ^ 2 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one, ← word_eOfNat,
    word_two_pow (by decide)]; norm_num

theorem word_17 : word 17 0 0 = gen ^ 2 ^ 2 + 1 := by
  rw [word_eOfNat, show (17 : ℕ) = 2 ^ 4 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one, ← word_eOfNat,
    word_two_pow (by decide)]; norm_num

/-- **`y` in the exponent** (G:2938-2951): `step_g = g^⌊y/8⌋` (value `33`) and
`rem_g = g^(y % 8)` (value `47`), `y = τ - 3`. -/
theorem vkBits_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (htg : σ (.n 6) = gen ^ τ)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ vkBitsT next kret) :
    σ (.n 17) = gen ^ (τ - 4) ∧ σ (.n 19) = gen ^ (τ - 3) ∧
      σ (.n 33) = gen ^ ((τ - 3) / krStep) ∧ σ (.n 47) = gen ^ ((τ - 3) % krStep) ∧ next := by
  simp only [vkBitsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e16, e17, e18, e19, -, b0, b1, b2, b3, b4, e25, e26, e27, e28, e29, e30, e31, e32, e33,
    e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51,
    e52, e53, heq, hn⟩ := h
  have h17 : σ (.n 17) = gen ^ (τ - 4) := by
    rw [e17, htg, e16, show τ = τ - 4 + 4 by omega, pow_add, mul_assoc, mul_comm (gen ^ 4),
      word_ginv4_mul, mul_one]
    congr 1
  have h19 : σ (.n 19) = gen ^ (τ - 3) := by
    rw [e19, h17, e18, word_gen, ← pow_succ]; congr 1; omega
  -- the step chain: bits 3 and 4
  set c : ℕ → E := fun k ↦ σ (.n (23 + k)) with hc
  have hcb : ∀ k < 2, c k * c k = c k := by
    intro k hk
    interval_cases k
    · exact b3.symm
    · exact b4.symm
  have h33 : σ (.n 33) = ∏ j ∈ Finset.range 2, (1 + c j * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, hc]
    rw [e33, e32, e31, e30, e29, e28, e27, e26, e25]
    simp only [word_one, Nat.reduceAdd, word_3, word_5]
  rw [prod_gen_pow_of_bool hcb] at h33
  set S := bitsVal (fun j ↦ decide (c j = 1)) 2 with hS
  have hSlt : S < 4 := bitsVal_lt _ 2
  -- the remainder chain: bits 0, 1, 2
  set r : ℕ → E := fun k ↦ σ (.n (20 + k)) with hr
  have hrb : ∀ k < 3, r k * r k = r k := by
    intro k hk
    interval_cases k
    · exact b0.symm
    · exact b1.symm
    · exact b2.symm
  have h47 : σ (.n 47) = ∏ j ∈ Finset.range 3, (1 + r j * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, hr]
    rw [e47, e46, e45, e44, e43, e42, e41, e40, e39, e38, e37, e36, e35, e34]
    simp only [word_one, Nat.reduceAdd, word_3, word_5, word_17]
  rw [prod_gen_pow_of_bool hrb] at h47
  set R := bitsVal (fun j ↦ decide (r j = 1)) 3 with hR
  have hRlt : R < 8 := bitsVal_lt _ 3
  -- the check
  have hchk : gen ^ (8 * S + R) = gen ^ (τ - 3) := by
    have := eq_of_add_eq_zero' heq
    rw [e51, e50, e49, e48, h33, h47, e53, e52, h17, word_gen, ← pow_succ] at this
    rw [show 8 * S + R = S + S + (S + S) + (S + S + (S + S)) + R by ring]
    simp only [pow_add]
    rw [this]
    congr 1; omega
  have hy := gen_pow_inj (by omega) (by omega) hchk
  refine ⟨h17, h19, ?_, ?_, hn⟩
  · rw [h33]; congr 1; simp only [krStep]; omega
  · rw [h47]; congr 1; simp only [krStep]; omega

/-! ## Copies, the point, the squeezes -/

theorem copyWordsT_holds {src dst : V} {sOff dOff b n : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (copyWordsT src dst sOff dOff b n) next kret) :
    (∀ i < n, LoadHolds rd (σ src) (sOff + i) (σ (.n (b + i))) ∧
      LoadHolds rd (σ dst) (dOff + i) (σ (.n (b + i)))) ∧ next := by
  rw [copyWordsT, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  refine ⟨fun i hi ↦ ?_, h.2⟩
  have := h.1 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  exact this

/-- A squeeze with nothing waiting. -/
theorem sqZeroT_holds {capb o : ℕ} {cap : List E} (hcap : (cap5 capb).map σ = cap)
    (hz : ∀ k < 4, σ (.n (68 + k)) = 0) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sqZeroT capb o) next kret) :
    σ (.n (o + 19)) = (⟨cap, []⟩ : Fs).squeeze.1 ∧
      (cap5 (o + 8)).map σ = (⟨cap, []⟩ : Fs).squeeze.2.cap ∧ next := by
  rw [sqZeroT, holdsList_append, holds_challengeT] at h
  simp only [keccakA, Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨hk, hch, hn⟩ := h
  have hin : ([V.n 68, .n 68, .n 68, .n 68, .n 68, .n 69, .n 70, .n 71] ++ cap5 capb).map σ =
      rateOf (⟨cap, []⟩ : Fs).pend ++ (⟨cap, []⟩ : Fs).cap := by
    rw [List.map_append, hcap, rateOf_nil]
    simp [hz 0 (by omega), hz 1 (by omega), hz 2 (by omega), hz 3 (by omega)]
  have := squeeze_atom (s := ⟨cap, []⟩) hk hin (b := o + 13) (by simpa using hch)
  simp only [Nat.add_assoc, Nat.reduceAdd] at this
  refine ⟨this.1, ?_, hn⟩
  rw [← this.2]
  simp [cap5, List.range_succ]

/-- **The six squeezes** (G:2963-2969): the segment coordinate, then the five lane coordinates. -/
theorem vkSqueezesT_holds {cap0 : List E} (hcap : (cap5 11).map σ = cap0)
    (hz : ∀ k < 4, σ (.n (68 + k)) = 0) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ vkSqueezesT next kret) :
    (⟨cap0, []⟩ : Fs).squeezeN 1 = ([σ (.n 91)], ⟨(cap5 80).map σ, []⟩) ∧
      (⟨(cap5 80).map σ, []⟩ : Fs).squeezeN 5 =
        ((List.range 5).map (fun i ↦ σ (.n (112 + 20 * i))), ⟨(cap5 181).map σ, []⟩) ∧
      LoadHolds rd (σ (.n 66)) 0 (σ (.n 91)) ∧
      (∀ i < 5, LoadHolds rd (σ (.n 92)) i (σ (.n (112 + 20 * i)))) ∧ next := by
  rw [vkSqueezesT, holdsList_append, holdsList_append, holdsList_range_flatten _ _
    (fun _ ↦ rfl)] at h
  obtain ⟨q0c, q0p, h⟩ := sqZeroT_holds hcap hz h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l89, -, hall, hn⟩ := h
  have step : ∀ i < 5, σ (.n (112 + 20 * i)) =
        (⟨(cap5 (if i = 0 then 80 else 81 + 20 * i)).map σ, []⟩ : Fs).squeeze.1 ∧
      (cap5 (101 + 20 * i)).map σ =
        (⟨(cap5 (if i = 0 then 80 else 81 + 20 * i)).map σ, []⟩ : Fs).squeeze.2.cap ∧
      LoadHolds rd (σ (.n 92)) i (σ (.n (112 + 20 * i))) := by
    intro i hi
    have hb := hall i hi
    rw [holdsList_append] at hb
    obtain ⟨q1, q2, hb⟩ := sqZeroT_holds rfl hz hb
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    refine ⟨by rw [show 112 + 20 * i = 93 + 20 * i + 19 by omega]; exact q1, ?_, hb⟩
    rw [← q2]; congr 2; omega
  refine ⟨?_, ?_, l89, fun i hi ↦ (step i hi).2.2, hn⟩
  · simp only [Fs.squeezeN]
    rw [← q0c]
    have : (⟨cap0, []⟩ : Fs).squeeze.2 = ⟨(cap5 80).map σ, []⟩ := by
      rw [show ((⟨cap0, []⟩ : Fs).squeeze.2) = ⟨(⟨cap0, []⟩ : Fs).squeeze.2.cap, []⟩ from rfl, ← q0p]
    rw [this]
  · have hs : ∀ i < 5, (⟨(cap5 (if i = 0 then 80 else 81 + 20 * i)).map σ, []⟩ : Fs).squeeze.2 =
        ⟨(cap5 (101 + 20 * i)).map σ, []⟩ := by
      intro i hi
      rw [show (⟨(cap5 (if i = 0 then 80 else 81 + 20 * i)).map σ, []⟩ : Fs).squeeze.2 =
        ⟨(⟨(cap5 (if i = 0 then 80 else 81 + 20 * i)).map σ, []⟩ : Fs).squeeze.2.cap, []⟩ from rfl,
        ← (step i hi).2.1]
    have s0 := step 0 (by omega); have s1 := step 1 (by omega); have s2 := step 2 (by omega)
    have s3 := step 3 (by omega); have s4 := step 4 (by omega)
    have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega)
    have h3 := hs 3 (by omega); have h4 := hs 4 (by omega)
    simp only [↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.one_ne_zero,
      OfNat.ofNat_ne_zero] at s0 s1 s2 s3 s4 h0 h1 h2 h3 h4
    simp only [Fs.squeezeN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, Nat.reduceAdd]
    rw [h0, h1, h2, h3, h4, ← s0.1, ← s1.1, ← s2.1, ← s3.1, ← s4.1]

/-- **`verify_keccak`'s head** (G:2934-2976). -/
theorem vkHeadT_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (htg : σ (.n 6) = gen ^ τ)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ vkHeadT next kret) :
    σ (.n 17) = gen ^ (τ - 4) ∧ σ (.n 19) = gen ^ (τ - 3) ∧
    σ (.n 33) = gen ^ ((τ - 3) / krStep) ∧ σ (.n 47) = gen ^ ((τ - 3) % krStep) ∧
    (∀ i < 4, LoadHolds rd (σ (.n 7)) i (σ (.n (54 + i))) ∧
      LoadHolds rd (σ (.n 9)) i (σ (.n (54 + i)))) ∧
    (1 + σ (.n 17) ≠ 0 → C "__loop10" [1, σ (.n 17), σ (.n 60), σ (.n 7) * gen ^ 4] []) ∧
    σ (.n 66) = σ (.n 60) * σ (.n 17) ∧
    (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeezeN 1 =
      ([σ (.n 91)], ⟨(cap5 80).map σ, []⟩) ∧
    (⟨(cap5 80).map σ, []⟩ : Fs).squeezeN 5 =
      ((List.range 5).map (fun i ↦ σ (.n (112 + 20 * i))), ⟨(cap5 181).map σ, []⟩) ∧
    LoadHolds rd (σ (.n 66)) 0 (σ (.n 91)) ∧
    (∀ i < 5, LoadHolds rd (σ (.n 92)) i (σ (.n (112 + 20 * i)))) ∧
    (LoadHolds rd (σ (.n 5)) 0 (σ (.n 193)) ∧ FsPackOk σ (.n 193) (193 + 1) dsObserve) ∧
    next := by
  rw [vkHeadT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_map_atoms] at h
  obtain ⟨hcp, h⟩ := h
  simp only [Atom.Holds] at hcp
  obtain ⟨h17, h19, h33, h47, h⟩ := vkBits_holds hτ1 hτ2 htg h
  obtain ⟨hcw, h⟩ := copyWordsT_holds h
  simp only [vkPointT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e56, e57, -, e59, e60, e61, e62, e63, -, hcall, e64, -, z68, z69, z70, z71, h⟩ := h
  have hz : ∀ k < 4, σ (.n (68 + k)) = 0 := by
    intro k hk
    interval_cases k
    · rw [z68, word_zero]
    · rw [z69, word_zero]
    · rw [z70, word_zero]
    · rw [z71, word_zero]
  have hcap : (cap5 11).map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    simp only [cap5, List.map_cons, List.map_nil]
    rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega), hcp 4 (by omega)]
  obtain ⟨q1, q5, l89, lr, h⟩ := vkSqueezesT_holds hcap hz h
  obtain ⟨⟨lv, pv⟩, hn⟩ := (holds_fsNextT _ _ _ _ _).1 h
  refine ⟨h17, h19, h33, h47, fun i hi ↦ ⟨by simpa using (hcw i hi).1, by simpa using (hcw i hi).2⟩,
    fun hne ↦ ?_, e64, q1, q5, l89, lr, ⟨lv, pv⟩, hn⟩
  have := hcall (by rw [e60, e59, word_one]; exact hne)
  simp only [List.map_cons, List.map_nil, e61, e63, e62, word_one, word_16] at this
  exact this

end
end LeanVM.Guest.B1.VerifySub
