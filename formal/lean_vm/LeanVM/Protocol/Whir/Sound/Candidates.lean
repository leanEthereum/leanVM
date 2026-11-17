/-
  LeanVM.Protocol.Whir.Sound.Candidates

  The level-0 word of a commitment, `K`-valuedness of close messages and polynomials, and stacks
  from lane messages: what the starting relation reads candidates off list members with.
-/

module

public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.ToArkLib.Whir.Interleaved

/-!
# The level-0 list and the candidates

The level-0 oracle of the deployed WHIR opening (`verify_whir` level `0`,
`crates/verifier/src/whir.rs` at leanVM `40f877dc`)
is the committed word read lane by lane: lane `u` of column `v` is `laneOf W u v`, word `63 − u`
of leaf `v` (the program's `row.reverse.map ofK`), `laneWord μ R W`.

* `isInK_of_agree`: a codeword of the `E`-code whose entries lie in `K` on at least `2^κ`
  coordinates has a `K`-valued message. The message's limb `1` encodes a `K`-codeword vanishing
  on those coordinates, hence vanishes.
* `exists_map_of_isInK`: a polynomial over `E` of degree at most `d` with values in `K` at more
  than `d` points of `K` is over `K`, so a level-0 list member at a threshold above its degree is
  (`LeanVM.Protocol.Whir.Sound.Start` reads a candidate off it).

The candidates are `LeanVM.Protocol.EndToEnd.Candidates`: the stack's block `u` (cells
`x + 2^(μ−6)·u`) is the message of lane `u`, `f(u, x) = q(x, u)` of Annex B "Optimizations".
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd

@[expose] public section

/-! ## The level-0 word and code -/

/-- The level-0 interleaved word of a committed word: lane `u` of column `v`. -/
def laneWord (μ R : ℕ) (W : Word) : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u v ↦ laneOf W u v

/-! ## `K`-valuedness -/

section Limbs

variable {κ R : ℕ}

/-- The limb `i` of a message, as a `K`-valued message. -/
def msgLimb (g : (Fin κ → Bool) → E) (i : Fin 2) : (Fin κ → Bool) → K := fun u ↦ (g u).limb i

/-- A message is the sum of its limbs in the basis `1, y`. -/
theorem msg_eq_limbs (g : (Fin κ → Bool) → E) :
    g = (fun u ↦ ofK (msgLimb g 0 u)) + y • (fun u ↦ ofK (msgLimb g 1 u)) := by
  funext u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, msgLimb]
  conv_lhs => rw [E.eq_sum_limbs (g u)]
  ring

/-- The encoding of a message, limb by limb: limb `i` of a codeword entry is the `K`-encoding of
limb `i` of the message. -/
theorem enc_eq_ofLimbs (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = E.ofLimbs (encK κ R (msgLimb g 0) v) (encK κ R (msgLimb g 1) v) := by
  conv_lhs => rw [msg_eq_limbs g]
  rw [map_add, map_smul, enc_ofK, enc_ofK, ofLimbs_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Limb `i` of a codeword entry is the `K`-encoding of limb `i` of the message. -/
theorem limb_enc (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) (i : Fin 2) :
    (enc κ R g v).limb i = encK κ R (msgLimb g i) v := by
  rw [enc_eq_ofLimbs, limb_ofLimbs]
  fin_cases i <;> rfl

/-- A `K`-message whose encoding vanishes on `2^κ` coordinates is zero. -/
theorem eq_zero_of_encK_vanish (h : κ + R ≤ 64) (a : (Fin κ → Bool) → K)
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card) (hv : ∀ v ∈ S, encK κ R a v = 0) :
    a = 0 := by
  have hmem : enc κ R (fun u ↦ ofK (a u)) ∈ ReedSolomon.code (domain κ R h) (2 ^ κ) := by
    rw [← range_enc h]; exact LinearMap.mem_range_self _ _
  have h0 : enc κ R (fun u ↦ ofK (a u)) = 0 :=
    eq_of_mem_code_of_agreeOn (domain κ R h) hmem (Submodule.zero_mem _) S hS fun v hvS ↦ by
      rw [enc_ofK]; simp [hv v hvS]
  have h1 : (fun u ↦ ofK (a u)) = 0 := enc_injective h (h0.trans (map_zero _).symm)
  funext u
  exact ofK_injective ((congrFun h1 u).trans (by simp))

/-- **`K`-valuedness.** If the encoding of a message lies in `K` on at least `2^κ` coordinates,
every entry of the message lies in `K`. -/
theorem isInK_of_agree (h : κ + R ≤ 64) (g : (Fin κ → Bool) → E)
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card) (hK : ∀ v ∈ S, IsInK (enc κ R g v)) :
    ∀ u, IsInK (g u) := by
  have h1 := eq_zero_of_encK_vanish h (msgLimb g 1) S hS fun v hv ↦ by
    rw [← limb_enc]; exact hK v hv
  exact fun u ↦ congrFun h1 u

end Limbs

/-! ## Stacks from lane messages -/

section Stack

variable {μ : ℕ}

/-- The stack whose block `u` is the `K`-message `a u`: cell `i` is `a (i / 2^κ) (i % 2^κ)`. -/
def stackOf (hμ : laneBits ≤ μ) (a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K) :
    Column μ :=
  ⟨Vector.ofFn fun i : Fin (2 ^ μ) ↦
    a ⟨i / 2 ^ (μ - laneBits), by
      have hi := i.isLt
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      rwa [Nat.add_sub_cancel' hμ]⟩
      ((bitsEquiv (μ - laneBits)).symm ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)⟩

/-- Block `u` of `stackOf a` is `a u`. -/
theorem blockOf_stackOf (hμ : laneBits ≤ μ)
    (a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K) (u : Fin (2 ^ laneBits)) :
    blockOf (stackOf hμ a) u = fun x ↦ ofK (a u x) := by
  funext x
  have hx := bitsToNat_lt x
  have hlt : bitsToNat x + 2 ^ (μ - laneBits) * u < 2 ^ μ := by
    have hu := u.isLt
    calc bitsToNat x + 2 ^ (μ - laneBits) * u < 2 ^ (μ - laneBits) * (u + 1) := by nlinarith
      _ ≤ 2 ^ (μ - laneBits) * 2 ^ laneBits := Nat.mul_le_mul_left _ hu
      _ = 2 ^ μ := by rw [← pow_add, Nat.sub_add_cancel hμ]
  simp only [EndToEnd.blockOf, stackOf, Vector.getD, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, hlt, dite_true, Option.getD_some]
  congr 2
  · apply Fin.ext
    simp only
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, zero_add]
  · apply (bitsEquiv (μ - laneBits)).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only [bitsEquiv_val]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- The blocks determine the stack. -/
theorem eq_of_blockOf_eq (hμ : laneBits ≤ μ) {q q' : Column μ}
    (h : ∀ u, blockOf q u = blockOf q' u) : q = q' := by
  obtain ⟨v⟩ := q
  obtain ⟨v'⟩ := q'
  congr 1
  apply Vector.ext
  intro i hi
  -- Cell `i` is cell `x + 2^κ u` of block `u = i / 2^κ`, `x = i % 2^κ`.
  have hu : i / 2 ^ (μ - laneBits) < 2 ^ laneBits := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hμ]
    exact hi
  have hx : bitsToNat ((bitsEquiv (μ - laneBits)).symm
      ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩) = i % 2 ^ (μ - laneBits) := by
    rw [← bitsEquiv_val, Equiv.apply_symm_apply]
  have := congrFun (h ⟨i / 2 ^ (μ - laneBits), hu⟩) ((bitsEquiv (μ - laneBits)).symm
      ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  simp only [EndToEnd.blockOf, hx, Nat.mod_add_div] at this
  have := ofK_injective this
  simpa [Vector.getD, hi] using this

end Stack

/-! ## Polynomials over `K` -/

open Polynomial in
/-- **`K`-valuedness of a polynomial.** A polynomial over `E` of degree at most `d` whose values at
more than `d` points of `K` lie in `K` is over `K`: its limb `1` polynomial vanishes there. -/
theorem exists_map_of_isInK {P : E[X]} {d : ℕ} (hP : P.natDegree ≤ d) (S : Finset K)
    (hS : d < S.card) (hK : ∀ x ∈ S, IsInK (P.eval (ofK x))) :
    ∃ P₀ : K[X], P = P₀.map (algebraMap K E) := by
  classical
  have hφ : ∀ a : K, algebraMap K E a = ofK a := fun _ ↦ rfl
  let L : Fin 2 → K[X] := fun i ↦ ∑ n ∈ Finset.range (d + 1), monomial n ((P.coeff n).limb i)
  have hcoeff : ∀ i n, (L i).coeff n = (P.coeff n).limb i := by
    intro i n
    simp only [L, finsetSum_coeff, coeff_monomial]
    by_cases hn : n < d + 1
    · rw [Finset.sum_eq_single n (fun b _ hb ↦ by simp [hb])
        (fun h ↦ absurd (Finset.mem_range.mpr hn) h)]
      simp
    · have h0 : ∀ b ∈ Finset.range (d + 1),
          (if b = n then (P.coeff b).limb i else 0) = 0 := fun b hb ↦ by
        have : b ≠ n := by rintro rfl; exact hn (Finset.mem_range.mp hb)
        simp [this]
      rw [Finset.sum_eq_zero h0, coeff_eq_zero_of_natDegree_lt (by omega), limb_zero]
  have hdeg : ∀ i, (L i).natDegree ≤ d := fun i ↦ natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ by
    rw [hcoeff, coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by exact_mod_cast hn)), limb_zero]
  have hsplit : P = (L 0).map (algebraMap K E) + C y * (L 1).map (algebraMap K E) := by
    ext n
    rw [coeff_add, coeff_C_mul, coeff_map, coeff_map, hcoeff, hcoeff, hφ, hφ]
    conv_lhs => rw [E.eq_sum_limbs (P.coeff n)]
    rw [mul_comm y]
  have heval : ∀ x : K, P.eval (ofK x) = E.ofLimbs ((L 0).eval x) ((L 1).eval x) := by
    intro x
    conv_lhs => rw [hsplit]
    rw [ofLimbs_eq, eval_add, eval_mul, eval_C, eval_map, eval_map, ← hφ x, eval₂_hom, eval₂_hom,
      hφ, hφ]
    ring
  have h1 : L 1 = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun x hx ↦ ?_) ((hdeg 1).trans_lt hS)
    have := hK x hx
    rw [heval] at this
    simpa [IsInK] using this
  exact ⟨L 0, by rw [hsplit, h1, Polynomial.map_zero, mul_zero, add_zero]⟩

end
end LeanVM.Protocol.Whir.Sound
