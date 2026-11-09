/-
  LeanVM.Guest.Fast.DiscreteLog

  The decoder's discrete-logarithm readers through the computable `discreteLog`: the
  precondition test, B1's `gLog` and `verify_sub`'s `cursorLen`.
-/

module

public import LeanVM.Protocol.Extraction.Fast.DiscreteLog
public import LeanVM.Guest.Located.ReplayFast
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# The decoder's logarithms, computable

`discreteLog` (`Protocol/Extraction/Fast/DiscreteLog.lean`) meets the decoder's interface,
**`discreteLog_discreteLogSpec`**: `DiscreteLogSpec discreteLog` (`Located/ReplayFast.lean`).
Plugged into the readers written over a logarithm:

* `preTest_eq_discreteLog`: `preTest = preTestWith discreteLog`;
* `gLog_eq_discreteLog`: `B1.Main.gLog = gLogWith discreteLog`;
* `cursorLen_eq_discreteLog`: `VerifySub.cursorLen = cursorLenWith discreteLog`. `cursorLen`
  scans `n ≤ 2^32` for `q = p · gen^n`; `cursorLenWith dl` divides `q` by `p` on `p`'s first
  nonzero limb (`limbQuot`), takes `dl` of the quotient and checks `n ≤ 2^32` and `q = p · g^n`
  limb by limb; `cursorLenWith_eq`: given any `DiscreteLogSpec dl`, it is `cursorLen`.

`preTest`, `gLog` and `cursorLen` are not compiled code (noncomputable, or a
`2^32`-step scan), so these are plain equations, not `@[csimp]` lemmas.

`cursorLenWith` reads `dl`'s result through `Option.filter` and `Option.getD`, not a `match`
(`discreteLogWith`'s note).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.B1 LeanVM.Guest.Located

@[expose] public section

/-! ## The interface -/

theorem discreteLog_discreteLogSpec : DiscreteLogSpec discreteLog :=
  fun _ _ ↦ discreteLog_eq_some_iff

/-! ## The precondition and `gLog` -/

theorem preTest_eq_discreteLog : preTest = preTestWith discreteLog :=
  (preTestWith_eq discreteLog_discreteLogSpec).symm

theorem gLog_eq_discreteLog : B1.Main.gLog = gLogWith discreteLog :=
  (gLogWith_eq discreteLog_discreteLogSpec).symm

/-! ## `cursorLen` -/

/-- `q / p` on the first nonzero limb of `p` (`0` when `p = 0`): `g^n` when `q = p · gen^n`. -/
def limbQuot (p q : E) : K :=
  if p.limb 0 ≠ 0 then q.limb 0 * (p.limb 0)⁻¹
  else if p.limb 1 ≠ 0 then q.limb 1 * (p.limb 1)⁻¹ else q.limb 2 * (p.limb 2)⁻¹

/-- **`cursorLen` by a logarithm `dl`**: the logarithm `n` of `a = q / p` (`limbQuot`), kept when
`n ≤ 2^32` and `q = p · a` limb by limb; `0` otherwise. -/
def cursorLenWith (dl : K → Option ℕ) (p q : E) : ℕ :=
  let a := limbQuot p q
  ((dl a).filter fun n ↦
    n ≤ 2 ^ 32 ∧ q = E.ofLimbs (p.limb 0 * a) (p.limb 1 * a) (p.limb 2 * a)).getD 0

theorem mul_gen_pow_eq (p : E) (n : ℕ) :
    p * gen ^ n = E.ofLimbs (p.limb 0 * Parameters.g ^ n) (p.limb 1 * Parameters.g ^ n)
      (p.limb 2 * Parameters.g ^ n) := by
  rw [gen_pow_eq_ofK, eq_ofLimbs p, ofLimbs_mul_ofK]
  simp only [ofLimbs_limb0, ofLimbs_limb1, ofLimbs_limb2]

theorem limbQuot_mul_gen_pow {p : E} (hp : p ≠ 0) (n : ℕ) :
    limbQuot p (p * gen ^ n) = Parameters.g ^ n := by
  unfold limbQuot
  rw [mul_gen_pow_eq]
  simp only [ofLimbs_limb0, ofLimbs_limb1, ofLimbs_limb2]
  split_ifs with h0 h1
  · field_simp
  · field_simp
  · have h2 : p.limb 2 ≠ 0 := fun h2 ↦ hp (by
      rw [eq_ofLimbs p, eq_ofLimbs (0 : E), ofLimbs_inj]
      simp only [limb_zero]
      exact ⟨not_not.1 h0, not_not.1 h1, h2⟩)
    field_simp

theorem limbQuot_zero (q : E) : limbQuot 0 q = 0 := by
  simp [limbQuot, limb_zero]

/-- **By a logarithm, the cursor's length is `cursorLen`**, on every pair. -/
theorem cursorLenWith_eq {dl : K → Option ℕ} (hdl : DiscreteLogSpec dl) :
    cursorLenWith dl = VerifySub.cursorLen := by
  funext p q
  have hsound : ∀ {a : K} {n : ℕ}, dl a = some n → Parameters.g ^ n = a := fun h ↦ ((hdl _ _).1 h).1
  have hcompl : ∀ n < 2 ^ 64 - 1, dl (Parameters.g ^ n) = some n := fun n hn ↦ (hdl _ _).2 ⟨rfl, hn⟩
  simp only [cursorLenWith]
  cases h : dl (limbQuot p q) with
  | none =>
    rw [Option.filter_none, Option.getD_none]
    by_cases hex : ∃ n ≤ 2 ^ 32, q = p * gen ^ n
    · obtain ⟨n, hn, rfl⟩ := hex
      by_cases hp : p = 0
      · subst hp
        unfold VerifySub.cursorLen
        rw [zero_mul, List.range_succ_eq_map, List.find?_cons]
        simp
      · rw [limbQuot_mul_gen_pow hp, hcompl n (by omega)] at h
        exact absurd h (by simp)
    · unfold VerifySub.cursorLen
      rw [List.find?_eq_none.2 fun n hn h ↦ hex ⟨n, by simpa [Nat.lt_succ_iff] using hn,
        of_decide_eq_true h⟩]
      rfl
  | some n =>
    have hx := hsound h
    rw [Option.filter_some]
    by_cases hc : n ≤ 2 ^ 32 ∧ q = E.ofLimbs (p.limb 0 * limbQuot p q) (p.limb 1 * limbQuot p q)
        (p.limb 2 * limbQuot p q)
    · simp only [decide_eq_true hc, ↓reduceIte, Option.getD_some]
      obtain ⟨hn32, hq⟩ := hc
      rw [← hx, ← mul_gen_pow_eq] at hq
      by_cases hp : p = 0
      · subst hp
        rw [limbQuot_zero] at hx
        exact absurd hx (pow_ne_zero n g_ne_zero)
      · rw [VerifySub.cursorLen_eq hp hq hn32]
    · simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
      by_cases hex : ∃ m ≤ 2 ^ 32, q = p * gen ^ m
      · obtain ⟨m, hm, rfl⟩ := hex
        by_cases hp : p = 0
        · subst hp
          rw [limbQuot_zero] at hx
          exact absurd hx (pow_ne_zero n g_ne_zero)
        · rw [limbQuot_mul_gen_pow hp, hcompl m (by omega)] at h
          obtain rfl := Option.some.inj h
          exact absurd ⟨hm, by rw [limbQuot_mul_gen_pow hp, ← mul_gen_pow_eq]⟩ hc
      · unfold VerifySub.cursorLen
        rw [List.find?_eq_none.2 fun n hn h ↦ hex ⟨n, by simpa [Nat.lt_succ_iff] using hn,
          of_decide_eq_true h⟩]
        rfl

theorem cursorLen_eq_discreteLog : VerifySub.cursorLen = cursorLenWith discreteLog :=
  (cursorLenWith_eq discreteLog_discreteLogSpec).symm

end

end LeanVM.Guest.Fast
