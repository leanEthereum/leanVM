module

public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Protocol.Extraction.Fast.RootFinder
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Data.Array.Lemmas

/-!
# Sizes along the decoder: the root finder

* **`rootsInFieldFast_size_le`**: the root finder returns at most `deg p` roots (distinct roots of
  `p`, `fieldRootCtx_nodup`); at a Roth–Ruckenstein node the equation `initialCoeffFast Q` has at
  most `|Q|` coefficients (`initialCoeffFast_size_le`);
* **remainders**: CompPoly's remainder-only division by a monic `q` returns fewer than `|q|`
  coefficients (`modByMonicRemainderOnly_size_lt`: each cancellation drops the top coefficient),
  `monicNormalize` keeps the size of the trimmed input and ends in `1` (`monicNormalize_size`,
  `monicNormalize_getLastD`); so `x² mod u` (`sqMod_size_lt`) and every Frobenius power
  `X^(2^i) mod u` (`frobeniusPowersFast_size_lt`) have at most `deg u` coefficients, and the
  squarings at most `deg u` from the second on (`squaringsFrom_size_lt`).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters

public section

/-! ## The roots -/

/-- **The root finder returns at most `deg p` roots.** -/
theorem rootsInFieldFast_size_le (p : CPolynomial K) : (rootsInFieldFast p).size ≤ p.natDegree := by
  by_cases hp : p = 0
  · simp [rootsInFieldFast, hp]
  have hnd : (rootsInFieldFast p).toList.Nodup := fieldRootCtxFast_nodup p
  have hroot : ∀ a ∈ (rootsInFieldFast p).toList, p.toPoly.IsRoot a := fun a ha ↦ by
    rw [Polynomial.IsRoot, ← CPolynomial.eval_toPoly]
    exact fieldRootCtxFast.sound p a ha
  have hp' : p.toPoly ≠ 0 := by
    intro h; apply hp; rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_zero]; exact h
  rw [← Array.length_toList, ← List.toFinset_card_of_nodup hnd, Finset.card_eq_sum_ones,
    CPolynomial.natDegree_toPoly]
  refine le_trans (Finset.sum_le_sum fun a ha ↦ ?_) (sum_rootMultiplicity_le p.toPoly _)
  exact (Polynomial.rootMultiplicity_pos hp').2 (hroot a (List.mem_toFinset.1 ha))

/-- The equation at a Roth–Ruckenstein node has at most `|Q|` coefficients. -/
theorem initialCoeffFast_size_le {F : Type*} [Field F] [BEq F] [LawfulBEq F] (Q : CBivariate F) :
    (initialCoeffFast Q).val.size ≤ Q.val.size :=
  (CPolynomial.Raw.Trim.size_le_size _).trans (by rw [Array.size_map])

/-! ## Remainders -/

section Remainder

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- A trimmed array whose coefficients vanish from `X` on has at most `X` entries. -/
theorem trim_size_le_of_coeff (p : CPolynomial.Raw F) (X : ℕ)
    (h : ∀ i, X ≤ i → p.coeff i = 0) : p.trim.size ≤ X := by
  by_contra hlt
  rcases CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero.1
      (CPolynomial.Raw.Trim.trim_twice p) with h0 | hne
  · omega
  · apply hne
    have := h (p.trim.size - 1) (by omega)
    rw [← CPolynomial.Raw.Trim.coeff_eq_coeff, CPolynomial.Raw.coeff] at this
    rw [Array.getLastD]
    exact this

/-- **A cancellation step drops the top coefficient**: `p − p_top·X^(|p|−|q|)·q`, `q` ending in
`1`, `p` trimmed, `|q| ≤ |p|`, has fewer than `|p|` coefficients. -/
theorem subScaledShift_size_lt (p q : CPolynomial.Raw F) (hp : p.trim = p) (hq1 : 1 ≤ q.size)
    (hql : q.getLastD 0 = 1) (hqp : q.size ≤ p.size) :
    (CPolynomial.Raw.subScaledShift p q p.leadingCoeff (p.size - q.size)).size < p.size := by
  rw [CPolynomial.Raw.subScaledShift]
  dsimp only
  refine lt_of_le_of_lt (trim_size_le_of_coeff _ (p.size - 1) fun i hi ↦ ?_) (by omega)
  rw [CPolynomial.Raw.coeff, CPolynomial.Raw.mk]
  by_cases hip : i < p.size
  · have hi' : i = p.size - 1 := by omega
    subst hi'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hip, ↓reduceDIte, Option.getD_some]
    have hc : p.size - q.size ≤ p.size - 1 ∧ p.size - 1 - (p.size - q.size) < q.size := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc), show p.size - 1 - (p.size - q.size) = q.size - 1 by omega]
    have hq : q.coeff (q.size - 1) = 1 := by
      rw [CPolynomial.Raw.coeff]; exact hql
    have hlead : p.leadingCoeff = p.coeff (p.size - 1) := by
      rw [CPolynomial.Raw.leadingCoeff, hp, Array.getLastD, CPolynomial.Raw.coeff]
    rw [hq, hlead, mul_one, sub_self]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [hip]

/-- **The remainder-only division by a monic `q` returns fewer than `|q|` coefficients** (with
fuel enough: `|p| < fuel + |q|`). -/
theorem modByMonicRemainderOnly_go_size_lt (q : CPolynomial.Raw F) (hq1 : 1 ≤ q.size)
    (hql : q.getLastD 0 = 1) (n : ℕ) :
    ∀ p : CPolynomial.Raw F, p.trim = p → p.size < n + q.size →
      (CPolynomial.Raw.modByMonicRemainderOnly.go n p q).size < q.size := by
  induction n with
  | zero => intro p _ h; rw [CPolynomial.Raw.modByMonicRemainderOnly.go]; omega
  | succ n ih =>
    intro p hp h
    rw [CPolynomial.Raw.modByMonicRemainderOnly.go]
    split
    · assumption
    · rename_i hge
      dsimp only
      have hlt := subScaledShift_size_lt p q hp hq1 hql (by omega)
      exact ih _ (CPolynomial.Raw.subScaledShift_is_trimmed _ _ _ _) (by omega)

theorem modByMonicRemainderOnly_size_lt (p q : CPolynomial.Raw F) (hp : p.trim = p)
    (hq1 : 1 ≤ q.size) (hql : q.getLastD 0 = 1) :
    (CPolynomial.Raw.modByMonicRemainderOnly p q).size < q.size :=
  modByMonicRemainderOnly_go_size_lt q hq1 hql p.size p hp (by omega)

theorem trim_getLastD_ne_zero (u : CPolynomial.Raw F) (hu : u.trim ≠ 0) :
    u.trim.getLastD 0 ≠ 0 := by
  rcases CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero.1
      (CPolynomial.Raw.Trim.trim_twice u) with h0 | hne
  · exact absurd (Array.eq_empty_of_size_eq_zero h0) hu
  · exact hne

omit [LawfulBEq F] in
theorem monicNormalize_eq (u : CPolynomial.Raw F) (hu : u.trim ≠ 0) :
    CPolynomial.Raw.monicNormalize u = u.trim.leadingCoeff⁻¹ • u.trim := by
  rw [CPolynomial.Raw.monicNormalize]
  have : (u.trim == 0) = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]

omit [LawfulBEq F] in
/-- `monicNormalize` keeps the trimmed input's size. -/
theorem monicNormalize_size (u : CPolynomial.Raw F) (hu : u.trim ≠ 0) :
    (CPolynomial.Raw.monicNormalize u).size = u.trim.size := by
  rw [monicNormalize_eq u hu]
  show (Array.map _ u.trim).size = _
  rw [Array.size_map]

/-- `monicNormalize` ends in `1`. -/
theorem monicNormalize_getLastD (u : CPolynomial.Raw F) (hu : u.trim ≠ 0) :
    (CPolynomial.Raw.monicNormalize u).getLastD 0 = 1 := by
  have hne := trim_getLastD_ne_zero u hu
  have hpos : 0 < u.trim.size := by
    rcases Nat.eq_zero_or_pos u.trim.size with h | h
    · exact absurd (Array.eq_empty_of_size_eq_zero h) hu
    · exact h
  rw [monicNormalize_eq u hu]
  show (Array.map _ u.trim).getLastD 0 = 1
  rw [Array.getLastD, Array.size_map, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some]
  have hl : u.trim.leadingCoeff = u.trim[u.trim.size - 1] := by
    rw [CPolynomial.Raw.leadingCoeff, CPolynomial.Raw.Trim.trim_twice, Array.getLastD,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  have hne' : u.trim[u.trim.size - 1] ≠ 0 := by
    rw [Array.getLastD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some] at hne
    exact hne
  rw [hl]
  exact inv_mul_cancel₀ hne'

/-- **A product reduced modulo a nonzero `u`** has fewer than `|trim u|` coefficients. -/
theorem mulModWith_size_lt (u a b : CPolynomial.Raw F) (hu : u.trim ≠ 0) :
    (CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u a b).size < u.trim.size := by
  rw [CPolynomial.Raw.mulModWith]
  have : (u.trim == 0) = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hpos : 0 < u.trim.size := by
    rcases Nat.eq_zero_or_pos u.trim.size with h | h
    · exact absurd (Array.eq_empty_of_size_eq_zero h) hu
    · exact h
  rw [← monicNormalize_size u hu]
  exact modByMonicRemainderOnly_size_lt _ _ (CPolynomial.Raw.mul_is_trimmed _ _)
    (by rw [monicNormalize_size u hu]; exact hpos) (monicNormalize_getLastD u hu)

end Remainder

/-! ## The Frobenius powers -/

theorem cpoly_trim_ne_zero {u : CPolynomial K} (hu : u ≠ 0) : u.val.trim ≠ 0 := by
  rw [CPolynomial.Raw.Trim.trim_eq_of_isCanonical u.property]
  intro h
  exact hu (Subtype.ext h)

/-- **`x² mod u` has at most `deg u` coefficients.** -/
theorem sqMod_size_lt {u : CPolynomial K} (hu : u ≠ 0) (c : CPolynomial.Raw K) :
    (sqMod u.val c).size < u.val.size := by
  have h := mulModWith_size_lt u.val c c (cpoly_trim_ne_zero hu)
  rwa [CPolynomial.Raw.Trim.trim_eq_of_isCanonical u.property] at h

/-- **The squarings modulo `u`**: from the second on, at most `deg u` coefficients. -/
theorem squaringsFrom_size_lt {u : CPolynomial K} (hu : u ≠ 0) (n : ℕ) (c : CPolynomial.Raw K) :
    ∀ x ∈ squaringsFrom u.val n c, x = c ∨ x.size < u.val.size := by
  induction n generalizing c with
  | zero => intro x hx; simp [squaringsFrom] at hx
  | succ n ih =>
    intro x hx
    rw [squaringsFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases ih _ x hx with rfl | h
      · exact Or.inr (sqMod_size_lt hu c)
      · exact Or.inr h

/-- **Every Frobenius power `X^(2^i) mod u` has at most `deg u` coefficients.** -/
theorem frobeniusPowersFast_size_lt {u : CPolynomial K} (hu : u ≠ 0) (k : ℕ)
    {p : CPolynomial K} (hp : p ∈ frobeniusPowersFast u k) : p.val.size < u.val.size := by
  rw [frobeniusPowersFast, List.mem_toArray, List.mem_map] at hp
  obtain ⟨c, -, rfl⟩ := hp
  refine lt_of_le_of_lt (CPolynomial.Raw.Trim.size_le_size _) ?_
  generalize (if (u.val.trim == 0) = true then (1 : CPolynomial.Raw K)
    else CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) = acc
  exact lt_of_lt_of_eq (mulModWith_size_lt u.val acc c (cpoly_trim_ne_zero hu))
    (by rw [CPolynomial.Raw.Trim.trim_eq_of_isCanonical u.property])

end

end LeanVM.Cost.Bounds
