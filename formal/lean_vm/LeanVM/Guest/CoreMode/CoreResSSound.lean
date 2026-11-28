/-
  LeanVM.Guest.CoreMode.CoreResSSound

  The `subRS` family sound at any valuation where the certificate's facts hold (`subRS_sound`), and a certificate's
  residuals of families all sound given those of `resFamG` (`resOk_sound`).
-/

module

public import LeanVM.Guest.CoreMode.CoreResG
public import LeanVM.Guest.CoreMode.HeapCRun

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

public section

/-- A fact `e(x) < m`, `m < 2^62`, at a valuation: `x = g^e`, `e < m`. -/
theorem ltNum_pow {σ : Val} {x m : ℕ} (hy : (CRes.lt (.val x) (.num m)).Holds σ) (hm : m < capE) :
    ∃ e < m, σ (V.n x) = ofK (addressOfIndex e) := by
  have hy' : LtF (vw σ) (idxC (.val x)) (idxC (.num m)) := hy
  obtain ⟨ya, yb, ha, hb, hab⟩ := hy'
  simp only [idxC, valW_baseC, vw] at ha
  simp only [idxC] at hb
  rw [rep_const hm, Option.some.injEq] at hb
  subst hb
  exact ⟨ya, hab, (rep_spec ha).2⟩

/-- **A fact's bound holds** (`factOf`) where the conditions `g` and the fact hold. -/
theorem factOf_sound {σ : Val} {L : List CRes} {g : List CCond} (hg : ∀ c ∈ g, c.Holds σ) {v n : ℕ} {y : CRes}
    (h : factOf g v y = some n) (hy : subRS L y = false → y.Holds σ) :
    ∃ e < n, σ (V.n v) = ofK (addressOfIndex e) := by
  unfold factOf at h
  split at h
  · rename_i x m
    have hy' := hy rfl
    cases hc : (Nat.beq x v && Nat.blt m capE)
    · rw [hc] at h; cases h
    · rw [hc] at h
      simp only [Bool.cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
      obtain ⟨rfl, hm⟩ := hc
      exact ltNum_pow hy' hm
  · rename_i g' x m
    have hy' := hy rfl
    cases hc : (Nat.beq x v && Nat.blt m capE && g'.all fun c ↦ g.contains c)
    · rw [hc] at h; cases h
    · rw [hc] at h
      simp only [Bool.cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, List.all_eq_true] at hc
      obtain ⟨⟨rfl, hm⟩, hsub⟩ := hc
      exact ltNum_pow (hy' fun c hc ↦ hg c (by simpa using hsub c hc)) hm
  · cases h

/-- **The least fact's bound holds** (`factB`) where the conditions `g` and the certificate's facts hold. -/
theorem factB_sound {σ : Val} {L : List CRes} {g : List CCond} (hF : ∀ y ∈ L, subRS L y = false → y.Holds σ)
    (hg : ∀ c ∈ g, c.Holds σ) (v n : ℕ) (h : factB L g v = some n) : ∃ e < n, σ (V.n v) = ofK (addressOfIndex e) := by
  obtain ⟨y, hy, hyf⟩ := List.mem_filterMap.mp (List.min?_mem h)
  exact factOf_sound hg hyf (hF y hy)

theorem prodW_append (w : ℕ → E) : ∀ (a b : List (ℕ × ℕ)), prodW w (a ++ b) = prodW w a * prodW w b
  | [], b => by simp [prodW]
  | (x, e) :: a, b => by simp only [List.cons_append, prodW, prodW_append w a b, mul_assoc]

section

variable {σ : Val} {L : List CRes} {g : List CCond}
  (hf : ∀ v n, factB L g v = some n → ∃ e < n, σ (V.n v) = ofK (addressOfIndex e))
include hf

/-- **A product's exponent at most `prodMax`.** -/
theorem prodMax_sound : ∀ {bs : List (ℕ × ℕ)} {M : ℕ}, prodMax L g bs = some M →
    ∃ e ≤ M, prodW (vw σ) bs = ofK (addressOfIndex e)
  | [], M, h => by
    simp only [prodMax, Option.some.injEq] at h
    subst h
    exact ⟨0, le_rfl, by simp [prodW, addressOfIndex]⟩
  | (v, a) :: bs, M, h => by
    simp only [prodMax] at h
    cases hv : factB L g v with
    | none => simp [hv] at h
    | some n =>
      cases hb : prodMax L g bs with
      | none => simp [hv, hb] at h
      | some Mb =>
        simp only [hv, hb, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨e1, he1, h1⟩ := hf v n hv
        obtain ⟨e2, he2, h2⟩ := prodMax_sound hb
        refine ⟨a * e1 + e2, Nat.add_le_add (Nat.mul_le_mul_left a (by omega)) he2, ?_⟩
        have hpw : ∀ (y : K) (n : ℕ), ofK y ^ n = ofK (y ^ n) := fun y n ↦ (map_pow (algebraMap K E) y n).symm
        simp only [prodW]
        rw [show vw σ v = σ (V.n v) from rfl, h1, h2, hpw, ← ofK_mul', addressOfIndex, addressOfIndex,
          addressOfIndex, ← pow_mul, ← pow_add, mul_comm e1 a]

/-- **An index's exponent at most `idxMax`.** -/
theorem idxMax_sound : ∀ {i : CIdx} {H y : ℕ}, idxMax L g i = some H → rep ((idxC i).valW (vw σ)) = some y → y ≤ H
  | .num h, H, y, hH, hy => by
    simp only [idxMax, Option.some.injEq] at hH
    subst hH
    exact rep_le hy (by simp only [idxC]; exact valW_const h)
  | .val v, H, y, hH, hy => by
    simp only [idxMax] at hH
    cases hv : factB L g v with
    | none => simp [hv] at hH
    | some n =>
      simp only [hv, Option.map_some, Option.some.injEq] at hH
      subst hH
      obtain ⟨e, he, hσ⟩ := hf v n hv
      have := rep_le hy (by simp only [idxC, valW_baseC, vw]; exact hσ)
      omega
  | .mono c, H, y, hH, hy => by
    simp only [idxMax] at hH
    cases hp : prodMax L g c.bases with
    | none => simp [hp] at hH
    | some M =>
      simp only [hp, Option.map_some, Option.some.injEq] at hH
      subst hH
      obtain ⟨e, he, hpe⟩ := prodMax_sound hf hp
      have := rep_le hy (z := e + c.off) (by
        simp only [idxC, CCell.valW]
        rw [hpe, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, pow_add])
      omega

/-- **A symbolic run inside a constant run** (`subRSg`) where its facts hold. -/
theorem subRSg_sound {q r : CRun} (h : subRSg L g q r = true) : ∀ x, q.Set (vw σ) x → r.Set (vw σ) x := by
  obtain ⟨⟨qb, qo⟩, S, ql, qh⟩ := q
  obtain ⟨⟨rb, ro⟩, S', rl, rh⟩ := r
  unfold subRSg at h
  split at h
  · rename_i l N hrl hrh
    simp only at hrl hrh
    subst hrl hrh
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq, Option.any_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hb, hS⟩, hro⟩, hl⟩, hN⟩, H, hH, M, hM, hlt⟩ := h
    subst hS
    have htk := basesBeq_eq hb
    obtain ⟨d, rfl⟩ : ∃ d, qo = ro + d := ⟨qo - ro, by omega⟩
    rw [Nat.add_sub_cancel_left] at hl hlt
    intro x hx
    obtain ⟨ylo, yhi, j, -, hyhi, -, hjh, rfl⟩ := hx
    have hyH := idxMax_sound hf hH hyhi
    obtain ⟨e, he, hpe⟩ := prodMax_sound hf hM
    have hSj : S * j ≤ S * (H - 1) := Nat.mul_le_mul_left _ (by omega)
    refine ⟨l, N, d + e + S * j, (by simp only [idxC]; exact rep_const (by omega)),
      (by simp only [idxC]; exact rep_const hN), by omega, by omega, ?_⟩
    have hq : prodW (vw σ) qb = prodW (vw σ) rb * ofK (addressOfIndex e) := by
      rw [← List.take_append_drop rb.length qb, prodW_append, htk, hpe]
    have hA : ∀ a b, ofK (addressOfIndex (a + b)) = ofK (addressOfIndex a) * ofK (addressOfIndex b) := by
      intro a b
      rw [addressOfIndex, addressOfIndex, addressOfIndex, pow_add, ofK_mul']
    have key : CCell.valW (vw σ) ⟨qb, ro + d⟩ * ofK (addressOfIndex (S * j)) =
        CCell.valW (vw σ) ⟨rb, ro⟩ * ofK (addressOfIndex (1 * (d + e + S * j))) := by
      show prodW (vw σ) qb * ofK (addressOfIndex (ro + d)) * ofK (addressOfIndex (S * j)) =
        prodW (vw σ) rb * ofK (addressOfIndex ro) * ofK (addressOfIndex (1 * (d + e + S * j)))
      rw [hq, Nat.one_mul, hA ro d, hA (d + e) (S * j), hA d e]
      ring
    exact congrArg (fun z : E ↦ z.limb 0) key
  · cases h

end

/-- **The `subRS` family holds** at a valuation where the certificate's other residuals hold (its facts among them). -/
theorem subRS_sound {σ : Val} {L : List CRes} (hF : ∀ y ∈ L, subRS L y = false → y.Holds σ) :
    ∀ x : CRes, subRS L x = true → x.Holds σ
  | .subR q r, h => subRSg_sound (factB_sound hF (fun _ hc ↦ by simp at hc)) h
  | .under g (.subR q r), h => fun hg ↦ subRSg_sound (factB_sound hF hg) h
  | .lt _ _, h | .nz _, h | .sub _ _, h | .subP _ _, h | .eq _ _, h => by simp [subRS] at h
  | .under _ (.lt _ _), h | .under _ (.nz _), h | .under _ (.sub _ _), h | .under _ (.under _ _), h
  | .under _ (.subP _ _), h | .under _ (.eq _ _), h => by simp [subRS] at h

/-- **Every residual of a certificate holds** (`resOk`) where those of `resFamG` do. -/
theorem resOk_sound {Cf : CFun} (h : resOk Cf = true) {σ : Val}
    (hb : ∀ x ∈ Cf.H.res, resFamG Cf.fn Cf.xc Cf.H.sig.gw x = true → x.Holds σ) : ∀ x ∈ Cf.H.res, x.Holds σ := by
  have hall := List.all_eq_true.mp h
  have hF : ∀ y ∈ Cf.H.res, subRS Cf.H.res y = false → y.Holds σ := fun y hy hs ↦
    hb y hy (by have := hall y hy; simpa [resOkR, hs] using this)
  intro x hx
  have := hall x hx
  simp only [resOkR, Bool.or_eq_true] at this
  rcases this with h1 | h1
  · exact hb x hx h1
  · exact subRS_sound hF x h1

end

end LeanVM.Guest.CoreMode
