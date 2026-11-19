module

public import NativeVm.Code.Phase7.Frame

/-!
# Phase 7's data in words: congruence and growth

What phase 7's own regions need beyond `NativeVm.Code.Data`: each predicate read through `Same`
(`GluedAt.congr`, `WhirAt.congr`, `RoundsAt.congr`), arrays grown by one element (`EVec.push`,
`WVec.push`, `RoundsAt.push`), and reading registers and words through stores (`msimp`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wd_inj wd_zero)

variable {mem mem' : UInt64 → Option UInt64} {p : UInt64}

theorem gluedWords_val : gluedWords = 758 := by decide
theorem gluedQOff_val : gluedQOff = 66 := by decide
theorem gluedWOff_val : gluedWOff = 297 := by decide
theorem whirGluedOff_val : whirGluedOff = 63 := by decide
theorem whirWords_val : whirWords = 7644 := by decide
theorem vecWords_stackCap : vecWords stackCap = 61 := by decide
theorem wvecWords_queryCap : wvecWords queryCap = 231 := by decide
theorem vecWords_queryCap : vecWords queryCap = 461 := by decide
theorem roundsWords_val : roundsWords = 25 := by decide
theorem stackCap_val : stackCap = 30 := by decide
theorem gluedCap_val : gluedCap = 10 := by decide
theorem roundCap_val : roundCap = 6 := by decide
theorem queryCap_val : queryCap = 230 := by decide

/-- Unfold phase 7's layout numbers, then `omega`. -/
macro "vomega" : tactic => `(tactic| first
  | omega
  | (simp only [gluedWords_val, gluedQOff_val, gluedWOff_val, whirGluedOff_val, whirWords_val,
      vecWords_stackCap, wvecWords_queryCap, vecWords_queryCap, roundsWords_val, stackCap_val,
      gluedCap_val, roundCap_val, queryCap_val, vecWords, wvecWords] at *; omega))

theorem Same.sub' {n : Nat} (h : Same mem mem' p n) {a m : Nat} (ha : a + m ≤ n) :
    Same mem mem' (wd p a) m := h.sub ha

theorem _root_.NativeVm.Code.GluedAt.congr {g : GluedClaimW} (h : Same mem mem' p gluedWords) (hg : GluedAt mem p g) :
    GluedAt mem' p g := by
  rw [gluedWords_val] at h
  obtain ⟨h1, h2, h3⟩ := hg
  have h0 : Same mem mem' p 2 := fun k hk ↦ h k (by omega)
  refine ⟨h1.congr h0, h2.congr (h 2 (by omega)), ?_⟩
  cases hw : g.weight with
  | eq z =>
    rw [hw] at h3
    obtain ⟨e3, e4⟩ := h3
    exact ⟨h.word (by omega) e3, e4.congr (h.sub (by vomega))⟩
  | induced mu qs ws =>
    rw [hw] at h3
    obtain ⟨e3, e4, e5, e6⟩ := h3
    exact ⟨h.word (by omega) e3, e4.congr (h 4 (by omega)),
      e5.congr (h.sub (by vomega)),
      e6.congr (h.sub (by vomega))⟩

/-- The glued claims' words: the count and the claims. -/
theorem gluedAll_congr {gs : Array GluedClaimW} (hsz : gs.size ≤ gluedCap)
    (h : Same mem mem' (wd p whirGluedOff) (1 + gluedWords * gluedCap))
    (hn : NatAt mem (wd p whirGluedOff) gs.size)
    (hg : ∀ i (h : i < gs.size), GluedAt mem (wd p (whirGluedOff + 1 + gluedWords * i)) gs[i]) :
    NatAt mem' (wd p whirGluedOff) gs.size ∧
      ∀ i (h : i < gs.size), GluedAt mem' (wd p (whirGluedOff + 1 + gluedWords * i)) gs[i] := by
  refine ⟨hn.congr (h.base (by omega) rfl), fun i hi ↦ (hg i hi).congr ?_⟩
  have h' := h.sub (a := 1 + gluedWords * i) (m := gluedWords) (by
    rw [gluedCap_val] at hsz ⊢; rw [gluedWords_val]; omega)
  rwa [wd_wd, ← Nat.add_assoc] at h'

theorem _root_.NativeVm.Code.WhirAt.congr {sW : WhirStateW} (h : Same mem mem' p whirWords) (hw : WhirAt mem p sW) :
    WhirAt mem' p sW := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  have hg := gluedAll_congr h3 (h.sub (by vomega)) h4 h5
  have h0 : Same mem mem' p 2 := fun k hk ↦ h k (by rw [whirWords_val]; omega)
  exact ⟨h1.congr h0, h2.congr (h.sub (by vomega)),
    h3, hg.1, hg.2⟩

/-- WHIR's state with a new claim and new `α`s, its glued claims' words kept. -/
theorem _root_.NativeVm.Code.WhirAt.update {sW : WhirStateW} {claim : EW} {alphas : Array EW} (hw : WhirAt mem p sW)
    (h : Same mem mem' (wd p whirGluedOff) (1 + gluedWords * gluedCap))
    (hc : EWAt mem' p claim) (ha : EVec mem' (wd p 2) stackCap alphas) :
    WhirAt mem' p { sW with claim := claim, alphas := alphas } := by
  obtain ⟨-, -, h3, h4, h5⟩ := hw
  have hg := gluedAll_congr h3 h h4 h5
  exact ⟨hc, ha, h3, hg.1, hg.2⟩

theorem _root_.NativeVm.Code.RoundsAt.congr {rs : Array FoldRoundW} (h : Same mem mem' p roundsWords)
    (hr : RoundsAt mem p rs) : RoundsAt mem' p rs := by
  obtain ⟨h1, h2, h3⟩ := hr
  rw [roundsWords_val] at h
  have := h1; rw [roundCap_val] at this
  refine ⟨h1, h2.congr (h.base (by omega) rfl), fun i hi ↦
    ⟨(h3 i hi).1.congr (h.sub (by omega)), (h3 i hi).2.congr (h.sub (by omega))⟩⟩

/-- An array of elements grown by one. -/
theorem _root_.NativeVm.Code.EVec.push {cap : Nat} {xs : Array EW} {x : EW} (h : EVec mem p cap xs)
    (hs : Same mem mem' (wd p 1) (2 * xs.size)) (hn : NatAt mem' p (xs.size + 1))
    (hx : EWAt mem' (wd p (1 + 2 * xs.size)) x) (hcap : xs.size < cap) :
    EVec mem' p cap (xs.push x) := by
  refine ⟨by rw [Array.size_push]; omega, by rw [Array.size_push]; exact hn, fun i hi ↦ ?_⟩
  rw [Array.size_push] at hi
  rw [wd_wd]
  by_cases hi' : i < xs.size
  · rw [Array.getElem_push_lt hi']
    have := (h.2.2 i hi').congr (hs.sub (a := 2 * i) (m := 2) (by omega))
    rwa [wd_wd] at this
  · have e : i = xs.size := by omega
    subst e
    rw [Array.getElem_push_eq]
    exact hx

/-- A word array grown by one. -/
theorem _root_.NativeVm.Code.WVec.push {cap : Nat} {xs : Array UInt64} {x : UInt64} (h : WVec mem p cap xs)
    (hs : Same mem mem' (wd p 1) xs.size) (hn : NatAt mem' p (xs.size + 1))
    (hx : mem' (wd p (1 + xs.size)) = some x) (hcap : xs.size < cap) :
    WVec mem' p cap (xs.push x) := by
  refine ⟨by rw [Array.size_push]; omega, by rw [Array.size_push]; exact hn, fun i hi ↦ ?_⟩
  rw [Array.size_push] at hi
  rw [wd_wd]
  by_cases hi' : i < xs.size
  · rw [Array.getElem_push_lt hi', ← wd_wd]
    exact hs.word hi' (h.2.2 i hi')
  · have e : i = xs.size := by omega
    subst e
    rw [Array.getElem_push_eq]
    exact hx

/-- The fold rounds grown by one. -/
theorem _root_.NativeVm.Code.RoundsAt.push {rs : Array FoldRoundW} {r : FoldRoundW} (h : RoundsAt mem p rs)
    (hs : Same mem mem' (wd p 1) (4 * rs.size)) (hn : NatAt mem' p (rs.size + 1))
    (ha : EWAt mem' (wd p (1 + 4 * rs.size)) r.alpha) (hb : EWAt mem' (wd p (3 + 4 * rs.size)) r.beta)
    (hcap : rs.size < roundCap) : RoundsAt mem' p (rs.push r) := by
  refine ⟨by rw [Array.size_push]; omega, by rw [Array.size_push]; exact hn, fun i hi ↦ ?_⟩
  rw [Array.size_push] at hi
  by_cases hi' : i < rs.size
  · rw [Array.getElem_push_lt hi']
    exact ⟨(h.2.2 i hi').1.congr (by
        have := hs.sub (a := 4 * i) (m := 2) (by omega); rwa [wd_wd] at this),
      (h.2.2 i hi').2.congr (by
        have := hs.sub (a := 4 * i + 2) (m := 2) (by omega)
        rwa [wd_wd, show 1 + (4 * i + 2) = 3 + 4 * i by omega] at this)⟩
  · have e : i = rs.size := by omega
    subst e
    rw [Array.getElem_push_eq]
    exact ⟨ha, hb⟩

/-! ## Reading through stores -/

theorem setMem_ne (s : QState) {a b : UInt64} (v : UInt64) (h : b ≠ a) :
    (s.setMem a v).mem b = s.mem b := by
  simp [QState.setMem_mem, h]

theorem wd_ne {b : UInt64} {k k' : Nat} (h : k ≠ k') (hk : k < 2 ^ 61) (hk' : k' < 2 ^ 61) :
    wd b k ≠ wd b k' := fun e ↦ h ((wd_inj hk hk').mp e)

theorem ite_no {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem ite_yes {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

end NativeVm.Code.P7
