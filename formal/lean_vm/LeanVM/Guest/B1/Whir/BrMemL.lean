/-
  LeanVM.Guest.B1.Whir.BrMemL

  A level's memory facts from the buffers' honest words.
-/

module

public import LeanVM.Guest.B1.Whir.BrFit

/-!
# A level's memory from the buffers' words

`OsSizes`: the candidate's rows fit its buffers (the strides of `ood_z`,
`basis_d`, the squeeze runs, the tail challenges, the levels' slots in `query_positions`,
`merkle_caps` and `merkle_cap_active`). `fall_length`: all fold challenges, `nFolds` of them.
`lvMemB_cont`: on a memory holding the fixed buffers' honest words at `P` and level `i`'s squeeze
chain at `sqz`, the level's memory facts `LvMemB` hold.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **The candidate's rows fit its buffers.** -/
structure OsSizes (c : OsCfg) : Prop where
  sq : ∀ i < c.levels.length, (lvAt c i).squeezes ≤ c.maxSq
  cols : ∀ i < c.levels.length, (lvAt c i).logCols ≤ ligColsCap
  yr : c.yrLog ≤ yrLogCap
  pos : ∀ i < c.levels.length, (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤
    if i + 1 < c.levels.length then (lvAt c (i + 1)).posOff else c.posLen
  caps : ∀ i < c.levels.length, 4 * (lvAt c i).capOff + 2 ^ ((lvAt c i).capDepth + 2) ≤
    if i + 1 < c.levels.length then 4 * (lvAt c (i + 1)).capOff else 4 * c.capLen
  flags : ∀ i < c.levels.length, (lvAt c i).capOff + 2 ^ (lvAt c i).capDepth ≤
    if i + 1 < c.levels.length then (lvAt c (i + 1)).capOff else c.capLen

/-- The fixed buffers' honest words in memory. -/
structure FixedMem (rd : Reader) (P : OsPtrs) (c : OsCfg) (tr : OsTr) : Prop where
  fch : ReadsAt rd P.fch (fchC c tr)
  roots : ReadsAt rd P.roots (rootsC c tr)
  betas : ReadsAt rd P.betas (betasC c tr)
  mus : ReadsAt rd P.mus (musC c tr)
  win : ReadsAt rd P.win winC
  qpos : ReadsAt rd P.qpos (qposC c tr)
  oodz : ReadsAt rd P.oodz (oodzC c tr)
  ood : ReadsAt rd P.ood (oodC c tr)
  fmsg : ReadsAt rd P.fmsg (fmsgC c tr)

variable {c : OsCfg} {tr : OsTr}

theorem fall_length {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg)
    (h : TrFit c tr) : tr.Fall.length = c.nFolds := by
  have hn := hF.n2
  have hi : c.levels.length - 1 < c.levels.length := by omega
  rw [OsTr.Fall, h.lf, SpLv.wsEnd_folds, List.length_append, h.off _ hi, SpLv.chs_length,
    (h.fit _ hi).fold]
  have := hF.lastF
  rwa [getLastD_eq_getD _ (by intro h; rw [h] at hn; simp at hn)] at this

theorem fall_chs (h : TrFit c tr)
    {i : ℕ} (hi : i < c.levels.length) {j : ℕ} (hj : j < (lvAt c i).folds) :
    tr.Fall.getD ((lvAt c i).foldsOff + j) 0 = (tr.L i).chs.getD j 0 := by
  obtain ⟨suf, hsuf⟩ := h.pre i hi
  rw [← hsuf, SpLv.wsEnd_folds, ← h.off i hi, List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by rw [SpLv.chs_length, (h.fit i hi).fold]; exact hj)]

theorem oodZ_length (F1 : Fs) (ra rb : E) {m : ℕ} (hm : 1 ≤ m) : (oodZ F1 ra rb m).length = m := by
  simp only [oodZ, List.length_cons, cRest, squeezeN_length]; omega

/-- **A level's memory facts from the buffers' words.** -/
theorem lvMemB_cont {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {i : ℕ}
    (hi : i < c.levels.length) {sqz : E} (hsq : ReadsAt rd sqz (sqzC c tr i)) :
    LvMemB rd P c i (lvAt c i) (tr.L i) sqz := by
  have hn := hF.n2
  have hst := hF.lv i hi
  obtain ⟨R, d, hOk⟩ := h.ok i hi
  have hfit := h.fit i hi
  have hnf : ∀ h' : i ≠ c.yrLevel, i + 1 < c.levels.length := fun h' ↦ by have := hF.yr; omega
  refine ⟨fun j hj ↦ ?_, ?_, ?_, fun j hj t ht ↦ ?_, ?_, ?_, fun hf ↦ ?_, fun hf ↦ ?_,
    fun hf ↦ ?_, fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hle : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := hst.le
    have := readsAt_map_range hm.fch (k := (lvAt c i).foldsOff + j) (by omega)
    rwa [fall_chs h hi hj] at this
  · have := readsAt_map_range hm.roots (k := 2 * i) (by omega)
    simpa [OsTr.L] using this
  · have := readsAt_map_range hm.roots (k := 2 * i + 1) (by omega)
    simpa [OsTr.L, Nat.add_mod, Nat.add_div] using this
  · have := readsAt_map_range hsq (k := 5 * j + t) (by have := hs.sq i hi; nlinarith)
    simp only [show (5 * j + t) / 5 = j by omega, show (5 * j + t) % 5 = t by omega, hj,
      ↓reduceIte] at this
    exact this
  · have := readsAt_map_range hm.mus (k := i) hi
    simpa [OsTr.L] using this
  · have := readsAt_map_range hm.betas (k := i) hi
    simpa [OsTr.L] using this
  · have hd := hOk.digest (by cases e : (tr.L i).fin <;> simp_all [hfit.fin])
    have := readsAt_map_range hm.roots (k := 2 * (i + 1)) (by have := hnf hf; omega)
    simp only [Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at this
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, h.roots i (hnf hf), SpLv.dn, hd, Option.getD_some,
      digestScalars_digestOfScalars hd] at this
    exact this
  · have hd := hOk.digest (by cases e : (tr.L i).fin <;> simp_all [hfit.fin])
    have := readsAt_map_range hm.roots (k := 2 * (i + 1) + 1) (by have := hnf hf; omega)
    simp only [Nat.add_mod, Nat.mul_mod_right, show (0 + 1 % 2) % 2 = 1 by rfl, one_ne_zero,
      ↓reduceIte, show (2 * (i + 1) + 1) / 2 = i + 1 by omega] at this
    rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring, h.roots i (hnf hf), SpLv.dn, hd, Option.getD_some,
      digestScalars_digestOfScalars hd] at this
    exact this
  · intro k hk
    rw [oodZ_length _ _ _ (by rw [hfit.ml]; exact hst.ml1), hfit.ml] at hk
    have hc : (lvAt c i).logCols ≤ 22 := hs.cols i hi
    have := readsAt_map_range hm.oodz (k := (i + 1) * ligColsCap + k) (by
      have := hnf hf; simp only [ligColsCap]; nlinarith)
    simp only [ligColsCap] at this
    simp only [show ((i + 1) * 22 + k) / 22 = i + 1 by omega,
      show ((i + 1) * 22 + k) % 22 = k by omega, Nat.le_add_left, ↓reduceIte,
      Nat.add_sub_cancel] at this
    rw [loadHolds_mul_gen_pow, ← List.getD_eq_getElem _ 0]
    exact this
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    have := readsAt_map_range hm.ood (k := (i + 1) * oodSlots + k) (by
      have := hnf hf; simp only [oodSlots] at *; nlinarith)
    simp only [show ((i + 1) * oodSlots + k) / oodSlots = i + 1 by simp only [oodSlots]; omega,
      show ((i + 1) * oodSlots + k) % oodSlots = k by simp only [oodSlots]; omega,
      Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [loadHolds_mul_gen_pow, ← List.getD_eq_getElem _ 0]
    exact this
  · intro k hk
    have hlast : i = c.levels.length - 1 := by rw [hf, hF.yr]
    have hms : (tr.L i).ms.length = c.yrLen := by
      rw [hOk.ms (hfit.fin.mpr hf), hfit.ml]
      have := hF.last
      rw [getLastD_eq_getD _ (by intro h; rw [h] at hn; simp at hn), ← hlast] at this
      rw [this, hF.ylen]
    have := readsAt_map_range hm.fmsg (k := k) (by omega)
    have hlf : tr.Lf = tr.L i := by rw [h.lf, ← hlast]
    rw [← List.getD_eq_getElem _ 0, ← hlf]
    exact this

end
end LeanVM.Guest.B1.Whir
