/-
  LeanVM.Guest.B1.Whir.CHonMem

  Reading the honest buffers back from a memory holding them.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Whir.CHonStatic

/-!
# The honest buffers, read back

On a memory holding the honest buffers at the base `b` (`OsMemF rd c b h.own`): `OsHD.load`, a
word of buffer `j` (`ownW j`) within its size; `OsHD.reads`, the whole of it when it fits. The
buffers' sizes (`HonStatic`) and words (`ownW_*`) at the indices the body reads: the head's
thirteen, each level's two (`13 + 2l`, `14 + 2l`), the finish's seven (`13 + 2n + k`) and the
residual chains (`20 + 2n + l`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ}

/-- **A word of buffer `j`**, within its size. -/
theorem load (hm : OsMemF rd h.c b h.own) {j e : ℕ} (hj : j < (osSizesF h.c).length)
    (hne : j ≠ osIxQbp) (he : e < (osSizesF h.c).getD j 0) :
    LoadHolds rd (osPtrF h.c b j) e ((h.ownW j).getD e 0) := by
  have hr := hm j hj hne
  rw [h.own_getD hj] at hr
  have := readsAt_getD' hr (by simp only [ownAt, fitTo_length]; exact he)
  rwa [ownAt, fitTo_getD he] at this

/-- **Buffer `j`'s words**, when they fit its size. -/
theorem reads (hm : OsMemF rd h.c b h.own) {j : ℕ} (hj : j < (osSizesF h.c).length)
    (hne : j ≠ osIxQbp) (hl : (h.ownW j).length ≤ (osSizesF h.c).getD j 0) :
    ReadsAt rd (osPtrF h.c b j) (h.ownW j) := fun e he ↦ by
  have := h.load hm hj hne (e := e) (by omega)
  rwa [List.getD_eq_getElem _ _ he] at this

/-- A word of buffer `j` through its pointer shifted by `o`. -/
theorem loadOff (hm : OsMemF rd h.c b h.own) {j o e : ℕ} (hj : j < (osSizesF h.c).length)
    (hne : j ≠ osIxQbp) (he : o + e < (osSizesF h.c).getD j 0) :
    LoadHolds rd (osPtrF h.c b j * gen ^ o) e ((h.ownW j).getD (o + e) 0) := by
  rw [loadHolds_mul_gen_pow]
  exact h.load hm hj hne he

/-! ## The buffers' words at their indices -/

theorem ownW_caps : h.ownW 0 = h.capsC := by simp [ownW]
theorem ownW_flags : h.ownW 1 = h.flagsC := by simp [ownW]
theorem ownW_fmsg : h.ownW 2 = h.fmsgC := by simp [ownW]
theorem ownW_roots : h.ownW 3 = h.rootsC := by simp [ownW]
theorem ownW_fch : h.ownW 4 = h.fchC := by simp [ownW]
theorem ownW_coefs : h.ownW 5 = h.coefsC := by simp [ownW]
theorem ownW_betas : h.ownW 6 = h.betasC := by simp [ownW]
theorem ownW_mus : h.ownW 7 = h.musC := by simp [ownW]
theorem ownW_hs : h.ownW 8 = h.hsC := by simp [ownW]
theorem ownW_oodz : h.ownW 9 = h.oodzC := by simp [ownW]
theorem ownW_ood : h.ownW 10 = h.oodC := by simp [ownW]
theorem ownW_qpos : h.ownW 11 = h.qposC := by simp [ownW]

theorem ownW_lv0 {l : ℕ} (hl : l < h.c.levels.length) :
    h.ownW (13 + 2 * l) = if l = h.c.yrLevel then h.sqzC l else h.sentC l := by
  have e1 : (13 + 2 * l - 13) / 2 = l := by omega
  have e2 : (13 + 2 * l - 13) % 2 = 0 := by omega
  simp only [ownW, show ¬ (13 + 2 * l < 13) by omega, show 13 + 2 * l < 13 + 2 * h.c.levels.length by omega,
    ↓reduceIte, e1, e2]

theorem ownW_lv1 {l : ℕ} (hl : l < h.c.levels.length) :
    h.ownW (14 + 2 * l) = if l = h.c.yrLevel then h.hsFC else h.sqzC l := by
  have e1 : (14 + 2 * l - 13) / 2 = l := by omega
  have e2 : (14 + 2 * l - 13) % 2 = 1 := by omega
  simp only [ownW, show ¬ (14 + 2 * l < 13) by omega, show 14 + 2 * l < 13 + 2 * h.c.levels.length by omega,
    ↓reduceIte, e1, e2, one_ne_zero]

theorem ownW_fin {k : ℕ} (hk : k < 7) :
    h.ownW (13 + 2 * h.c.levels.length + k) =
      [h.T, finPtC h.c h.G h.T, finPt1C h.c h.G h.T, finBdC h.c h.G h.T h.recs, finLsC h.c h.G h.T h.recs,
        finLaC h.c h.G h.T h.recs, finIchC h.c h.G h.T h.recs h.li h.tr.2.1].getD k [] := by
  simp only [ownW, show ¬ (13 + 2 * h.c.levels.length + k < 13) by omega,
    show ¬ (13 + 2 * h.c.levels.length + k < 13 + 2 * h.c.levels.length) by omega,
    show 13 + 2 * h.c.levels.length + k < 20 + 2 * h.c.levels.length by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem ownW_rc (l : ℕ) :
    h.ownW (20 + 2 * h.c.levels.length + l) = finRcC h.c h.G h.T h.recs h.li l := by
  simp only [ownW, show ¬ (20 + 2 * h.c.levels.length + l < 13) by omega,
    show ¬ (20 + 2 * h.c.levels.length + l < 13 + 2 * h.c.levels.length) by omega,
    show ¬ (20 + 2 * h.c.levels.length + l < 20 + 2 * h.c.levels.length) by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

end OsHD

/-! ## The sizes -/

namespace HonStatic

variable {c : OsCfg} (hS : HonStatic c)
include hS

theorem n2 : 2 ≤ c.levels.length := hS.1
theorem yr : c.yrLevel + 1 = c.levels.length := hS.2.1
theorem ylog : c.yrLog ≤ yrLogCap := hS.2.2.1

theorem caps : ∀ l < c.levels.length, 4 * (osLvAt c l).capOff + 2 ^ ((osLvAt c l).capDepth + 2) ≤
    (if l + 1 < c.levels.length then 4 * (osLvAt c (l + 1)).capOff else 4 * c.capLen) := hS.2.2.2.1

theorem flags : ∀ l < c.levels.length, (osLvAt c l).capOff + 2 ^ (osLvAt c l).capDepth ≤
    (if l + 1 < c.levels.length then (osLvAt c (l + 1)).capOff else c.capLen) := hS.2.2.2.2.1

theorem pos : ∀ l < c.levels.length, (osLvAt c l).posOff + (osLvAt c l).squeezes * sqPer (osLvAt c l) ≤
    (if l + 1 < c.levels.length then (osLvAt c (l + 1)).posOff else c.posLen) := hS.2.2.2.2.2.1

theorem sq {l : ℕ} (hl : l < c.levels.length) : (osLvAt c l).squeezes ≤ c.maxSq ∧ 1 ≤ sqPer (osLvAt c l) :=
  hS.2.2.2.2.2.2.1 l hl

theorem mid {l : ℕ} (hl : l < c.yrLevel) :
    (osLvAt c l).logCols ≤ ligColsCap ∧ (osLvAt c l).folds ≤ hsStride := hS.2.2.2.2.2.2.2.1 l hl

theorem fo0 : (osLvAt c 0).foldsOff = 0 := hS.2.2.2.2.2.2.2.2.1

theorem fo {l : ℕ} (hl : l + 1 < c.levels.length) :
    (osLvAt c (l + 1)).foldsOff = (osLvAt c l).foldsOff + (osLvAt c l).folds :=
  hS.2.2.2.2.2.2.2.2.2.1 l (by have := hS.2.1; omega)

theorem foT : (osLvAt c c.yrLevel).foldsOff + (osLvAt c c.yrLevel).folds = c.nFolds :=
  hS.2.2.2.2.2.2.2.2.2.2.1

theorem len : (osSizesF c).length = 20 + 2 * c.levels.length + c.yrLevel :=
  hS.2.2.2.2.2.2.2.2.2.2.2.1

theorem head {j : ℕ} (hj : j < 13) : (osSizesF c).getD j 0 = (headSizes c).getD j 0 :=
  hS.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj

theorem lv0 {l : ℕ} (hl : l < c.levels.length) : (osSizesF c).getD (13 + 2 * l) 0 =
    (if l = c.yrLevel then (c.maxSq + 1) * 5 else 2 + (osLvAt c l).folds) :=
  (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l hl).1

theorem lv1 {l : ℕ} (hl : l < c.levels.length) : (osSizesF c).getD (14 + 2 * l) 0 =
    (if l = c.yrLevel then c.yrLen + (osLvAt c l).folds else (c.maxSq + 1) * 5) :=
  (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l hl).2

theorem fin {k : ℕ} (hk : k < 7) : (osSizesF c).getD (13 + 2 * c.levels.length + k) 0 =
    [yrLogCap, pointCap, pointCap, c.levels.length * ligColsCap, c.levels.length, c.levels.length,
      2 * c.levels.length].getD k 0 :=
  hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk

theorem rc {l : ℕ} (hl : l < c.yrLevel) :
    (osSizesF c).getD (20 + 2 * c.levels.length + l) 0 = 2 * ((osLvAt c l).queries / resBatch + 1) :=
  hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 l hl

/-- The head's buffers' indices are buffers. -/
theorem headLt {j : ℕ} (hj : j < 13) : j < (osSizesF c).length := by rw [hS.len]; omega

theorem lvLt {l : ℕ} (hl : l < c.levels.length) :
    13 + 2 * l < (osSizesF c).length ∧ 14 + 2 * l < (osSizesF c).length := by
  rw [hS.len]; omega

theorem finLt {k : ℕ} (hk : k < 7) : 13 + 2 * c.levels.length + k < (osSizesF c).length := by
  rw [hS.len]; omega

theorem rcLt {l : ℕ} (hl : l < c.yrLevel) : 20 + 2 * c.levels.length + l < (osSizesF c).length := by
  rw [hS.len]; omega

end HonStatic

end
end LeanVM.Guest.B1.Whir
