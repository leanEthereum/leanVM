/-
  LeanVM.Guest.B1.Whir.CHonMem

  Reading the honest buffers back from a memory holding them.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Whir.CHonStatic
public import LeanVM.Guest.B1.Place.OsProtoSpec

/-!
# The honest buffers, read back

On a memory holding the honest buffers at the base `b` (`OsMemA rd c b h.own`): `OsHD.load`, a
word of buffer `j` (`ownW j`) within its size; `OsHD.reads`, the whole of it when it fits. The
buffers' sizes (`HonStatic`) and words (`ownW_*`) at the indices the body reads: the head's
eleven, each non-final level's message (`11 + l`), the final lane (`11 + y`) and the finish's
seven (`12 + y + k`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ}

/-- **A word of buffer `j`**, within its size. -/
theorem load (hm : OsMemA rd h.c b h.own) {j e : ℕ} (hj : j < (osSizesL h.c).length)
    (hne : j ≠ osIxQbpA) (he : e < (osSizesL h.c).getD j 0) :
    LoadHolds rd (osPtrA h.c b j) e ((h.ownW j).getD e 0) := by
  have hr : ReadsAt rd (osPtrA h.c b j) (h.own.getD j []) := hm j hj hne
  rw [h.own_getD hj] at hr
  have := readsAt_getD' hr (by simp only [ownAt, fitTo_length]; exact he)
  rwa [ownAt, fitTo_getD he] at this

/-- **Buffer `j`'s words**, when they fit its size. -/
theorem reads (hm : OsMemA rd h.c b h.own) {j : ℕ} (hj : j < (osSizesL h.c).length)
    (hne : j ≠ osIxQbpA) (hl : (h.ownW j).length ≤ (osSizesL h.c).getD j 0) :
    ReadsAt rd (osPtrA h.c b j) (h.ownW j) := fun e he ↦ by
  have := h.load hm hj hne (e := e) (by omega)
  rwa [List.getD_eq_getElem _ _ he] at this

/-- A word of buffer `j` through its pointer shifted by `o`. -/
theorem loadOff (hm : OsMemA rd h.c b h.own) {j o e : ℕ} (hj : j < (osSizesL h.c).length)
    (hne : j ≠ osIxQbpA) (he : o + e < (osSizesL h.c).getD j 0) :
    LoadHolds rd (osPtrA h.c b j * gen ^ o) e ((h.ownW j).getD (o + e) 0) := by
  rw [loadHolds_mul_gen_pow]
  exact h.load hm hj hne he

/-! ## The buffers' words at their indices -/

theorem ownW_fmsg : h.ownW 0 = h.fmsgC := by simp [ownW]
theorem ownW_roots : h.ownW 1 = h.rootsC := by simp [ownW]
theorem ownW_fch : h.ownW 2 = h.fchC := by simp [ownW]
theorem ownW_coefs : h.ownW 3 = h.coefsC := by simp [ownW]
theorem ownW_betas : h.ownW 4 = h.betasC := by simp [ownW]
theorem ownW_mus : h.ownW 5 = h.musC := by simp [ownW]
theorem ownW_hs : h.ownW 6 = h.hsC := by simp [ownW]
theorem ownW_oodz : h.ownW 7 = h.oodzC := by simp [ownW]
theorem ownW_ood : h.ownW 8 = h.oodC := by simp [ownW]
theorem ownW_qpos : h.ownW 9 = h.qposC := by simp [ownW]

theorem ownW_sent {l : ℕ} (hl : l < h.c.yrLevel) : h.ownW (11 + l) = h.sentC l := by
  simp only [ownW, show ¬ (11 + l < 11) by omega, show 11 + l < 11 + h.c.yrLevel by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem ownW_lane : h.ownW (11 + h.c.yrLevel) = h.hsFC := by
  simp only [ownW, show ¬ (11 + h.c.yrLevel < 11) by omega, lt_irrefl, ↓reduceIte]

theorem ownW_fin {k : ℕ} (hk : k < 7) :
    h.ownW (12 + h.c.yrLevel + k) =
      [h.T, finPtC h.c h.G h.T, finPt1C h.c h.G h.T, finBdC h.c h.G h.T h.recs, finLsC h.c h.G h.T h.recs,
        finLaC h.c h.G h.T h.recs, finIchC h.c h.G h.T h.recs h.li h.tr.2.1].getD k [] := by
  simp only [ownW, show ¬ (12 + h.c.yrLevel + k < 11) by omega,
    show ¬ (12 + h.c.yrLevel + k < 11 + h.c.yrLevel) by omega,
    show ¬ (12 + h.c.yrLevel + k = 11 + h.c.yrLevel) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

end OsHD

/-! ## The sizes -/

namespace HonStatic

variable {c : OsCfg} (hS : HonStatic c)
include hS

theorem n2 : 2 ≤ c.levels.length := hS.1
theorem yr : c.yrLevel + 1 = c.levels.length := hS.2.1
theorem ylog : c.yrLog ≤ yrLogCap := hS.2.2.1

theorem pos : ∀ l < c.levels.length, (c.levels.getD l default).posOff +
    (c.levels.getD l default).squeezes * sqPer (c.levels.getD l default) ≤
    (if l + 1 < c.levels.length then (c.levels.getD (l + 1) default).posOff
      else c.levels.length * ligPosCap) := hS.2.2.2.1

theorem per {l : ℕ} (hl : l < c.levels.length) : 1 ≤ sqPer (c.levels.getD l default) :=
  hS.2.2.2.2.1 l hl

theorem mid {l : ℕ} (hl : l < c.yrLevel) :
    (c.levels.getD l default).logCols ≤ ligColsCap ∧ (c.levels.getD l default).folds ≤ hsStride :=
  hS.2.2.2.2.2.1 l hl

theorem fo0 : (c.levels.getD 0 default).foldsOff = 0 := hS.2.2.2.2.2.2.1

theorem fo {l : ℕ} (hl : l + 1 < c.levels.length) :
    (c.levels.getD (l + 1) default).foldsOff =
      (c.levels.getD l default).foldsOff + (c.levels.getD l default).folds :=
  hS.2.2.2.2.2.2.2.1 l (by have := hS.2.1; omega)

theorem foT : (c.levels.getD c.yrLevel default).foldsOff + (c.levels.getD c.yrLevel default).folds =
    c.nFolds := hS.2.2.2.2.2.2.2.2.1

theorem len : (osSizesL c).length = 19 + c.yrLevel := hS.2.2.2.2.2.2.2.2.2.1

theorem head {j : ℕ} (hj : j < 11) : (osSizesL c).getD j 0 = (headSizes c).getD j 0 :=
  hS.2.2.2.2.2.2.2.2.2.2.1 j hj

theorem sent {l : ℕ} (hl : l < c.yrLevel) :
    (osSizesL c).getD (11 + l) 0 = 2 + (c.levels.getD l default).folds :=
  hS.2.2.2.2.2.2.2.2.2.2.2.1 l hl

theorem lane : (osSizesL c).getD (11 + c.yrLevel) 0 = c.yrLen + (c.levels.getD c.yrLevel default).folds :=
  hS.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fin {k : ℕ} (hk : k < 7) : (osSizesL c).getD (12 + c.yrLevel + k) 0 =
    [yrLogCap, pointCap, pointCap, c.levels.length * ligColsCap, c.levels.length, c.levels.length,
      2 * c.levels.length].getD k 0 :=
  hS.2.2.2.2.2.2.2.2.2.2.2.2.2 k hk

/-- The head's buffers' indices are buffers. -/
theorem headLt {j : ℕ} (hj : j < 11) : j < (osSizesL c).length := by rw [hS.len]; omega

theorem sentLt {l : ℕ} (hl : l ≤ c.yrLevel) : 11 + l < (osSizesL c).length := by rw [hS.len]; omega

theorem finLt {k : ℕ} (hk : k < 7) : 12 + c.yrLevel + k < (osSizesL c).length := by
  rw [hS.len]; omega

end HonStatic

end
end LeanVM.Guest.B1.Whir
