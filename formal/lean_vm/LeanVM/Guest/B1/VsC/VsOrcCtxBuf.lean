/-
  LeanVM.Guest.B1.VsC.VsOrcCtxBuf

  The fixed own buffers `.n 6 … .n 23` of an honest context as `BufAt`s, at every phase boundary.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPhEnd
public import LeanVM.Guest.B1.VsC.VsOrcMem
public import LeanVM.Guest.B1.VsC.VsOrcBuf
public import LeanVM.Guest.B1.VsC.VsOrcExport

/-!
# The own buffers at a boundary

On an honest context `x` and a state whose memories hold `x.Wo` (`Bnd.hO`): buffer `j < 18` (`.n (j + 6)`) points at `x.base j`
(**`VsCtx.ptrL`**), its words `x.Lw.getD j []` (`bw`'s, the overlay's for `.n 19`) are read on `x.rd0` and on every
memory with the state's `O` (`Bnd.hO`), and its cells are in `x.OwnB`: **`VsCtx.bufAtL`**, a `BufAt` for every
cell predicate containing `OwnB` and every length up to its size.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

theorem vsAllocIdx_fixed {j : ℕ} (hj : j < 18) : vsAllocIdx.getD j 0 = j + 6 := by
  interval_cases j <;> rfl

namespace VsCtx

variable {x : VsCtx}

/-- **The fixed buffers' pointers.** -/
theorem ptrL (h : x.Hon) {j : ℕ} (hj : j < 18) : vsVal x.rd0 x.w x.args (.n (j + 6)) = ptrAt (x.base j) := by
  have ha : x.args.length = 6 := rfl
  rw [vsVal_fixed ha ⟨by omega, by omega⟩, base, vsBases_getD x.cur x.p (by omega), ← vsW_ptr (rd1 := x.rd1)
    (args := x.args) (ret := x.ret) ha h.hret (by omega : j < 24), vsAllocIdx_fixed hj]
  rfl

theorem mem_Wo (h : x.Hon) {j : ℕ} (hj : j < 24) : (x.base j, x.Lw.getD j []) ∈ x.Wo := by
  have hbl : (bases x.cur (vsAllocSz x.p)).length = 24 := by rw [bases_length, vsAllocSz_length]
  have hLl : x.Lw.length = 24 := by rw [Lw, List.length_set, bw_length h]
  have hWo : x.Wo = (bases x.cur (vsAllocSz x.p)).zip x.Lw := rfl
  rw [hWo, List.mem_iff_getElem]
  refine ⟨j, by rw [List.length_zip, hbl, hLl]; omega, ?_⟩
  rw [List.getElem_zip, base, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem Lw_length (h : x.Hon) {j : ℕ} (hj : j < 24) : (x.Lw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
  have hLl : x.Lw.length = 24 := by rw [Lw, List.length_set, bw_length h]
  rw [← Lw_sizes h, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
    List.getElem_map]

/-- **A fixed own buffer at a boundary.** -/
theorem bufAtL (h : x.Hon) {st : St} (hO' : ∀ rd, st.O rd → HoldsWords rd x.Wo) {j : ℕ} (hj : j < 18) {C : ℕ → Prop}
    (hC : ∀ i, x.OwnB i → C i) {n : ℕ} (hn : n ≤ (vsAllocSz x.p).getD j 0) :
    BufAt x.rd0 (vsVal x.rd0 x.w x.args) x.Pre st.O C (j + 6) (x.base j) n (x.Lw.getD j []) := by
  have hm := mem_Wo h (by omega : j < 24)
  obtain ⟨hlo, hhi⟩ := base_lt h j (by omega)
  exact ⟨ptrL h hj, by rw [Lw_length h (by omega)]; exact hn, holdsWords_rd0 h _ hm,
    fun rd _ ho => hO' rd ho _ hm, fun i hi => hC _ ⟨by omega, by omega⟩⟩

/-- **The export on an honest context**: from the fresh claim's point and values being `r_pt`'s and `splitv`'s
first words (the export's converse). -/
theorem phExportOk (h : x.Hon) {st : St} (hO' : ∀ rd, st.O rd → HoldsWords rd x.Wo) {al : String → Bool} {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {K : St → Prop}
    (hpt : x.c.freshClaim.point = (x.bw.getD 6 []).take 19)
    (hval : x.c.freshClaim.values = (x.bw.getD 8 []).take 36) (hK : K st) :
    PhExportOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st K := by
  have ha : x.args.length = 6 := rfl
  have B6 := bufAtL h hO' (j := 6) (by omega) hO (n := 24) le_rfl
  have B8 := bufAtL h hO' (j := 8) (by omega) hO (n := 36) le_rfl
  simp only [Lw_getD h (show 6 < 24 by omega), Lw_getD h (show 8 < 24 by omega), show (6 : ℕ) ≠ 13 by omega,
    show (8 : ℕ) ≠ 13 by omega, ↓reduceIte] at B6 B8
  have e6 : x.base 6 = vsBase x.cur x.p 6 := vsBases_getD x.cur x.p (by omega)
  have e8 : x.base 8 = vsBase x.cur x.p 8 := vsBases_getD x.cur x.p (by omega)
  rw [e6] at B6
  rw [e8] at B8
  exact phExportOk_honest (fun i h1 h2 => hO i ⟨h1, h2⟩)
    (vsW_ptr (rd1 := x.rd1) (args := x.args) (ret := x.ret) ha h.hret (j := 6) (by omega))
    (vsW_ptr (rd1 := x.rd1) (args := x.args) (ret := x.ret) ha h.hret (j := 8) (by omega))
    (by have := B6.len; omega) B8.len ⟨B6.r0, B6.rO⟩ ⟨B8.r0, B8.rO⟩ (pre_rd0 h).2 hpt hval hK

end VsCtx

end
end LeanVM.Guest.B1.VsC
