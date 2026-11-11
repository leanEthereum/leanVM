/-
  LeanVM.Guest.B1.Whir.BrLevel

  A level of the Spec's honest trace as the guest's honest level data.
-/

module

public import LeanVM.Guest.B1.Whir.CLevels
public import LeanVM.Guest.B1.Whir.SpecTrace
public import LeanVM.Guest.B1.Whir.Glue

/-!
# A level of the trace, as the guest's data

`spDat L d wp`: the guest's data of a level `L : SpLv` of the honest trace (its words, its next
commitment's digest `d`, its row weights buffer at `wp`, its root's cells
the cap's returns, its enforced sum `opening_queries`' return). `SpLvFit`: the level's row against
the Spec's level. `lvOut_sp`: what the guest's level leaves is what the Spec's leaves: the next
sponge `L.Fend`, the glued quadratic and claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **A level's honest data**, from the trace's level `L`. -/
def spDat (L : SpLv) (d : Digest) (wp : E) : LvDat :=
  ⟨L.xf, L.ms, L.ra, L.rb, L.y, L.c0, L.c2, L.nonce, d, wp, (digestHalves L.root).1,
    (digestHalves L.root).2, L.enforced, L.ic0, L.ic2⟩

/-- The level's row against the trace's level. -/
structure SpLvFit (c : OsCfg) (lvl : ℕ) (lv : OsLv) (L : SpLv) : Prop where
  fold : L.level.fold = lv.folds
  f1 : 1 ≤ lv.folds
  ml : L.ml = lv.logCols
  nsq : L.nsq = lv.squeezes
  fin : L.fin = true ↔ lvl = c.yrLevel

theorem foldsTr_quad_len3 : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E), q.length = 3 →
    (foldsTr n F q t xs).2.2.1.length = 3
  | 0, _, _, _, _, h => by simp only [foldsTr]; exact h
  | n + 1, F, q, t, xs, _ => by
    simp only [foldsTr]
    exact foldsTr_quad_len3 n _ _ _ _ (by simp)

theorem foldsTr_quad_len : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E), 1 ≤ n →
    (foldsTr n F q t xs).2.2.1.length = 3
  | 0, _, _, _, _, h => absurd h (by omega)
  | n + 1, F, q, t, xs, _ => by
    simp only [foldsTr]
    exact foldsTr_quad_len3 n _ _ _ _ (by simp)

theorem list3 {l : List E} (h : l.length = 3) : l = [l.getD 0 0, l.getD 1 0, l.getD 2 0] := by
  match l, h with
  | [a, b, c], _ => rfl

theorem spDat_lvR {lv : OsLv} {L : SpLv} (hfold : L.level.fold = lv.folds) (d : Digest)
    (wp : E) : lvR lv (spDat L d wp) L.F L.ws.quad L.ws.target = L.tr := by
  simp only [lvR, spDat, SpLv.tr, hfold]

theorem spDat_cap {c : OsCfg} {lvl : ℕ} {lv : OsLv} {L : SpLv} (h : SpLvFit c lvl lv L)
    (d : Digest) (wp : E) :
    (⟨lvCap c lvl lv (spDat L d wp) L.F L.ws.quad L.ws.target, []⟩ : Fs) = L.F2 := by
  unfold lvCap
  by_cases hf : lvl = c.yrLevel
  · have hL : L.fin = true := h.fin.mpr hf
    simp only [hf, ↓reduceIte, capFin, spDat_lvR h.fold, SpLv.F2, hL]
    rfl
  · have hL : L.fin = false := by
      cases e : L.fin
      · rfl
      · exact absurd (h.fin.mp e) hf
    simp only [hf, ↓reduceIte, capNon, spDat_lvR h.fold, SpLv.F2, hL, h.ml]
    rfl

theorem spDat_lam {c : OsCfg} {lvl : ℕ} {lv : OsLv} {L : SpLv} (h : SpLvFit c lvl lv L)
    (d : Digest) (wp : E) : lvLam c lvl lv (spDat L d wp) L.F L.ws.quad L.ws.target = L.lam := by
  unfold lvLam lamOf SpLv.lam sqLast
  rw [← spDat_cap h d wp, (squeezeN_sqCaps _ _).1, h.nsq]

/-- **What the guest's level leaves is the trace's.** -/
theorem lvOut_sp {c : OsCfg} {lvl : ℕ} {lv : OsLv} {L : SpLv} (h : SpLvFit c lvl lv L)
    (d : Digest) (wp : E) :
    lvOut c lvl lv (spDat L d wp) L.F L.ws.quad L.ws.target =
      (L.Fend, L.wsEnd.quad, L.wsEnd.target) := by
  have hq3 : L.tr.2.2.1.length = 3 := by
    rw [SpLv.tr, h.fold]; exact foldsTr_quad_len _ _ _ _ _ h.f1
  have hQ := list3 hq3
  have hlam := spDat_lam h d wp
  have hFq : lvFq c lvl lv (spDat L d wp) L.F L.ws.quad L.ws.target = (L.F2.squeezeN L.nsq).2 := by
    unfold lvFq sqLast; rw [← spDat_cap h d wp, (squeezeN_sqCaps _ _).1, h.nsq]
  unfold lvOut
  rw [hlam, hFq, spDat_lvR h.fold]
  by_cases hf : lvl = c.yrLevel
  · have hL : L.fin = true := h.fin.mpr hf
    simp only [hf, ↓reduceIte]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [SpLv.wsEnd, SpLv.pending, hL, ↓reduceIte, List.nil_append, glue_one, SpLv.ws1]
      rw [hQ]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.getD_cons_zero,
        List.getD_cons_succ, spDat]
      refine List.cons_eq_cons.mpr ⟨by ring, List.cons_eq_cons.mpr ⟨by ring,
        List.cons_eq_cons.mpr ⟨by ring, rfl⟩⟩⟩
    · simp only [SpLv.wsEnd, SpLv.pending, hL, ↓reduceIte, List.nil_append, glue_one, SpLv.ws1,
        spDat]
      ring
  · have hL : L.fin = false := by
      cases e : L.fin
      · rfl
      · exact absurd (h.fin.mp e) hf
    simp only [hf, ↓reduceIte]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [SpLv.wsEnd, SpLv.pending, hL, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.nil_append, glue_two, SpLv.ws1]
      rw [hQ]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.getD_cons_zero,
        List.getD_cons_succ, spDat]
      refine List.cons_eq_cons.mpr ⟨by ring, List.cons_eq_cons.mpr ⟨by ring,
        List.cons_eq_cons.mpr ⟨by ring, rfl⟩⟩⟩
    · simp only [SpLv.wsEnd, SpLv.pending, hL, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.nil_append, glue_two, SpLv.ws1, spDat]
      ring

end
end LeanVM.Guest.B1.Whir
