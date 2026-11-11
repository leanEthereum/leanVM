/-
  LeanVM.Guest.B1.Whir.BrLevelH

  A level of the Spec's honest trace gives the guest's level hypotheses.
-/

module

public import LeanVM.Guest.B1.Whir.BrLevel
public import LeanVM.Guest.B1.Whir.SpecCaps

/-!
# A level's hypotheses from the trace

`LvMem`: what memory holds for a level of the trace `L` at the fixed buffers `P` and the cursor
`cur`: its words, its fold challenges, its root's cells, `μ` and its batching scalar, its next commitment's root, point and
out-of-domain words (not the last level), the final message (the last).
`LvCallsOk`: the calls of `C` the level makes, at their honest arguments and returns (the
dispatches on the rate's selector into `level_positions`, `level_queries` and the fold rounds').
`lvH_sp`: with the trace's facts (`L.Ok`) and the configuration's (`SpLvFit`, `LvB`), they are the
level's hypotheses `LvH` at the data `spDat`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

theorem readsAt_right {rd : Reader} {p : E} {xs ys : List E} (h : ReadsAt rd p (xs ++ ys)) :
    ReadsAt rd (p * gen ^ xs.length) ys := fun k hk ↦ by
  have := h (xs.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [loadHolds_mul_gen_pow] using this

theorem readsAt_get {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem readsAt_off {rd : Reader} {p : E} {o : ℕ} {xs : List E} (h : ReadsAt rd (p * gen ^ o) xs)
    {k : ℕ} (hk : k < xs.length) : LoadHolds rd p (o + k) (xs.getD k 0) :=
  (loadHolds_mul_gen_pow rd p o k _).mp (readsAt_get h hk)

/-- What memory holds for a level of the trace. -/
structure LvMem (rd : Reader) (P : OsPtrs) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (L : SpLv)
    (cur : E) : Prop where
  words : ReadsAt rd cur L.words
  fch : ∀ j < lv.folds, LoadHolds rd P.fch (lv.foldsOff + j) (L.chs.getD j 0)
  r0 : LoadHolds rd P.roots (2 * lvl) (digestHalves L.root).1
  r1 : LoadHolds rd P.roots (2 * lvl + 1) (digestHalves L.root).2
  mu : LoadHolds rd P.mus lvl L.lam⁻¹
  beta : LoadHolds rd P.betas lvl
    ((if lvl = c.yrLevel then L.lam else L.lam * L.lam) * L.lam ^ lv.queries)
  r0' : lvl ≠ c.yrLevel → LoadHolds rd P.roots (2 * lvl + 2) L.ra
  r1' : lvl ≠ c.yrLevel → LoadHolds rd P.roots (2 * lvl + 3) L.rb
  oodz : lvl ≠ c.yrLevel →
    ReadsAt rd (P.oodz * gen ^ ((lvl + 1) * ligColsCap)) (oodZ L.F1 L.ra L.rb L.ml)
  ood : lvl ≠ c.yrLevel →
    ReadsAt rd (P.ood * gen ^ ((lvl + 1) * oodSlots)) [L.lam, L.y, L.c0, L.c2]
  fmsg : lvl = c.yrLevel → ReadsAt rd P.fmsg L.ms

/-- The calls of `C` a level makes, at their honest arguments and returns, at the rate's
selector `R`. -/
structure LvCallsOk (C : CallRel) (rd : Reader) (P : OsPtrs) (R : E) (c : OsCfg) (lvl : ℕ)
    (lv : OsLv) (L : SpLv) (wp : E) : Prop where
  fold : FoldCallC C rd
  can : ∀ args rets, MeaningAssertCanonical args rets → C "assert_canonical" args rets
  ood : lvl ≠ c.yrLevel → ∀ args rets, MeaningOpeningOodPoint lv.logCols rd args rets →
    C ("opening_ood_point__L" ++ natStr lv.logCols) args rets
  grind : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
    C ("grind_check__L" ++ natStr lv.grind) args rets
  fm : lvl = c.yrLevel → ∀ args rets, MeaningOpeningFinalMessage c.yrLen rd args rets →
    args.getD 8 0 = P.fmsg →
    C ("opening_final_message__L" ++ natStr c.yrLen) args rets
  pos : DispC C rd R ((c.lvAt lvl).map osPositionsName)
    (L.F2.cap ++ [P.qpos * gen ^ lv.posOff, P.qbp * gen ^ lv.posOff, P.win])
    (sqLast lv L.F2.cap)
  rw : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
    [P.fch * gen ^ lv.foldsOff, wp] []
  queries : DispC C rd R ((c.lvAt lvl).map (osQueriesName lvl))
    [L.lam, P.qbp * gen ^ lv.posOff, wp]
    [(digestHalves L.root).1, (digestHalves L.root).2, L.enforced, L.lam ^ lv.queries]

/-- **A level of the trace gives the level's hypotheses.** -/
theorem lvH_sp {C : CallRel} {rd : Reader} {P : OsPtrs} {Rs : E} {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    {L : SpLv} {R : List (Digest × ℕ × ℕ)} {d d' : Digest} {wp cur : E}
    (h : SpLvFit c lvl lv L) (hb : LvB c lvl lv L.level lv.logCols)
    (hlvl : lvl ≠ c.yrLevel → (lvl + 1) * ligColsCap < u128Bound)
    (hyl : lvl = c.yrLevel → 2 ^ lv.logCols = c.yrLen)
    (hOk : L.Ok R d') (hdd : L.fin = false → digestFromHalves (L.ra, L.rb) = some d)
    (hm : LvMem rd P c lvl lv L cur) (hc : LvCallsOk C rd P Rs c lvl lv L wp) :
    LvH C rd P Rs c lvl lv (spDat L d wp) L.F L.ws.quad L.ws.target cur := by
  have hR := spDat_lvR h.fold d wp
  have hcap := spDat_cap h d wp
  have hlam := spDat_lam h d wp
  have hxl : L.xf.length = 2 * lv.folds := by rw [hOk.xf, h.fold]
  have hst : ∀ j, j < lv.folds → LoadHolds rd P.fch (lv.foldsOff + j)
      ((lvR lv (spDat L d wp) L.F L.ws.quad L.ws.target).2.1.getD j 0) := fun j hj ↦ by
    rw [hR]; exact hm.fch j hj
  have hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound := ⟨hb.bounds.1, hb.bounds.2.1⟩
  unfold LvH
  by_cases hf : lvl = c.yrLevel
  · have hL : L.fin = true := h.fin.mpr hf
    have hc' : (lvl = c.yrLevel) = True := eq_true hf
    simp only [hc', ↓reduceIte]
    have hcapF : capFin lv (spDat L d wp) L.F L.ws.quad L.ws.target = L.F2.cap := by
      have := congrArg Fs.cap hcap; unfold lvCap at this; simpa [hf] using this
    have hlamF : lamOf lv (capFin lv (spDat L d wp) L.F L.ws.quad L.ws.target) = L.lam := by
      have := hlam; unfold lvLam lvCap at this; simpa [hf] using this
    have hmsl : L.ms.length = c.yrLen := by rw [hOk.ms hL, h.ml, hyl hf]
    have hw : L.words = L.xf ++ (L.ms ++ [L.nonce]) ++ [L.ic0, L.ic2] := by
      simp only [SpLv.words, hL, ↓reduceIte]
    have hwr := hm.words
    rw [hw] at hwr
    refine ⟨hf, hc.fold, hc.fm hf, hc.grind, hxl, readsAt_left (readsAt_left hwr), hst, hmsl,
      ?_, hm.fmsg hf, ?_, by rw [hcapF]; exact hc.pos, by rw [hlamF]; exact hOk.lam,
      by rw [hlamF]; exact hm.mu, hbo, hc.rw, by rw [hlamF]; exact hc.queries, hm.r0, hm.r1, ?_, ?_⟩
    · have := readsAt_right (readsAt_left hwr); rwa [hxl] at this
    · rw [hR]; have := hOk.powFin hL; exact this
    · have := readsAt_right hwr
      simp only [List.length_append, List.length_cons, List.length_nil, hxl, hmsl] at this
      simpa [spDat, Nat.add_assoc] using this
    · rw [hlamF]; have := hm.beta; simpa [hf] using this
  · have hL : L.fin = false := by
      cases e : L.fin
      · rfl
      · exact absurd (h.fin.mp e) hf
    have hc' : (lvl = c.yrLevel) = False := eq_false hf
    simp only [hc', ↓reduceIte]
    have hcapN : capNon lv (spDat L d wp) L.F L.ws.quad L.ws.target = L.F2.cap := by
      have := congrArg Fs.cap hcap; unfold lvCap at this; simpa [hf] using this
    have hlamN : lamOf lv (capNon lv (spDat L d wp) L.F L.ws.quad L.ws.target) = L.lam := by
      have := hlam; unfold lvLam lvCap at this; simpa [hf] using this
    have hw : L.words = L.xf ++ [L.ra, L.rb, L.y, L.c0, L.c2, L.nonce] ++ [L.ic0, L.ic2] := by
      simp only [SpLv.words, hL, Bool.false_eq_true, ↓reduceIte]
    have hwr := hm.words
    rw [hw] at hwr
    have hood := hm.ood hf
    refine ⟨hf, h.f1, hc.fold, hc.can, hc.ood hf, hc.grind, hlvl hf, hxl,
      readsAt_left (readsAt_left hwr), hst,
      (digestScalars_digestOfScalars (hdd hL)).symm, ?_, hm.r0' hf, hm.r1' hf, ?_,
      readsAt_off hood (k := 1) (by simp), readsAt_off hood (k := 2) (by simp),
      readsAt_off hood (k := 3) (by simp), ?_, by rw [hcapN]; exact hc.pos,
      by rw [hlamN]; exact hOk.lam, by rw [hlamN]; exact hm.mu, hbo,
      hc.rw, by rw [hlamN]; exact hc.queries, hm.r0, hm.r1, ?_, ?_, ?_⟩
    · have := readsAt_right (readsAt_left hwr); rwa [hxl] at this
    · rw [hR, ← h.ml]; exact hm.oodz hf
    · rw [hR, ← h.ml]; exact hOk.powNf hL
    · have := readsAt_right hwr
      simp only [List.length_append, List.length_cons, List.length_nil, hxl] at this
      simpa [spDat] using this
    · rw [hlamN]; have := readsAt_off hood (k := 0) (by simp); simpa using this
    · rw [hlamN]; have := hm.beta; simpa [hf] using this

end
end LeanVM.Guest.B1.Whir
