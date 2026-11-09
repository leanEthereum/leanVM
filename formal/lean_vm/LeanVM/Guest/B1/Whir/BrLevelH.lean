/-
  LeanVM.Guest.B1.Whir.BrLevelH

  A level of the Spec's honest trace gives the guest's level hypotheses.
-/

module

public import LeanVM.Guest.B1.Whir.BrLevel
public import LeanVM.Guest.B1.Whir.SpecCaps

/-!
# A level's hypotheses from the trace

`LvMem`: what memory holds for a level of the trace `L` at the fixed buffers `P`, the squeeze run's
buffer `sqz` and the cursor `cur`: its words, its fold challenges, its root's cells, the squeeze
chain's capacities, its query weights and batching scalar, its next commitment's root, point and
out-of-domain words (not the last level), the final message (the last).
`LvCallsOk`: the calls of `C` the level makes, at their honest arguments and returns.
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
    (sqz cur : E) : Prop where
  words : ReadsAt rd cur L.words
  fch : ∀ j < lv.folds, LoadHolds rd P.fch (lv.foldsOff + j) (L.chs.getD j 0)
  r0 : LoadHolds rd P.roots (2 * lvl) (digestHalves L.root).1
  r1 : LoadHolds rd P.roots (2 * lvl + 1) (digestHalves L.root).2
  rows : ∀ j ≤ lv.squeezes, ∀ i < 5, LoadHolds rd sqz (5 * j + i)
    ((L.F2.squeezeN j).2.cap.getD i 0)
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

/-- The calls of `C` a level makes, at their honest arguments and returns. -/
structure LvCallsOk (C : CallRel) (rd : Reader) (P : OsPtrs) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (L : SpLv) (sqz wp : E) : Prop where
  fold : ∀ args rets, MeaningOpeningFold rd args rets → C "opening_fold" args rets
  can : ∀ args rets, MeaningAssertCanonical args rets → C "assert_canonical" args rets
  ood : lvl ≠ c.yrLevel → ∀ args rets, MeaningOpeningOodPoint lv.logCols rd args rets →
    C ("opening_ood_point__L" ++ natStr lv.logCols) args rets
  grind : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
    C ("grind_check__L" ++ natStr lv.grind) args rets
  fm : lvl = c.yrLevel → ∀ args rets, MeaningOpeningFinalMessage c.yrLen rd args rets →
    args.getD 8 0 = P.fmsg →
    C ("opening_final_message__L" ++ natStr c.yrLen) args rets
  sq : 1 + gen ^ lv.squeezes ≠ 0 → C (c.sqLoop lvl) [1, gen ^ lv.squeezes, sqz, P.qpos, P.qbp, P.win] []
  rw : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
    [P.fch * gen ^ lv.foldsOff, wp] []
  cap : C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
    [P.caps * gen ^ (4 * lv.capOff), P.flags * gen ^ lv.capOff]
    [(digestHalves L.root).1, (digestHalves L.root).2]
  queries : C (osQueriesName lvl lv) [P.caps * gen ^ (4 * lv.capOff),
    P.flags * gen ^ lv.capOff, L.lam, L.lam ^ lv.queries, P.qbp * gen ^ lv.posOff, wp,
    gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0))] [L.enforced]

theorem sqNext_of_rows {rd : Reader} {sqz : E} {F : Fs} (hF : F.pend = []) {n : ℕ}
    (h : ∀ j ≤ n, ∀ i < 5, LoadHolds rd sqz (5 * j + i) ((F.squeezeN j).2.cap.getD i 0)) :
    ∀ j < n, SqNextMem rd sqz (gen ^ j) (F.squeezeN j).2.cap := fun j hj i hi ↦ by
  have hr := h (j + 1) (by omega) i hi
  have hp : (F.squeezeN j).2 = ⟨(F.squeezeN j).2.cap, []⟩ := fs_of_pend_nil (squeezeN_pend hF j)
  rw [squeezeN_snoc] at hr
  rw [← hp, ← pow_mul, loadHolds_mul_gen_pow, show 5 * (j + 1) + i = j * 5 + (5 + i) by ring] at *
  exact hr

/-- **A level of the trace gives the level's hypotheses.** -/
theorem lvH_sp {C : CallRel} {rd : Reader} {P : OsPtrs} {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    {L : SpLv} {R : List (Digest × ℕ × ℕ)} {d d' : Digest} {sqz wp cur : E}
    (h : SpLvFit c lvl lv L) (hb : LvB c lvl lv L.level lv.logCols)
    (hlvl : lvl ≠ c.yrLevel → (lvl + 1) * ligColsCap < u128Bound)
    (hyl : lvl = c.yrLevel → 2 ^ lv.logCols = c.yrLen)
    (hOk : L.Ok R d') (hdd : L.fin = false → digestFromHalves (L.ra, L.rb) = some d)
    (hm : LvMem rd P c lvl lv L sqz cur) (hc : LvCallsOk C rd P c lvl lv L sqz wp) :
    LvH C rd P c lvl lv (spDat L d sqz wp) L.F L.ws.quad L.ws.target cur := by
  have hR := spDat_lvR h.fold d sqz wp
  have hcap := spDat_cap h d sqz wp
  have hlam := spDat_lam h d sqz wp
  have hpend : L.F2.pend = [] := by rw [← hcap]
  have hxl : L.xf.length = 2 * lv.folds := by rw [hOk.xf, h.fold]
  have hst : ∀ j, j < lv.folds → LoadHolds rd P.fch (lv.foldsOff + j)
      ((lvR lv (spDat L d sqz wp) L.F L.ws.quad L.ws.target).2.1.getD j 0) := fun j hj ↦ by
    rw [hR]; exact hm.fch j hj
  have hrows0 : ∀ i < 5, LoadHolds rd sqz i (L.F2.cap.getD i 0) := fun i hi ↦ by
    have := hm.rows 0 (by omega) i hi; simpa [Fs.squeezeN] using this
  have hnext := sqNext_of_rows hpend (n := lv.squeezes) hm.rows
  have hIn : IsInK (1 + gen ^ lv.squeezes) := isInK_add isInK_one (gen_pow_isInK _)
  have hbo : lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧ lv.capOff < u128Bound ∧
      lv.posOff < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound := by
    obtain ⟨b1, b2, b3, b4, -, b6⟩ := hb.bounds; exact ⟨b1, b2, b3, b4, b6⟩
  unfold LvH
  by_cases hf : lvl = c.yrLevel
  · have hL : L.fin = true := h.fin.mpr hf
    have hc' : (lvl = c.yrLevel) = True := eq_true hf
    simp only [hc', ↓reduceIte]
    have hcapF : capFin lv (spDat L d sqz wp) L.F L.ws.quad L.ws.target = L.F2.cap := by
      have := congrArg Fs.cap hcap; unfold lvCap at this; simpa [hf] using this
    have hlamF : lamOf lv (capFin lv (spDat L d sqz wp) L.F L.ws.quad L.ws.target) = L.lam := by
      have := hlam; unfold lvLam lvCap at this; simpa [hf] using this
    have hmsl : L.ms.length = c.yrLen := by rw [hOk.ms hL, h.ml, hyl hf]
    have hw : L.words = L.xf ++ (L.ms ++ [L.nonce]) ++ [L.ic0, L.ic2] := by
      simp only [SpLv.words, hL, ↓reduceIte]
    have hwr := hm.words
    rw [hw] at hwr
    have hF2 : L.F2 = (⟨L.F2.cap, []⟩ : Fs) := fs_of_pend_nil hpend
    refine ⟨hf, hc.fold, hc.fm hf, hc.grind, hxl, readsAt_left (readsAt_left hwr), hst, hmsl, ?_,
      hm.fmsg hf, ?_, hb.sq0, hb.sq5, ?_, ?_, ⟨hIn, hc.sq⟩, hb.qdigits, by rw [hlamF]; exact hOk.lam,
      by rw [hlamF]; exact hm.mu, hbo, hc.rw, hc.cap, hm.r0, hm.r1, ?_, ?_, ?_⟩
    · have := readsAt_right (readsAt_left hwr); rwa [hxl] at this
    · rw [hR]; have := hOk.powFin hL; exact this
    · intro i hi; rw [hcapF]; exact hrows0 i hi
    · intro j hj; rw [hcapF, ← hF2]; exact hnext j hj
    · rw [hlamF]; exact hc.queries
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
    have hcapN : capNon lv (spDat L d sqz wp) L.F L.ws.quad L.ws.target = L.F2.cap := by
      have := congrArg Fs.cap hcap; unfold lvCap at this; simpa [hf] using this
    have hlamN : lamOf lv (capNon lv (spDat L d sqz wp) L.F L.ws.quad L.ws.target) = L.lam := by
      have := hlam; unfold lvLam lvCap at this; simpa [hf] using this
    have hw : L.words = L.xf ++ [L.ra, L.rb, L.y, L.c0, L.c2, L.nonce] ++ [L.ic0, L.ic2] := by
      simp only [SpLv.words, hL, Bool.false_eq_true, ↓reduceIte]
    have hwr := hm.words
    rw [hw] at hwr
    have hF2 : L.F2 = (⟨L.F2.cap, []⟩ : Fs) := fs_of_pend_nil hpend
    have hood := hm.ood hf
    refine ⟨hf, h.f1, hc.fold, hc.can, hc.ood hf, hc.grind, hlvl hf, hxl,
      readsAt_left (readsAt_left hwr), hst,
      (digestScalars_digestOfScalars (hdd hL)).symm, ?_, hm.r0' hf, hm.r1' hf, ?_,
      readsAt_off hood (k := 1) (by simp), readsAt_off hood (k := 2) (by simp),
      readsAt_off hood (k := 3) (by simp), ?_, hb.sq0, hb.sq5, ?_, ?_, ⟨hIn, hc.sq⟩, hb.qdigits,
      by rw [hlamN]; exact hOk.lam, by rw [hlamN]; exact hm.mu, hbo,
      hc.rw, hc.cap, hm.r0, hm.r1, ?_, ?_, ?_, ?_⟩
    · have := readsAt_right (readsAt_left hwr); rwa [hxl] at this
    · rw [hR, ← h.ml]; exact hm.oodz hf
    · rw [hR, ← h.ml]; exact hOk.powNf hL
    · intro i hi; rw [hcapN]; exact hrows0 i hi
    · intro j hj; rw [hcapN, ← hF2]; exact hnext j hj
    · rw [hlamN]; exact hc.queries
    · have := readsAt_right hwr
      simp only [List.length_append, List.length_cons, List.length_nil, hxl] at this
      simpa [spDat] using this
    · rw [hlamN]; have := readsAt_off hood (k := 0) (by simp); simpa using this
    · rw [hlamN]; have := hm.beta; simpa [hf] using this

end
end LeanVM.Guest.B1.Whir
