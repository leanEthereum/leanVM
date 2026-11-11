/-
  LeanVM.Guest.B1.Whir.BrCaps

  The honest caps, flags, row weights and final message in memory, and the meanings of the
  callees that read them.
-/

module

public import LeanVM.Guest.B1.Whir.BrBody

/-!
# The callees reading the caller's buffers, honestly

* `capsL`, `flagsL`: level `i`'s honest cap cells and flags, the buffers `level_queries` hints;
  `caps_get`, `flags_get` read them.
* `cap_meaning_at`: `verify_merkle_cap`'s meaning on them, its returns the level's root's cells.
* `rw_meaning_at`: `opening_row_weights`' meaning on the fold challenges and the level's row
  weights.
* `ffm_meaning_at`: `fold_final_msg`'s meaning on the final message and the tail challenges.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {c : OsCfg} {tr : OsTr}

/-- Level `i`'s honest cap cells, `level_queries`' hinted `merkle_caps`. -/
noncomputable def capsL (c : OsCfg) (tr : OsTr) (i : ℕ) : List E :=
  (List.range (4 * 2 ^ (lvAt c i).capDepth)).map (capCell (tr.L i).height (SpLv.batch' (tr.L i)))

/-- Level `i`'s honest cap flags, `level_queries`' hinted `merkle_cap_active`. -/
noncomputable def flagsL (c : OsCfg) (tr : OsTr) (i : ℕ) : List E :=
  (List.range (2 ^ (lvAt c i).capDepth)).map
    (capFl (tr.L i).height (SpLv.batch' (tr.L i)) (lvAt c i).capDepth)

/-- **Level `i`'s cap cells.** -/
theorem caps_get {rd : Reader} {caps : E} {i : ℕ} (hC : ReadsAt rd caps (capsL c tr i))
    {k : ℕ} (hk : k < 2 ^ ((lvAt c i).capDepth + 2)) :
    LoadHolds rd caps k (capCell (tr.L i).height (SpLv.batch' (tr.L i)) k) :=
  readsAt_map_range hC (by rw [pow_add] at hk; omega)

/-- **Level `i`'s cap flags.** -/
theorem flags_get {rd : Reader} {flags : E} {i : ℕ} (hC : ReadsAt rd flags (flagsL c tr i))
    {k : ℕ} (hk : k < 2 ^ (lvAt c i).capDepth) :
    LoadHolds rd flags k (capFl (tr.L i).height (SpLv.batch' (tr.L i)) (lvAt c i).capDepth k) :=
  readsAt_map_range hC hk

/-- **`verify_merkle_cap`'s meaning on level `i`'s honest cap**, its returns the level's root's
cells. -/
theorem cap_meaning_at (h : TrFit c tr) {μ r : ℕ} {target : E} {S : KeccakState}
    {xs : List E} {os : List (List Opening)} {root : Digest} (hrun : TrRun c μ r target S xs os root tr)
    (hcaps : CapsAgree μ r target S xs os root) {rd : Reader} {caps flags : E} {i : ℕ}
    (hC : ReadsAt rd caps (capsL c tr i)) (hF : ReadsAt rd flags (flagsL c tr i))
    (hi : i < c.levels.length) (hcdd : (lvAt c i).capDepth ≤ (lvAt c i).depth) :
    MeaningVerifyMerkleCap (lvAt c i).capDepth rd [caps, flags]
      [(digestHalves (tr.L i).root).1, (digestHalves (tr.L i).root).2] := by
  have hil : i < tr.Ls.length := by rw [h.len]; exact hi
  obtain ⟨R, d, hOk⟩ := h.ok i hi
  have hh := hrun.height i hil
  have hb := h.lvb i hi
  have hD : (tr.L i).D = (lvAt c i).depth := by
    rw [SpLv.D, (h.fit i hi).ml, hb.depth]
  have hmem : tr.L i ∈ tr.Ls := by
    rw [OsTr.L, List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil
  refine SpLv.cap_meaning (tr.L i) hOk hh (SpLv.batchAgrees (tr.L i) hcaps (hrun.qs _ hmem))
    (by rw [hb.queries]; have := hb.q2; omega) hb.cd (by rw [hh, hD]; exact hcdd)
    (fun k _ hk ↦ caps_get hC hk) (fun k _ hk ↦ flags_get hF hk)

/-- **`opening_row_weights`' meaning on level `i`'s fold challenges and honest row weights.** -/
theorem rw_meaning_at {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {wp : E} {i : ℕ} (hi : i < c.levels.length)
    (hW : ReadsAt rd wp (wpC c tr i))
    (hil : 2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl) :
    MeaningOpeningRowWeights (lvAt c i).folds (if i = 0 then 1 else 0) rd
      [P.fch * gen ^ (lvAt c i).foldsOff, wp] [] := by
  have hcl : (tr.L i).chs.length = (lvAt c i).folds := by
    rw [SpLv.chs_length, (h.fit i hi).fold]
  have hpre : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := by
    have hp := (h.pre i hi).length_le
    rw [SpLv.wsEnd_folds, List.length_append, h.off i hi, hcl, fall_length hF h] at hp
    exact hp
  have hil1 : 2 ^ rwLo (lvAt c i).folds ≤ c.maxIl := le_trans (Nat.le_add_right _ _) hil
  refine ⟨rfl, (tr.L i).chs, hcl, fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [loadHolds_mul_gen_pow, List.getElem_eq_getD 0, ← fall_chs h hi (by omega)]
    exact fch_get hm (by omega)
  · have := readsAt_map_range hW (k := j) (by omega)
    simp only [hj, ↓reduceIte] at this
    exact this
  · have := readsAt_map_range hW (k := 2 ^ rwLo (lvAt c i).folds + j) (by omega)
    simp only [show ¬ 2 ^ rwLo (lvAt c i).folds + j < 2 ^ rwLo (lvAt c i).folds by omega,
      show 2 ^ rwLo (lvAt c i).folds + j < 2 ^ rwLo (lvAt c i).folds +
        2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) by omega, ↓reduceIte,
      Nat.add_sub_cancel_left] at this
    exact this

/-- **`fold_final_msg`'s meaning on the final message and the tail challenges.** -/
theorem ffm_meaning_at {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {T : E}
    (hT : ReadsAt rd T (tailC tr.Lf tr.xsR)) :
    MeaningFoldFinalMsg c.yrLog rd [P.fmsg, T] [multilinearEval tr.Lf.ms tr.Tc] := by
  have hn := hF.n2
  have hi : c.levels.length - 1 < c.levels.length := by omega
  have hml : tr.Lf.ml = c.yrLog := by
    rw [h.lf, (h.fit _ hi).ml]
    have := hF.last
    rwa [getLastD_eq_getD _ (by intro h; rw [h] at hn; simp at hn)] at this
  have hfin : tr.Lf.fin = true := by
    rw [h.lf, (h.fit _ hi).fin, hF.yr]
  obtain ⟨R, d, hOk⟩ := h.ok _ hi
  rw [← h.lf] at hOk
  have hms : tr.Lf.ms.length = c.yrLen := by rw [hOk.ms hfin, hml, hF.ylen]
  refine ⟨tr.Lf.ms, tr.Tc, by rw [hms, hF.ylen], h.tcLen, fun k hk ↦ ?_, fun k hk ↦ ?_, rfl⟩
  · have := readsAt_map_range hm.fmsg (k := k) (by omega)
    rw [List.getElem_eq_getD 0]; exact this
  · rw [List.getElem_eq_getD 0]
    exact tailC_get h hs hT (by rw [← h.tcLen]; exact hk)

end
end LeanVM.Guest.B1.Whir
