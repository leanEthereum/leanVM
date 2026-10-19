/-
  LeanVM.Guest.B1.Whir.OsSig

  The values `open_stacked`'s finish allocates its buffers with, from its honest values alone.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC14

/-!
# The finish's buffers (TRIAGE #36)

`osFinish_sig`: at the finish's honest values the point's pointer, the basis rows' sizes and
pointers, the inner sums' and each level's chain's, as `OsFinSig`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {σ : Val}

/-- Entry `m·l + i` of blocks of `m` words. -/
theorem os_flatten_getD_mul {f : ℕ → List E} {m : ℕ} (hf : ∀ l, (f l).length = m) :
    ∀ n l i, l < n → i < m → ((List.range n).map f).flatten.getD (m * l + i) 0 = (f l).getD i 0
  | 0, _, _, hl, _ => absurd hl (by omega)
  | n + 1, l, i, hl, hi => by
    have hlen : ((List.range n).map f).flatten.length = m * n := by
      simp only [List.length_flatten, List.map_map, Function.comp_def, hf, List.map_const', List.length_range,
        List.sum_replicate, smul_eq_mul]; ring
    rw [List.range_succ, List.map_append, List.flatten_append]
    by_cases h : l < n
    · rw [oq_getD_app_lt (by rw [hlen]; nlinarith)]
      exact os_flatten_getD_mul hf n l i h hi
    · have hl' : l = n := by omega
      subst hl'
      rw [oq_getD_app_ge (by rw [hlen]; omega), hlen, show m * l + i - m * l = i by omega]
      simp

theorem os_basisRow_k (ba bb : ℕ) (cf : ℕ × (ℕ × ℕ) × ℕ → E) :
    ∀ (items : List (ℕ × (ℕ × ℕ) × ℕ)) (k : ℕ), (osBasisRow ba bb items k).2 = k + (osBasisRowVals cf items).length
  | [], k => by simp [osBasisRow, osBasisRowVals]
  | (slot, src, inv) :: rest, k => by
    have hvs : osBasisRowVals cf ((slot, src, inv) :: rest) =
        osBasisBlkVals (cf (slot, src, inv)) inv ++ osBasisRowVals cf rest := rfl
    have hb : (osBasisBlk ba bb slot src inv k).2 = k + (osBasisBlkVals (cf (slot, src, inv)) inv).length := by
      unfold osBasisBlk osBasisBlkVals; split <;> rfl
    simp only [osBasisRow]
    rw [os_basisRow_k ba bb cf rest, hb, hvs, List.length_append]; ring

theorem os_bases_k (yrLog tch ba bb : ℕ) (cf : ℕ × (ℕ × ℕ) × ℕ → E) :
    ∀ (lvl : ℕ) (lvs : List OsLvl) (k : ℕ),
      (osBases yrLog tch ba bb lvl lvs k).2 = k + (osBasesVals yrLog tch cf lvl lvs).length
  | _, [], k => by simp [osBases, osBasesVals]
  | lvl, lv :: rest, k => by
    simp only [osBases, osBasesVals, List.length_append]
    rw [os_bases_k yrLog tch ba bb cf (lvl + 1) rest, os_basisRow_k ba bb cf]; ring

/-- The first value after the finish's basis rows. -/
def osFinBs (cfg : OsCfg) (st : OsSt) (tch : ℕ) : ℕ :=
  (osBases cfg.yrLog tch (st.k + 1 + 44) (st.k + 1 + 46) 0 cfg.levels (st.k + 1 + 47)).2

/-- The finish's buffers' sizes and pointers. -/
structure OsFinSig (σ : Val) (cfg : OsCfg) (st : OsSt) (tch : ℕ) (D : OsFinD) : Prop where
  pt : σ (.n (st.k + 1)) = D.pt
  baSz : σ (.n (st.k + 1 + 43)) = osGw (cfg.levels.length * 22)
  ba : σ (.n (st.k + 1 + 44)) = D.ba
  bbSz : σ (.n (st.k + 1 + 45)) = osGw (cfg.levels.length * 22)
  bb : σ (.n (st.k + 1 + 46)) = D.bb
  ichSz : σ (.n (osFinBs cfg st tch)) = osGw (cfg.levels.length + 1)
  ich : σ (.n (osFinBs cfg st tch + 1)) = D.ich
  resSz : ∀ l < cfg.levels.length, σ (.n (osFinBs cfg st tch + 3 + 13 * l)) = osGw (cfg.maxQ + 1)
  res : ∀ l < cfg.levels.length, σ (.n (osFinBs cfg st tch + 3 + 13 * l + 1)) = D.chv l

/-- **The finish's buffers** at its honest values. -/
theorem osFinish_sig {cfg : OsCfg} {st : OsSt} {tch : ℕ} {D : OsFinD}
    (hv : ∀ j < (osFinishVals cfg tch D).length, σ (.n (st.k + j)) = (osFinishVals cfg tch D).getD j 0) :
    OsFinSig σ cfg st tch D := by
  set n := cfg.levels.length with hn
  set PT := osPtVals D.pt D.ent
  set H4 : List E := [osGw (n * 22), D.ba, osGw (n * 22), D.bb]
  set B := osBasesVals cfg.yrLog tch D.cf 0 cfg.levels
  set I3 : List E := [osGw (n + 1), D.ich, 0]
  set R := osResidualsVals cfg.maxQ cfg.levels D.chv D.i0 D.b D.r
  have hV : osFinishVals cfg tch D = [D.yat] ++ PT ++ H4 ++ B ++ I3 ++ R ++
      (osOodWsVals cfg.yrLog D.sc D.z D.c (cfg.levels.headD default).logCols 1 cfg.levels.tail none ++
        [D.t, D.pt, D.ichN] ++ (match osFinAcc cfg D with | none => [] | some a => [D.ichN + a]) ++ [D.yat]) := by
    simp only [osFinishVals, List.append_assoc]; rfl
  rw [hV] at hv
  obtain ⟨v6, -⟩ := os_look_app hv
  obtain ⟨v5, gR⟩ := os_look_app v6
  obtain ⟨v4, gI⟩ := os_look_app v5
  obtain ⟨v3, -⟩ := os_look_app v4
  obtain ⟨v2, gH⟩ := os_look_app v3
  obtain ⟨-, gPT⟩ := os_look_app v2
  have lPT : PT.length = 43 := os_length_ptVals _ _
  have lR : R.length = 13 * n := os_length_residualsVals _ _ _ _ _ _
  have lH4 : H4.length = 4 := rfl
  have lI3 : I3.length = 3 := rfl
  simp only [List.length_append, List.length_cons, List.length_nil, lPT, lH4, lI3, Nat.zero_add] at gPT gH gI gR
  have h0 := gH 0 (by omega); have h1 := gH 1 (by omega)
  have h2 := gH 2 (by omega); have h3 := gH 3 (by omega)
  simp only [H4, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3
  have hbs : osFinBs cfg st tch = st.k + (1 + 43 + 4 + B.length) := by
    rw [osFinBs, os_bases_k _ _ _ _ D.cf]; ring
  have i0 := gI 0 (by omega); have i1 := gI 1 (by omega)
  simp only [I3, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at i0 i1
  have hR : ∀ l < n, ∀ i < 13, R.getD (13 * l + i) 0 = (osResVals cfg.maxQ (cfg.levels.getD l default).queries
      (D.chv l) (D.i0 l) (D.b l) (D.r l)).getD i 0 := fun l hl i hi =>
    os_flatten_getD_mul (f := fun lvl => osResVals cfg.maxQ (cfg.levels.getD lvl default).queries (D.chv lvl)
      (D.i0 lvl) (D.b lvl) (D.r lvl)) (m := 13) (fun _ => rfl) n l i hl hi
  refine ⟨by simpa [PT, osPtVals] using gPT 0 (by omega), by rw [← h0], by rw [← h1],
    by rw [← h2], by rw [← h3], by rw [hbs, ← i0], by rw [hbs, ← i1],
    fun l hl => ?_, fun l hl => ?_⟩
  · have := gR (13 * l + 0) (by rw [lR]; omega)
    rw [hR l hl 0 (by omega)] at this
    simp only [osResVals, List.getD_cons_zero] at this
    rw [hbs]; convert this using 3
  · have := gR (13 * l + 1) (by rw [lR]; omega)
    rw [hR l hl 1 (by omega)] at this
    simp only [osResVals, List.getD_cons_zero, List.getD_cons_succ] at this
    rw [hbs]; convert this using 3

end
end LeanVM.Guest.B1
