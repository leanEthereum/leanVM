/-
  LeanVM.Guest.B1.Whir.RateCfg

  A size's configuration at a rate: the body is the body at the rate's levels; the dispatches on
  the rate's selector call the rate's specializations.
-/

module

public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.Whir.RateFree

/-!
# A size's body at a rate

`open_stacked__L{m}` is `osBody (osCfg m)`, whose levels are the first rate's rows; the columns a
rate changes (`queries`, `depth`, `capDepth`, `squeezes`) reach the body only through the
dispatches' names (`OsCfg.lvAt`). So it is also the body at the configuration `osCfgR m ri`
whose levels are rate `ri`'s rows (`osBody_rate`, `Whir/RateFree.lean`), and the proof runs at
that configuration.

* `LvRate σ c lvl lv`: the selector `σ 0` is `g^ri` for a rate `ri < 4` whose row of level `lvl`
  is `lv`; `dispatch_rate`: a dispatch on it over `(c.lvAt lvl).map f` calls `f lv`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value

@[expose] public section

theorem osCfgR_lvAt_length (m ri lvl : ℕ) : ((osCfgR m ri).lvAt lvl).length = 4 := by
  simp [osCfgR, OsCfg.lvAt, osCfg]

theorem osCfgR_lvAt_getD {m ri : ℕ} (lvl : ℕ) (hri : ri < 4) :
    ((osCfgR m ri).lvAt lvl).getD ri default = (osCfgR m ri).levels.getD lvl default := by
  simp only [osCfgR, OsCfg.lvAt, osCfg, OsCfg.withLevels]
  rw [List.getD_eq_getElem _ _ (by simpa using hri)]
  simp only [List.getElem_map, List.getElem_range]

/-! ## The dispatches -/

/-- The rate's selector at level `lvl`: `σ 0 = g^ri`, `ri < 4`, and rate `ri`'s row of the level
is `lv`. -/
def LvRate (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Prop :=
  ∃ ri < 4, σ (.n osRate) = ofK (addressOfIndex ri) ∧ (c.lvAt lvl).length = 4 ∧
    (c.lvAt lvl).getD ri default = lv

/-- **A dispatch on the rate's selector** over the names `f` gives the rate's rows calls `f lv`. -/
theorem dispatch_rate {C : CallRel} {rd : Reader} {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hr : LvRate σ c lvl lv) (f : OsLv → String) {args rets : List V}
    (h : StmtOk C rd σ (.dispatch (.n osRate) ((c.lvAt lvl).map f) args rets)) :
    C (f lv) (args.map σ) (rets.map σ) := by
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hr
  have := stmtOk_dispatch hx (by omega) (by simp [hlen]) h
  obtain ⟨hlt, hc⟩ := this
  rw [List.length_map] at hlt
  rwa [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
    ← List.getD_eq_getElem _ default hlt, hlv] at hc


/-! ## The rate's values -/

/-- The values `level_rate` sets at a row, as exponents of `g`. -/
def osRateVals (lv : OsLv) : List ℕ := [lv.posOff, lv.squeezes, lv.queries / resBatch, lv.queries % resBatch]

/-- Arm `r` of `level_rate`'s `match` from `k`, at the row `lv` (`osRates`). -/
def osRateArm (k r : ℕ) (lv : OsLv) : List Stmt :=
  ((osRateVals lv).zipIdx.map fun (e, i) ↦
    let a := if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i
    [osCst a (gw e), osCp (k + 2 * i + 1) a]).flatten

theorem osRates_eq (c : OsCfg) (lvl : ℕ) (st : OsSt) : osRates c lvl st =
    (osCst st.k (word (2 ^ 63) 0) ::
      .match_ (.n osRate) ((c.lvAt lvl).zipIdx.map fun (lv, r) ↦ osRateArm (st.k + 1) r lv) ::
      [osMul (st.k + 1 + 8 + 4 * (ligNRates - 1)) osQpos (st.k + 1 + 1),
        osMul (st.k + 1 + 8 + 4 * (ligNRates - 1) + 1) osQbp (st.k + 1 + 1)],
     { st with k := st.k + 1 + 8 + 4 * (ligNRates - 1) + 2, lp := st.k + 1 + 8 + 4 * (ligNRates - 1),
               lw := st.k + 1 + 8 + 4 * (ligNRates - 1) + 1,
               rts := st.rts ++ [[st.k + 1 + 1, st.k + 1 + 3, st.k + 1 + 5, st.k + 1 + 7]] }) := rfl

theorem osRateArm_val {rd : Reader} {σ : Val} {k r : ℕ} {lv : OsLv} (h : AtomsOk rd σ (osRateArm k r lv))
    (i : ℕ) (hi : i < 4) : σ (.n (k + 2 * i + 1)) = gw ((osRateVals lv).getD i 0) := by
  have key : ∀ e, (osRateVals lv).getD i 0 = e →
      [osCst (if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i) (gw e),
        osCp (k + 2 * i + 1) (if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i)] ∈
        (osRateVals lv).zipIdx.map fun (e, i) ↦
          [osCst (if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i) (gw e),
            osCp (k + 2 * i + 1) (if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i)] := by
    intro e he
    refine List.mem_map.mpr ⟨(e, i), ?_, rfl⟩
    rw [← he]
    interval_cases i <;> simp [osRateVals, List.zipIdx]
  have hm := key _ rfl
  have h1 := h (.const (.n (if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i))
    (gw ((osRateVals lv).getD i 0))) (List.mem_flatten.mpr ⟨_, hm, List.mem_cons_self ..⟩)
  have h2 := h (.copy (.n (k + 2 * i + 1)) (.n (if r = 0 then k + 2 * i else k + 8 + 4 * (r - 1) + i)))
    (List.mem_flatten.mpr ⟨_, hm, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩)
  rw [holds_copy] at h2
  rw [holds_const] at h1
  rw [h2, h1]

/-- **`level_rate` at the rate's row**: the row's values as words, the level's positions and
window pointers `query_positions·g^posOff`, `query_win_ptrs·g^posOff`. -/
theorem osRates_sound {C : CallRel} {rd : Reader} {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    {st : OsSt} (hr : LvRate σ c lvl lv) (hok : AllOk C rd σ (osRates c lvl st).1) :
    (∀ i < 4, σ (.n (st.k + 1 + 2 * i + 1)) = gw ((osRateVals lv).getD i 0)) ∧
      σ (.n (osRates c lvl st).2.lp) = σ (.n osQpos) * gw lv.posOff ∧
      σ (.n (osRates c lvl st).2.lw) = σ (.n osQbp) * gw lv.posOff := by
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hr
  rw [osRates_eq] at hok ⊢
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, holds_mul, osMul] at hok
  obtain ⟨-, ⟨j, hj, hjx, hA⟩, m0, m1⟩ := hok
  have hjl : j < 4 := by simpa [hlen] using hj
  have hji : j = ri := gen_pow_inj (by omega) (by omega)
    (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK, ← hjx, hx])
  subst hji
  have harm : ((c.lvAt lvl).zipIdx.map fun (lv, r) ↦ osRateArm (st.k + 1) r lv)[j] =
      osRateArm (st.k + 1) j lv := by
    rw [List.getElem_map, List.getElem_zipIdx]
    simp only [Nat.zero_add]
    rw [← hlv, List.getD_eq_getElem _ _ (by omega)]
  rw [harm] at hA
  have hv := osRateArm_val hA
  have h0 := hv 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  refine ⟨hv, ?_, ?_⟩
  · simp only; rw [m0, h0]; rfl
  · simp only; rw [m1, h0]; rfl

end
end LeanVM.Guest.B1.Whir
