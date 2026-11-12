/-
  LeanVM.Guest.B1.Whir.RateCfg

  A size's configuration at a rate: the body is the body at the rate's levels; the dispatches on
  the rate's selector call the rate's specializations.
-/

module

public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.Whir.DataAll

/-!
# A size's body at a rate

`open_stacked__L{m}` is `osBody (osCfg m)`, whose levels are the first rate's rows; the columns a
rate changes (`queries`, `depth`, `capDepth`, `squeezes`) reach the body only through the
dispatches' names (`OsCfg.lvAt`). So it is also the body at the configuration `osCfgR m ri`
whose levels are rate `ri`'s rows (`osBody_rate`, `OsRate` decided by the kernel in
`Whir/Data*.lean`), and the proof runs at that configuration.

* `LvRate σ c lvl lv`: the selector `σ 0` is `g^ri` for a rate `ri < 4` whose row of level `lvl`
  is `lv`; `dispatch_rate`: a dispatch on it over `(c.lvAt lvl).map f` calls `f lv`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value

@[expose] public section

/-- **A size's body is its body at any rate's levels.** -/
theorem osBody_rate {m ri : ℕ} (hm : m < ligNSizes) (hri : ri < ligNRates) :
    osBody (osCfg m) = osBody (osCfgR m ri) :=
  osRate_all m hm ri hri

theorem osCfgR_lvAt (m ri lvl : ℕ) : (osCfgR m ri).lvAt lvl = (osCfg m).lvAt lvl := rfl

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

end
end LeanVM.Guest.B1.Whir
