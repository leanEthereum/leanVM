/-
  LeanVM.Guest.B1.Whir.OsCfgFactsB

  `OsBodyFacts` from one Boolean check, decided per configuration.
-/

module

public import LeanVM.Guest.B1.Whir.OsCfgFacts
public import LeanVM.Guest.B1.Whir.StackedCfg

/-!
# A configuration's body facts by evaluation

`osFactsB cfg`: the layout's inequalities over the levels, the sizes' bounds, the body's last
statement a `ret`, the statements before it straight-line with no `frameAddr` and the buffers
`osAllocList cfg`, and the tail challenges' value apart from `osFch`. `os_facts_of`: it gives
`OsBodyFacts cfg`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The layout's inequalities between two levels `i < j`. -/
def osLayPair (cfg : OsCfg) (i j : ℕ) : Bool :=
  decide (4 * (cfg.lv i).capOff + 2 * 2 ^ ((cfg.lv i).capDepth + 1) ≤ 4 * (cfg.lv j).capOff) &&
    decide ((cfg.lv i).capOff + 2 ^ (cfg.lv i).capDepth ≤ (cfg.lv j).capOff) &&
    decide ((cfg.lv i).foldsOff + (cfg.lv i).folds ≤ (cfg.lv j).foldsOff) &&
    decide ((cfg.lv i).posOff + (cfg.lv i).squeezes * (192 / (cfg.lv i).depth) ≤ (cfg.lv j).posOff)

/-- The layout's inequalities at one level. -/
def osLayOne (cfg : OsCfg) (i : ℕ) : Bool :=
  decide (4 * (cfg.lv i).capOff + 2 * 2 ^ ((cfg.lv i).capDepth + 1) ≤ 4 * cfg.capLen) &&
    decide ((cfg.lv i).capOff + 2 ^ (cfg.lv i).capDepth ≤ cfg.capLen) &&
    decide ((cfg.lv i).foldsOff + (cfg.lv i).folds ≤ cfg.nFolds) &&
    decide ((cfg.lv i).queries ≤ cfg.maxQ) &&
    decide ((cfg.lv i).posOff + (cfg.lv i).squeezes * (192 / (cfg.lv i).depth) ≤ cfg.posLen) &&
    decide ((cfg.lv i).logCols ≤ 22) && decide ((cfg.lv i).prefixLen + cfg.yrLog ≤ 22) &&
    decide ((cfg.lv i).squeezes ≤ cfg.maxSq) && decide (2 ^ (cfg.lv i).folds ≤ cfg.maxIl) &&
    decide (0 < (cfg.lv i).queries)

/-- The layout, by evaluation. -/
def osLayoutB (cfg : OsCfg) : Bool :=
  (List.range cfg.levels.length).all (fun j => (List.range j).all fun i => osLayPair cfg i j) &&
    (List.range cfg.levels.length).all (osLayOne cfg)

theorem os_layout_of {cfg : OsCfg} (h : osLayoutB cfg = true) : OsLayoutOk cfg := by
  simp only [osLayoutB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hp, ho⟩ := h
  have P : ∀ i j, i < j → j < cfg.levels.length → osLayPair cfg i j = true := fun i j hij hj =>
    hp j hj i hij
  have O : ∀ i < cfg.levels.length, osLayOne cfg i = true := ho
  simp only [osLayPair, Bool.and_eq_true, decide_eq_true_eq] at P
  simp only [osLayOne, Bool.and_eq_true, decide_eq_true_eq] at O
  exact ⟨fun i j hij hj => (P i j hij hj).1.1.1, fun i hi => (O i hi).1.1.1.1.1.1.1.1.1,
    fun i j hij hj => (P i j hij hj).1.1.2, fun i hi => (O i hi).1.1.1.1.1.1.1.1.2,
    fun i j hij hj => (P i j hij hj).1.2, fun i hi => (O i hi).1.1.1.1.1.1.1.2,
    fun i hi => (O i hi).1.1.1.1.1.1.2, fun i j hij hj => (P i j hij hj).2,
    fun i hi => (O i hi).1.1.1.1.1.2, fun i hi => (O i hi).1.1.1.1.2, fun i hi => (O i hi).1.1.1.2,
    fun i hi => (O i hi).1.1.2, fun i hi => (O i hi).1.2, fun i hi => (O i hi).2⟩

/-- The sizes, by evaluation. -/
def osSizesB (cfg : OsCfg) : Bool :=
  (osHeadSizes cfg).all (fun s => decide (s < 2 ^ 64 - 1)) && decide (2 * (cfg.maxSq + 1) < 2 ^ 64 - 1) &&
    decide (cfg.maxIl < 2 ^ 64 - 1) && decide (cfg.levels.length * 22 < 2 ^ 64 - 1) &&
    decide (cfg.levels.length + 1 < 2 ^ 64 - 1) && decide (cfg.maxQ + 1 < 2 ^ 64 - 1)

theorem os_sizes_of {cfg : OsCfg} (h : osSizesB cfg = true) : OsSizesOk cfg := by
  simp only [osSizesB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The body ends in a `ret`. -/
def osRetB (cfg : OsCfg) : Bool :=
  match (osBody cfg).getLast? with
  | some (.ret _) => true
  | _ => false

theorem os_last_of {cfg : OsCfg} (h : osRetB cfg = true) :
    osBody cfg = (osBody cfg).dropLast ++ [.ret (osRetVs cfg)] := by
  unfold osRetB at h
  unfold osRetVs
  split at h
  · next vs hl =>
    rw [hl]
    exact (List.dropLast_append_getLast? _ hl).symm
  · exact absurd h (by simp)

/-- **A configuration's body facts, by evaluation.** -/
def osFactsB (cfg : OsCfg) : Bool :=
  osLayoutB cfg && osSizesB cfg && osRetB cfg && (osBody cfg).dropLast.all Main.Stmt.straight &&
    ((osBody cfg).dropLast.filterMap Main.Stmt.addrS).isEmpty &&
    decide ((osBody cfg).dropLast.filterMap Main.Stmt.allocSz = osAllocList cfg) &&
    decide (OsRun.tch cfg ≠ osFch)

theorem os_facts_of {cfg : OsCfg} (h : osFactsB cfg = true) : OsBodyFacts cfg := by
  simp only [osFactsB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hs⟩, hr⟩, hst⟩, ha⟩, hal⟩, ht⟩ := h
  exact ⟨os_layout_of hl, os_sizes_of hs, os_last_of hr, hst, ha, hal, ht⟩

end
end LeanVM.Guest.B1
