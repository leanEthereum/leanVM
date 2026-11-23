/-
  LeanVM.Guest.CoreMode.Fn.level_positions.Sound

  `level_positions`'s own routing facts and family, sound (`CoreMode/FnReg.lean`): its exponent facts and its count of
  squeezes at least `g^2`, carried down from its callers (`EndExec.expCarryQ_all`).
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResExpC
public import LeanVM.Guest.CoreMode.Fn.level_positions.Data
public import LeanVM.Guest.CoreMode.Fn.level_positions.Fam
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.level_positions

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

theorem expFacts_eq : expFacts = expCarry.map fun c ↦ (c.1, c.2.1, none, c.2.2.2) := by
  simp [expFacts, expCarry, List.map_map, Function.comp_def]

/-- **Its exponent facts** (`expOk_of_carry`). -/
theorem expFacts_ok : ∀ c ∈ expFacts, ExpOk c := by
  intro c hc
  rw [expFacts_eq] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  exact expOk_of_carry (FnReg.expCarry_of_level_positions _ hc')

/-- **Its family** (`expCarryQ_all`, its carried lower bound `2`). -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  intro c hc r hr I hI σ bufs kids ht fn hf x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨rfl, hp⟩ := hx
  have hmem : (k, param% level_positions "squeezes_g", 2, 268435456) ∈ FnReg.expCarry :=
    FnReg.expCarry_of_level_positions _ (by simp [expCarry, hk])
  obtain ⟨e, h1, h2, hσ⟩ := expCarryQ_all hr I hI _ hmem σ bufs kids ht fn hf _ hp
  dsimp only at h1 h2
  refine ⟨1, e, CoreMode.rep_const (by unfold CoreMode.capE; omega), ?_, by omega⟩
  simp only [CoreMode.idxC, CoreMode.valW_baseC, CoreMode.vw, hσ]
  exact CoreMode.rep_of (by unfold CoreMode.capE; omega)

end

end LeanVM.Guest.CoreMode.Own.level_positions
