/-
  LeanVM.Guest.CoreMode.Fn.level_positions.SoundA

  `level_positions`' own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its
  count of squeezes at least `g^2`, carried down from its callers (`EndExec.expCarryQ_allA`).
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.level_positions.Data
public import LeanVM.Guest.CoreMode.Fn.level_positions.Fam
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.level_positions

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- **Its family** (`expCarryQ_allA`, its carried lower bound `2`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc r hR hr I hI σ bufs kids ht fn hf x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨rfl, hp⟩ := hx
  have hmem : (k, param% level_positions "squeezes_g", 2, 268435456) ∈ FnReg.expCarry :=
    FnReg.expCarry_of_level_positions _ (by simp [expCarry, hk])
  obtain ⟨e, h1, h2, hσ⟩ := expCarryQ_allA hR I hI _ hmem σ bufs kids ht fn hf _ hp
  dsimp only at h1 h2
  refine ⟨1, e, CoreMode.rep_const (by unfold CoreMode.capE; omega), ?_, by omega⟩
  simp only [CoreMode.idxC, CoreMode.valW_baseC, CoreMode.vw, hσ]
  exact CoreMode.rep_of (by unfold CoreMode.capE; omega)

end

end LeanVM.Guest.CoreMode.Own.level_positions
