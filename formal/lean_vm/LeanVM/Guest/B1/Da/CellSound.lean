/-
  LeanVM.Guest.B1.Da.CellSound

  `da_verify_cell`'s core IR gives its meaning (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.CellChk

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- The symbols `da_verify_cell` hints, read off its valuation. -/
def cellSymsOf (σ : Val) : List E := (List.range 128).map fun j => σ (.n (j + 1))

/-- **`da_verify_cell`'s body, at a valuation**: under any call relation (it calls nothing), the
meaning holds with the symbols `cellSymsOf σ` and the weights read at its argument. -/
theorem da_verify_cell_val {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    (hpar : (fn% «da_verify_cell»).params.map σ = args)
    (hb : Stmt.HoldsList C rd σ (Fn.body fn% «da_verify_cell») False (fun rs => rs = rets)) :
    ∃ lv, args = [lv] ∧ (cellSymsOf σ).length = LeanDa.cellSymbols ∧
      ReadsAt rd lv (memRun rd lv 128) ∧ (memRun rd lv 128).length = LeanDa.cellSymbols ∧
      rets = digestCells (keccak256 ((cellSymsOf σ).flatMap E.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦
          (memRun rd lv 128).getD e 0 * (cellSymsOf σ).getD e 0).sum] := by
  have hok := cell_ok
  unfold cellOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨rfl, -⟩, htm⟩, hchk⟩, hret⟩, hcp⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hrets⟩ := hb
    rw [hparams] at hpar
    subst hpar
    have htmpl : ∀ a ∈ tmplA, a.Holds rd σ := fun a ha => by
      rw [← atomsEqb_sound htm] at ha
      exact hat a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
    have hC : ∀ a ∈ A.drop 384, a.Holds rd σ := fun a ha => hat a (List.mem_of_mem_drop ha)
    have hd := straight_digest hchk rfl rfl hret hC
    have hsum := acc_sum htmpl 127 (by norm_num)
    rw [show accV 127 = 511 from rfl] at hsum
    refine ⟨σ (.n 0), rfl, by simp [LeanDa.cellSymbols, cellSymsOf], fun j hj => ?_,
      by simp [LeanDa.cellSymbols], ?_⟩
    · simp only [length_memRun] at hj
      simp only [memRun, List.getElem_map, List.getElem_range]
      exact (blk_sound hj htmpl).1
    · have hr : [σ (.n 844), σ (.n 845), σ (.n 846)] = rets := hrets
      rw [← hr, copy_sound hcp hC, hsum]
      have hv : ((cellSpec (A.drop 384)).vals σ).take ((cellSpec (A.drop 384)).len / 16) =
          cellSymsOf σ := by
        simp only [cellSpec, ChainSpec.vals, List.map_map]
        rw [List.take_of_length_le (by simp)]
        rfl
      rw [hv, cellsBytes_eq_eBytes] at hd
      have hl : ∀ a b c : E, [a, b, c] = [a, b] ++ [c] := fun _ _ _ => rfl
      rw [hl, ← hd]
      refine congrArg (fun x => [σ (.n 844), σ (.n 845)] ++ [x]) ?_
      simp only [LeanDa.cellSymbols]
      refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
      have hj' := List.mem_range.mp hj
      have h1 : j < (memRun rd (σ (.n 0)) 128).length := by rw [length_memRun]; exact hj'
      have h2 : j < (cellSymsOf σ).length := by
        rw [cellSymsOf, List.length_map, List.length_range]; exact hj'
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [memRun, cellSymsOf, List.getElem_map, List.getElem_range]
  · exact absurd hok (by simp)

/-- **`da_verify_cell`'s core IR gives its meaning.** -/
theorem da_verify_cell_holds : da_verify_cell_sound_Spec := by
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify_cell _ _).mp hrel
  obtain ⟨lv, rfl, hsl, hrd, hwl, hrets⟩ := da_verify_cell_val hpar hb
  exact ⟨cellSymsOf σ, memRun rd lv 128, hsl, hrd, hwl, hrets⟩

end
end LeanVM.Guest.B1.Da
