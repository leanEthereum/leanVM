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
def cellSymsOf (σ : Val) : List K := (List.range 256).map fun j => (σ (.n (j + 1))).limb 0

/-- **`da_verify_cell`'s body, at a valuation**: under any call relation (it calls nothing), the
meaning holds with the symbols `cellSymsOf σ` and the weights read at its argument. -/
theorem da_verify_cell_val {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    (hpar : (fn% «da_verify_cell»).params.map σ = args)
    (hb : Stmt.HoldsList C rd σ (Fn.body fn% «da_verify_cell») False (fun rs => rs = rets)) :
    ∃ lv, args = [lv] ∧ (cellSymsOf σ).length = LeanDa.cellSymbols ∧
      ReadsAt rd lv (memRun rd lv 256) ∧ (memRun rd lv 256).length = LeanDa.cellSymbols ∧
      rets = digestCells (keccak256 ((cellSymsOf σ).flatMap K.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦
          (memRun rd lv 256).getD e 0 * ofK ((cellSymsOf σ).getD e 0)).sum] := by
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
    have hC : ∀ a ∈ A.drop 1280, a.Holds rd σ := fun a ha => hat a (List.mem_of_mem_drop ha)
    have hd := straight_digest hchk rfl rfl hret hC
    have hsym : ∀ j < 256, IsInK (σ (.n (j + 1))) := by
      intro j hj
      obtain ⟨h1, h2, -⟩ := blk_sound (show j / 2 < 128 by omega) htmpl
      rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [show j + 1 = 2 * (j / 2) + 1 by omega]; exact h1
      · rw [show j + 1 = 2 * (j / 2) + 2 by omega]; exact h2
    have hloads : ∀ j < 256, LoadHolds rd (σ (.n 0)) j (memAt rd (σ (.n 0)) j) := by
      intro j hj
      obtain ⟨-, -, -, l0, l1, -⟩ := blk_sound (show j / 2 < 128 by omega) htmpl
      rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [show j = 2 * (j / 2) by omega]; exact l0
      · rw [show j = 2 * (j / 2) + 1 by omega]; exact l1
    have hsum := acc_sum htmpl 127 (by norm_num)
    rw [show accV 127 = 1407 from rfl] at hsum
    refine ⟨σ (.n 0), rfl, by simp [LeanDa.cellSymbols, cellSymsOf], fun j hj => ?_,
      by simp [LeanDa.cellSymbols], ?_⟩
    · simp only [length_memRun] at hj
      simp only [memRun, List.getElem_map, List.getElem_range]
      exact hloads j hj
    · have hr : [σ (.n 1740), σ (.n 1741), σ (.n 1742)] = rets := hrets
      rw [← hr, copy_sound hcp hC, hsum]
      have hv : ((cellSpec (A.drop 1280)).vals σ).take ((cellSpec (A.drop 1280)).len / 16) =
          (List.range 128).map fun e => σ (.n (packV e)) := by
        simp only [cellSpec, ChainSpec.vals, List.map_map]
        rw [List.take_of_length_le (by simp)]
        rfl
      rw [hv] at hd
      have hb : cellsBytes ((List.range 128).map fun e => σ (.n (packV e))) =
          (cellSymsOf σ).flatMap K.toBytes := by
        rw [cellSymsOf, show (256 : ℕ) = 2 * 128 from rfl, flatMap_pairs, cellsBytes, List.flatMap_map]
        refine List.flatMap_congr fun e he => ?_
        have hp := (blk_sound (List.mem_range.mp he) htmpl).2.2.1
        rw [cellBytes, hp, ofLimbs_limb0, ofLimbs_limb1]
      rw [hb] at hd
      have hl : ∀ a b c : E, [a, b, c] = [a, b] ++ [c] := fun _ _ _ => rfl
      rw [hl, ← hd]
      refine congrArg (fun x => [σ (.n 1740), σ (.n 1741)] ++ [x]) ?_
      simp only [LeanDa.cellSymbols]
      refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
      have hj' := List.mem_range.mp hj
      have h1 : j < (memRun rd (σ (.n 0)) 256).length := by rw [length_memRun]; exact hj'
      have h2 : j < (cellSymsOf σ).length := by
        rw [cellSymsOf, List.length_map, List.length_range]; exact hj'
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [memRun, cellSymsOf, List.getElem_map, List.getElem_range]
      rw [← eq_ofK_limb (hsym j hj')]
  · exact absurd hok (by simp)

/-- **`da_verify_cell`'s core IR gives its meaning.** -/
theorem da_verify_cell_holds : da_verify_cell_sound_Spec := by
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify_cell _ _).mp hrel
  obtain ⟨lv, rfl, hsl, hrd, hwl, hrets⟩ := da_verify_cell_val hpar hb
  exact ⟨cellSymsOf σ, memRun rd lv 256, hsl, hrd, hwl, hrets⟩

end
end LeanVM.Guest.B1.Da
