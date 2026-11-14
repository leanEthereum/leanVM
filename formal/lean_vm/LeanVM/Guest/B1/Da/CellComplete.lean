/-
  LeanVM.Guest.B1.Da.CellComplete

  `da_verify_cell`, completely: `128` symbols (the hint) and the weights in memory give its core
  IR relation, its returns the cell's digest and the dot product (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.CellChk
public import LeanVM.Guest.B1.Da.CellCChk
public import LeanVM.Guest.B1.Digest.PairComplete

/-!
# `da_verify_cell`, completely

The honest valuation is the body evaluated on the weights' pointer (`Fwd.ev`), the hinted
symbols the honest ones. The template's loads read the weights, so the template holds, and every
atom holds. The returns are computed as in `da_verify_cell_holds`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The cell's returns: its symbols' digest's cells, then their dot product with the weights. -/
def cellRets (syms ws : List E) : List E :=
  digestCells (keccak256 (syms.flatMap E.toBytes)) ++
    [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * syms.getD e 0).sum]

/-- `da_verify_cell`'s meaning, for given symbols and weights in memory, gives its core IR. -/
def da_verify_cell_complete_Spec : Prop :=
  ∀ (rd : Reader) (lv : E) (syms ws : List E), syms.length = LeanDa.cellSymbols →
    ws.length = LeanDa.cellSymbols → ReadsAt rd lv ws →
      coreProgram.Rel rd "da_verify_cell" [lv] (cellRets syms ws)

/-- The oracle of the symbols' hint. -/
def symOrc (syms : List E) (j : ℕ) : E := syms.getD (j - 1) 0

theorem weightLoad_spec {a : Atom} (h : isWeightLoad a = true) :
    ∃ d i, a = .load d (.n 0) i ∧ i < 128 := by
  unfold isWeightLoad at h
  split at h
  · rename_i d p i
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨d, i, by rw [h.1], h.2⟩
  · exact absurd h (by simp)

set_option maxRecDepth 10000 in
/-- **`da_verify_cell` is complete.** -/
theorem da_verify_cell_complete : da_verify_cell_complete_Spec := by
  intro rd lv syms ws hsl hwl hreads
  simp only [LeanDa.cellSymbols] at hsl hwl
  have hok := cell_ok
  have hcok := cellc_ok
  unfold cellOk at hok
  unfold cellCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hcok
  obtain ⟨hparams, hok⟩ := hok
  obtain ⟨⟨⟨⟨c', hchk⟩, hst⟩, hneedsT⟩, hcok⟩ := hcok
  split at hok
  · rename_i A vs hsp
    rw [hsp] at hcok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hok hcok
    obtain ⟨⟨⟨⟨⟨rfl, hA384⟩, htm⟩, hchain⟩, hret⟩, hcp⟩ := hok
    obtain ⟨hneedsC, hhint⟩ := hcok
    have hbody := splitBody_eq hsp
    let w : ℕ → E := symOrc syms
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w [lv] (Fn.body fn% «da_verify_cell»)) :=
        ⟨_, rfl⟩
    obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body fn% «da_verify_cell») [lv] hchk
    rw [show [lv].length = 1 from rfl, hst, ← hσ] at hgs
    have hg : ∀ a ∈ A, Good rd [] w σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = lv := by rw [hσ]; exact ev_params rd _ (l := [lv]) hchk (by simp)
    -- the split of the atoms
    have hA : A = A.take 1 ++ (A.drop 1).take 383 ++ A.drop 384 := by
      have h1 : (A.drop 1).drop 383 = A.drop 384 := by simp
      rw [List.append_assoc, ← h1, List.take_append_drop, List.take_append_drop]
    rw [atomsEqb_sound htm, hhint] at hA
    have hmT : ∀ a ∈ tmplA, a ∈ A := fun a ha => by rw [hA]; simp [ha]
    have hmC : ∀ a ∈ A.drop 384, a ∈ A := fun a ha => List.mem_of_mem_drop ha
    -- the symbols
    have hsym : ∀ j < 128, σ (.n (j + 1)) = syms.getD j 0 := by
      intro j hj
      have h := hg symHint (by rw [hA]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
      have := h (.n (j + 1)) (by simp; omega)
      rw [this]
      simp [w, symOrc]
    -- the template
    have htmpl : ∀ a ∈ tmplA, a.Holds rd σ := by
      refine atoms_holds (fun a ha => hg a (hmT a ha)) fun a ha hns => Or.inl ?_
      rcases hneedsT a ha with h | h
      · rw [hns] at h; exact absurd h (by simp)
      · obtain ⟨d, i, ha', hi⟩ := weightLoad_spec h
        clear h
        subst ha'
        rcases (hg _ (hmT _ ha) : Good rd [] w σ (.load d (.n 0) i)) with h | h
        · exact absurd h (by simp)
        · show LoadHolds rd (σ (.n 0)) i (σ d)
          have hl := hreads i (by omega)
          rw [h, e0, rdAt_of_load hl]
          exact hl
    have hC : ∀ a ∈ A.drop 384, a.Holds rd σ :=
      atoms_holds (fun a ha => hg a (hmC a ha))
        fun a ha hns => by rw [hneedsC a ha] at hns; exact absurd hns (by simp)
    have hat : ∀ a ∈ A, a.Holds rd σ := by
      intro a ha
      rw [hA] at ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (rfl | ha) | ha
      · trivial
      · exact htmpl a ha
      · exact hC a ha
    -- the returns
    have hd := straight_digest hchain rfl rfl hret hC
    have hsum := acc_sum htmpl 127 (by norm_num)
    rw [show accV 127 = 511 from rfl] at hsum
    have hrets : [σ (.n 844), σ (.n 845), σ (.n 846)] = cellRets syms ws := by
      rw [copy_sound hcp hC, hsum]
      have hv : ((cellSpec (A.drop 384)).vals σ).take ((cellSpec (A.drop 384)).len / 16) =
          (List.range 128).map fun j => σ (.n (j + 1)) := by
        simp only [cellSpec, ChainSpec.vals, List.map_map]
        rw [List.take_of_length_le (by simp)]
        rfl
      have hsyms : (List.range 128).map (fun j => σ (.n (j + 1))) = syms := by
        refine List.ext_getElem (by rw [List.length_map, List.length_range, hsl]) fun j h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        rw [hsym j (by simpa using h1), List.getD_eq_getElem _ _ (by omega)]
      rw [hv, hsyms, cellsBytes_eq_eBytes] at hd
      have hl : ∀ a b c : E, [a, b, c] = [a, b] ++ [c] := fun _ _ _ => rfl
      rw [hl, cellRets, ← hd]
      refine congrArg (fun x => [σ (.n 844), σ (.n 845)] ++ [x]) ?_
      simp only [LeanDa.cellSymbols]
      refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
      have hj' := List.mem_range.mp hj
      rw [e0, hsym j hj', memAt_of_load (hreads j (by omega)), List.getD_eq_getElem ws _ (by omega)]
    refine (rel_iff_sem find_da_verify_cell _ _).mpr ⟨σ, by rw [hparams]; simp [e0], ?_⟩
    rw [hbody, holdsList_atoms_ret]
    exact ⟨hat, hrets⟩
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
