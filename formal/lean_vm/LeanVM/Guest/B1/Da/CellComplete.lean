/-
  LeanVM.Guest.B1.Da.CellComplete

  `da_verify_cell`, completely: `256` symbols (the hint) and the weights in memory give its core
  IR relation, its returns the cell's digest and the dot product (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.CellChk
public import LeanVM.Guest.B1.Da.CellCChk
public import LeanVM.Guest.B1.Digest.PairComplete

/-!
# `da_verify_cell`, completely

The honest valuation is the body evaluated on the weights' pointer (`Fwd.ev`), the hinted
symbols `ofK` of the honest ones. The template's assertions see `K` words and its loads read the
weights, so the template holds (`blk_sound` then packs each pair into a canonical cell); the
chain's inputs are canonical from the packed cells, so every atom holds. The returns are computed
as in `da_verify_cell_holds`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The cell's returns: its symbols' digest's cells, then their dot product with the weights. -/
def cellRets (syms : List K) (ws : List E) : List E :=
  digestCells (keccak256 (syms.flatMap K.toBytes)) ++
    [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * ofK (syms.getD e 0)).sum]

/-- `da_verify_cell`'s meaning, for given symbols and weights in memory, gives its core IR. -/
def da_verify_cell_complete_Spec : Prop :=
  ∀ (rd : Reader) (lv : E) (syms : List K) (ws : List E), syms.length = LeanDa.cellSymbols →
    ws.length = LeanDa.cellSymbols → ReadsAt rd lv ws →
      coreProgram.Rel rd "da_verify_cell" [lv] (cellRets syms ws)

/-- The oracle of the symbols' hint. -/
def symOrc (syms : List K) (j : ℕ) : E := ofK (syms.getD (j - 1) 0)

theorem symInK_spec {a : Atom} (h : isSymInK a = true) : ∃ x y, a = .assertInK x y ∧
    x = .n x.idx ∧ 1 ≤ x.idx ∧ x.idx ≤ 256 ∧ y = .n y.idx ∧ 1 ≤ y.idx ∧ y.idx ≤ 256 := by
  cases a <;> simp only [isSymInK, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rename_i x y
  exact ⟨x, y, rfl, h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem weightLoad_spec {a : Atom} (h : isWeightLoad a = true) :
    ∃ d i, a = .load d (.n 0) i ∧ i < 256 := by
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
  obtain ⟨⟨⟨⟨⟨c', hchk⟩, hst⟩, hcanT⟩, hneedsT⟩, hcok⟩ := hcok
  split at hok
  · rename_i A vs hsp
    rw [hsp] at hcok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hok hcok
    obtain ⟨⟨⟨⟨⟨rfl, hA1280⟩, htm⟩, hchain⟩, hret⟩, hcp⟩ := hok
    obtain ⟨⟨hcanC, hneedsC⟩, hhint⟩ := hcok
    have hbody := splitBody_eq hsp
    let w : ℕ → E := symOrc syms
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w [lv] (Fn.body Data.core30)) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body Data.core30) [lv] hchk
    rw [show [lv].length = 1 from rfl, hst, ← hσ] at hgs
    have hg : ∀ a ∈ A, Good rd [] w σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = lv := by rw [hσ]; exact ev_params rd _ (l := [lv]) hchk (by simp)
    -- the split of the atoms
    have hA : A = A.take 1 ++ (A.drop 1).take 1279 ++ A.drop 1280 := by
      have h1 : (A.drop 1).drop 1279 = A.drop 1280 := by simp
      rw [List.append_assoc, ← h1, List.take_append_drop, List.take_append_drop]
    rw [atomsEqb_sound htm, hhint] at hA
    have hmT : ∀ a ∈ tmplA, a ∈ A := fun a ha => by rw [hA]; simp [ha]
    have hmC : ∀ a ∈ A.drop 1280, a ∈ A := fun a ha => List.mem_of_mem_drop ha
    -- the symbols
    have hsym : ∀ j < 256, σ (.n (j + 1)) = ofK (syms.getD j 0) := by
      intro j hj
      have h := hg symHint (by rw [hA]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
      have := h (.n (j + 1)) (by simp; omega)
      rw [this]
      simp [w, symOrc]
    have hsymK : ∀ v : V, v = .n v.idx → 1 ≤ v.idx → v.idx ≤ 256 → IsInK (σ v) := by
      intro v hv h1 h2
      rw [hv, show v.idx = (v.idx - 1) + 1 by omega, hsym _ (by omega)]
      exact ofK_isInK _
    -- the template
    have htmpl : ∀ a ∈ tmplA, a.Holds rd σ := by
      refine atoms_holds hidx hcanT (fun a ha => hg a (hmT a ha))
        (fun i hi => absurd hi (by simp)) fun a ha hns => Or.inl ?_
      rcases hneedsT a ha with (h | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      · obtain ⟨x, y, rfl, hx, hx1, hx2, hy, hy1, hy2⟩ := symInK_spec h
        exact ⟨hsymK _ hx hx1 hx2, hsymK _ hy hy1 hy2⟩
      · obtain ⟨d, i, ha', hi⟩ := weightLoad_spec h
        clear h
        subst ha'
        rcases (hg _ (hmT _ ha) : Good rd [] w σ (.load d (.n 0) i)) with h | h
        · exact absurd h (by simp)
        · show LoadHolds rd (σ (.n 0)) i (σ d)
          have hl := hreads i (by omega)
          rw [h, e0, rdAt_of_load hl]
          exact hl
    -- the packed cells
    have hpack : ∀ e < 128, σ (.n (packV e)) =
        E.ofLimbs ((σ (.n (2 * e + 1))).limb 0) ((σ (.n (2 * e + 2))).limb 0) 0 :=
      fun e he => (blk_sound he htmpl).2.2.1
    have hcanP : ∀ i ∈ (List.range 128).map packV, IsCanonical128 (σ (.n i)) := by
      intro i hi
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
      rw [hpack e (List.mem_range.mp he)]
      exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
    have hC : ∀ a ∈ A.drop 1280, a.Holds rd σ :=
      atoms_holds hidx hcanC (fun a ha => hg a (hmC a ha)) hcanP
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
    obtain ⟨hd, -⟩ := straight_digest hchain rfl rfl hret hC
    have hsum := acc_sum htmpl 127 (by norm_num)
    rw [show accV 127 = 1407 from rfl] at hsum
    have hrets : [σ (.n 1740), σ (.n 1741), σ (.n 1742)] = cellRets syms ws := by
      rw [copy_sound hcp hC, hsum]
      have hv : ((cellSpec (A.drop 1280)).vals σ).take ((cellSpec (A.drop 1280)).len / 16) =
          (List.range 128).map fun e => σ (.n (packV e)) := by
        simp only [cellSpec, ChainSpec.vals, List.map_map]
        rw [List.take_of_length_le (by simp)]
        rfl
      rw [hv] at hd
      have hsyms : (List.range 256).map (fun j => (σ (.n (j + 1))).limb 0) = syms := by
        refine List.ext_getElem (by rw [List.length_map, List.length_range, hsl]) fun j h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        rw [hsym j (by simpa using h1), ofK_eq_ofLimbs, ofLimbs_limb0,
          List.getD_eq_getElem _ _ (by omega)]
      have hb : cellsBytes ((List.range 128).map fun e => σ (.n (packV e))) = syms.flatMap K.toBytes := by
        rw [← hsyms, show (256 : ℕ) = 2 * 128 from rfl, flatMap_pairs, cellsBytes, List.flatMap_map]
        refine List.flatMap_congr fun e he => ?_
        rw [cellBytes, hpack e (List.mem_range.mp he), ofLimbs_limb0, ofLimbs_limb1]
      rw [hb] at hd
      have hl : ∀ a b c : E, [a, b, c] = [a, b] ++ [c] := fun _ _ _ => rfl
      rw [hl, cellRets, ← hd]
      refine congrArg (fun x => [σ (.n 1740), σ (.n 1741)] ++ [x]) ?_
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
