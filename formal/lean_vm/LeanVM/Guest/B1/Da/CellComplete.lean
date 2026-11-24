/-
  LeanVM.Guest.B1.Da.CellComplete

  `da_verify_cell`, completely: `128` symbols (the hint) and the weights in memory give its core
  IR relation, its returns the cell's digest and the dot product.
-/

module

public import LeanVM.Guest.B1.Da.Interface
import LeanVM.Guest.B1.Da.CellLink
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_cell»

/-!
# `da_verify_cell`, completely

The symbols and the weights satisfy the meaning, so the reference function (`cellRef_sem`) and,
through the link (`cell_linked`), the core function relate the weights' pointer to `cellRets`. On
the honest valuation of the names (`cellRef_honest`) carried to the body (`cell_owners`), the
hinted values hold the symbols (`da_verify_cell_complete_vals`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Digest

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

/-- A checked map's backward direction, as `Map.pieces_bwd_at` in one piece. -/
private theorem check_bwd_at {X : Type} [DecidableEq X] [Coded X] {m : Map X} {f : Fn}
    {r : Func X} {pos : List (ℕ × X)} (h : m.check f r = true) (hpos : ownersAt m pos = true)
    {C : CallRel} {rd : Reader} {ρ : X → E} {kret : List E → Prop}
    (hsat : Cmd.SatList rd ρ r.body) (hret : kret (r.rets.map (Tm.eval ρ))) :
    f.params.map (m.sig ρ) = r.params.map ρ ∧ (∀ p ∈ pos, m.sig ρ (.n p.1) = ρ p.2) ∧
      Stmt.HoldsList C rd (m.sig ρ) f.body False kret := by
  unfold Map.check at h
  rw [Bool.and_eq_true] at h
  split at h
  · rw [Bool.and_eq_true] at h
    exact Map.pieces_bwd_at (Kc := 0) (P := [f.body]) (Q := [r.body]) (Tm.eqbs_sound h.2.1)
      (by simp) (by simp) h.2.2 hpos hsat hret
  · exact absurd h.2 (by simp)

/-- **`da_verify_cell` is complete, its hinted symbols exposed**: a valuation of its parameter `lv`
holding the symbols at `.n 1 ..= .n 128`, on which its body holds under every call relation,
returning `cellRets syms ws`. -/
theorem da_verify_cell_complete_vals (rd : Reader) (lv : E) (syms : List E) (ws : List E)
    (hsl : syms.length = LeanDa.cellSymbols) (hwl : ws.length = LeanDa.cellSymbols) (hreads : ReadsAt rd lv ws) :
    ∃ σ : Val, σ (.n (val% «da_verify_cell» "lvals")) = lv ∧ (∀ j < 128, σ (.n (j + (val% «da_verify_cell» "sym[0]"))) = syms.getD j 0) ∧ ∀ C : CallRel,
      Stmt.HoldsList C rd σ (Fn.body fn% «da_verify_cell») False (fun rs => rs = cellRets syms ws) := by
  obtain ⟨ρ, hp, hs, hr, hsym⟩ := cellRef_honest hsl hreads hwl
  have h := fun C => check_bwd_at (C := C) cell_linked cell_owners hs (kret := (· = cellRets syms ws)) hr
  refine ⟨cellMap.sig ρ, ?_, fun j hj => ?_, fun C => (h C).2.2⟩
  · have e : [cellMap.sig ρ (.n 0)] = [lv] := ((h fun _ _ _ => True).1).trans hp
    exact List.head_eq_of_cons_eq e
  · exact ((h fun _ _ _ => True).2.1 (j + 1, .sym j)
      (List.mem_map_of_mem (List.mem_range.mpr hj))).trans (hsym j)

theorem da_verify_cell_params : (fn% «da_verify_cell»).params = [.n (val% «da_verify_cell» "lvals")] :=
  rfl

/-- **`da_verify_cell` is complete.** -/
theorem da_verify_cell_complete : da_verify_cell_complete_Spec := fun _ _ syms ws hsl hwl hr =>
  (cellVerified.rel_iff_of_check (c := ()) find_da_verify_cell cell_linked _ _).mpr
    ⟨syms, ws, hsl, hr, hwl, rfl⟩

end
end LeanVM.Guest.B1.Da
