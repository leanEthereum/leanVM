/-
  LeanVM.Guest.B1.Da.CellSound

  `da_verify_cell`'s core IR gives its meaning.
-/

module

public import LeanVM.Guest.B1.Da.Padding
import LeanVM.Guest.B1.Da.CellLink

/-!
# `da_verify_cell`, sound

A valuation `σ` of `da_verify_cell`'s body gives one of its reference function's names
(`cellMap.rho σ`), the hinted values owning the symbols' names (`cell_linked`, `cell_owners`,
through `Map.pieces_fwd_at`), and on the names the commands give the weights read and the returned
words (`cellRef_sat`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Ref
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Digest

/-- A checked map's forward direction, as `Map.pieces_fwd_at` in one piece. -/
private theorem check_fwd_at {X : Type} [DecidableEq X] [Coded X] {m : Map X} {f : Fn}
    {r : Func X} {pos : List (ℕ × X)} (h : m.check f r = true) (hpos : ownersAt m pos = true)
    {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (hb : Stmt.HoldsList C rd σ f.body False kret) :
    f.params.map σ = r.params.map (m.rho σ) ∧ (∀ p ∈ pos, m.rho σ p.2 = σ (.n p.1)) ∧
      Cmd.SatList rd (m.rho σ) r.body ∧ kret (r.rets.map (Tm.eval (m.rho σ))) := by
  unfold Map.check at h
  rw [Bool.and_eq_true] at h
  split at h
  · rw [Bool.and_eq_true] at h
    exact Map.pieces_fwd_at (Kc := 0) (P := [f.body]) (Q := [r.body]) h.1 ‹_›
      (Tm.eqbs_sound h.2.1) (by simp) (by simp) h.2.2 hpos hb
  · exact absurd h.2 (by simp)

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
  obtain ⟨ep, hpos, hsat, hret⟩ := check_fwd_at cell_linked cell_owners hb
  obtain ⟨hr, hd⟩ := cellRef_sat hsat
  have hlv : σ (.n 0) = cellMap.rho σ .lvals := List.head_eq_of_cons_eq ep
  have hsyms : cellSymsOf σ = symsOf (cellMap.rho σ) :=
    List.map_congr_left fun j hj => (hpos (j + 1, .sym j) (List.mem_map_of_mem hj)).symm
  have hws : memRun rd (σ (.n 0)) 128 = wsOf (cellMap.rho σ) := by
    rw [hlv, readsAt_memRun hr]
    simp [wsOf]
  refine ⟨σ (.n 0), hpar.symm, by simp [cellSymsOf, LeanDa.cellSymbols], hws ▸ hlv ▸ hr,
    by simp [LeanDa.cellSymbols], ?_⟩
  rw [hsyms, hws, ← hd]
  exact hret.symm

/-- **`da_verify_cell`'s core IR gives its meaning.** -/
theorem da_verify_cell_holds : da_verify_cell_sound_Spec := by
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify_cell _ _).mp hrel
  obtain ⟨lv, rfl, hsl, hrd, hwl, hrets⟩ := da_verify_cell_val hpar hb
  exact ⟨cellSymsOf σ, memRun rd lv 128, hsl, hrd, hwl, hrets⟩

end
end LeanVM.Guest.B1.Da
