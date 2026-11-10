/-
  LeanVM.Guest.B1.Digest.StatementComplete

  `statement_digest`, completely: its meaning gives its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.StatementChk
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Steps

/-!
# `statement_digest`, completely

The honest valuation is the template evaluated on the arguments (`Fwd.ev`, its checks in
`StatementChk`): its loads hold on the words the meaning reads, so every atom holds
(`Fwd.atoms_holds`). The relation then holds at the valuation's returns, which soundness makes
the meaning's digest; the meaning's words are the memory's, so its returns are these.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem mem_sd_load {a : Atom} (ha : a ∈ sdLoads) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))))

/-- The meaning's words are the memory's: its returns are determined. -/
theorem statement_digest_unique {rd : Reader} {args r r' : List E}
    (h : MeaningStatementDigest rd args r) (h' : MeaningStatementDigest rd args r') : r = r' := by
  match args, h, h' with
  | [s0, s1, x0, x1, y0, y1, a0, a1, dp], h, h' =>
    obtain ⟨cells, hlen, hreads, hr⟩ := h
    obtain ⟨cells', hlen', hreads', hr'⟩ := h'
    have hc : cells' = cells := by
      rw [readsAt_memRun hreads, readsAt_memRun hreads', hlen, hlen']
    rw [hr, hr', hc]

set_option maxRecDepth 10000 in
/-- **`statement_digest` is complete.** -/
theorem statement_digest_complete : statement_digest_complete_Spec := by
  intro rd args rets h
  match args, h with
  | [s0, s1, x0, x1, y0, y1, a0, a1, dp], h =>
    have hM := h
    obtain ⟨cells, hlen, hreads, -⟩ := h
    let args : List E := [s0, s1, x0, x1, y0, y1, a0, a1, dp]
    let σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args sdBody)
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) sdBody args sd_chk
    rw [show args.length = 9 from rfl, sd_stores] at hgs
    have hg : ∀ a ∈ sdAtoms, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (List.mem_append_left _ (List.mem_map_of_mem ha))
    have hpar : ∀ i < 9, σ (.n i) = args.getD i 0 := fun i hi => ev_params rd _ (l := args) sd_chk hi
    have e8 : σ (.n 8) = dp := hpar 8 (by omega)
    -- every atom: the loads read the meaning's cells
    have hat : ∀ a ∈ sdAtoms, a.Holds rd σ := by
      refine atoms_holds hg fun a ha hn => Or.inl ?_
      have hf : a ∈ sdAtoms.filter needsSide := List.mem_filter.mpr ⟨ha, hn⟩
      rw [sd_needs] at hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
      have hi' := List.mem_range.mp hi
      have g := hg _ ha
      have hl := hreads i (by omega)
      simp only [Good] at g
      show LoadHolds rd (σ (.n 8)) i (σ (.n (17 + i)))
      rcases g with g | g
      · simp at g
      · rw [g, e8, rdAt_of_load hl]
        exact hl
    -- the relation, and its returns
    have hrel : coreProgram.Rel rd "statement_digest" args [σ (.n 115), σ (.n 116)] := by
      refine (rel_iff_sem find_statement_digest _ _).mpr ⟨σ, ?_, ?_⟩
      · rw [core21_params]
        simp only [List.map_cons, List.map_nil]
        rw [hpar 0 (by omega), hpar 1 (by omega), hpar 2 (by omega), hpar 3 (by omega),
          hpar 4 (by omega), hpar 5 (by omega), hpar 6 (by omega), hpar 7 (by omega),
          hpar 8 (by omega)]
        rfl
      · rw [core21_body, holdsList_atoms_ret]
        exact ⟨hat, rfl⟩
    rw [statement_digest_unique hM (statement_digest_sound rd _ _ hrel)]
    exact hrel
  | [], h => exact h.elim
  | [_], h => exact h.elim
  | [_, _], h => exact h.elim
  | [_, _, _], h => exact h.elim
  | [_, _, _, _], h => exact h.elim
  | [_, _, _, _, _], h => exact h.elim
  | [_, _, _, _, _, _], h => exact h.elim
  | [_, _, _, _, _, _, _], h => exact h.elim
  | [_, _, _, _, _, _, _, _], h => exact h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Digest
