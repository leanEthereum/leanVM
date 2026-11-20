/-
  LeanVM.Guest.B1.Sig.SpWotsLinksAll

  `sp_wots`'s compiled function is its reference function, with the values its signature's
  decoder reads owning their names: the pieces of its link, assembled.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLinks0
public import LeanVM.Guest.B1.Sig.SpWotsLinks1
public import LeanVM.Guest.B1.Sig.SpWotsLinks2

/-!
# `sp_wots`, linked

`sp_wots_fwd` and `sp_wots_sem_iff` are what the pieces of `SpWotsLinks0` to `SpWotsLinks2` give
(`Map.pieces_fwd_at`, `Map.pieces_sem_iff`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Ref

public section

private theorem sp_piece {i : ℕ} (hi : i < 22) : spPiece i = true := by
  interval_cases i
  exacts [sp_piece_0, sp_piece_1, sp_piece_2, sp_piece_3, sp_piece_4, sp_piece_5, sp_piece_6,
    sp_piece_7, sp_piece_8, sp_piece_9, sp_piece_10, sp_piece_11, sp_piece_12, sp_piece_13,
    sp_piece_14, sp_piece_15, sp_piece_16, sp_piece_17, sp_piece_18, sp_piece_19, sp_piece_20,
    sp_piece_21]

/-- The pieces, together. -/
theorem sp_pieces : spMap.Pieces spKc spWotsRef.rets spK0 (cutAt spCuts Fn.«sp_wots».core.body)
    (cutAt spRefCuts spWotsRef.body) :=
  Map.pieces_of 22 _ _ _ (by rw [length_cutAt]; rfl) (by rw [length_cutAt]; rfl)
    (fun i hi => ((Bool.and_eq_true _ _).mp (sp_piece hi)).2)
    ((Bool.and_eq_true _ _).mp sp_piece_last).2

/-- **A valuation of `sp_wots`'s body is one of its reference function's names**, the decoder's
values owning theirs. -/
theorem sp_wots_fwd {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (hb : Stmt.HoldsList C rd σ Fn.«sp_wots».core.body False kret) :
    ∃ ρ : SpName → E, Fn.«sp_wots».core.params.map σ = spWotsRef.params.map ρ ∧
      (∀ p ∈ spPositions, ρ p.2 = σ (.n p.1)) ∧ Cmd.SatList rd ρ spWotsRef.body ∧
        kret (spWotsRef.rets.map (Tm.eval ρ)) :=
  ⟨_, Map.pieces_fwd_at sp_distinct sp_params.1 (Tm.eqbs_sound sp_params.2)
    (flatten_cutAt _ _).symm (flatten_cutAt _ _).symm sp_pieces sp_owners hb⟩

/-- **`sp_wots`'s core IR is its reference function.** -/
theorem sp_wots_sem_iff {C : CallRel} {rd : Reader} (args rets : List E) :
    (Fn.«sp_wots».core).Sem C rd args rets ↔ spWotsRef.Sem rd args rets :=
  Map.pieces_sem_iff sp_distinct sp_params.1 (Tm.eqbs_sound sp_params.2) (flatten_cutAt _ _).symm
    (flatten_cutAt _ _).symm sp_pieces args rets

end
end LeanVM.Guest.B1.Sig
