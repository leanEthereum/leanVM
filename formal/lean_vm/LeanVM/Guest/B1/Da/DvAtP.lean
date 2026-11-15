/-
  LeanVM.Guest.B1.Da.DvAtP

  `da_verify` placed on a witness by trees that pop the honest hints: its blobs' cell loops by trees whose cell checks
  hold the witness's symbols (`cellL_completeAtTB`), so every valid instance of the tree pops the shape, the challenge
  and the cells' symbols blob by blob.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.DaPops

/-!
# `da_verify`, popping its hints

`daPopsW z w`: the check's entries on a witness; `da_verify_completeAtTBP`: `da_verify` complete within `dvB` by
trees of its honest shape whose valid instances pop them.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Returns)

@[expose] public section

/-- The check's entries on a witness `w`, its challenge `z`: its shape, its challenge, its blobs' cells. -/
def daPopsW (z : E) (w : LeanVM.Da.MatrixWitness) : List Pop :=
  ("da_shape", [gen ^ w.rows.length, gen ^ wLog w]) :: ("da_challenge", [z]) :: daSymPops w

variable {fs SB SK : String → ℕ} (cert : String → V → ℕ)

/-- **`da_verify` is complete, placed, on a witness opening `(root, z)`, by a tree of its honest shape whose valid
instances pop its hints**, within `dvB`. -/
theorem da_verify_completeAtTBP (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness}
    {root : LeanVM.Protocol.Digest} {z : E} (hw : w.Opens root z) (s : ℕ) (hS : DvStaticB fs SB SK) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ [z]))
      (fun t => dvNH w.rows.length (wLog w) t ∧ ∀ (rd : Reader) (args rets : List E),
        t.Valid coreProgram rd args rets → t.pops coreProgram rd = daPopsW z w)
      (dvB fs SB SK w.rows.length (wLog w)) := by
  have hr1 := hw.1
  have hr : w.rows.length ≤ 1024 := hw.2.1
  have hL : 2 ^ wLog w = LeanDa.paddedRowCount w.rows.length := rfl
  have hL10 : wLog w ≤ 10 := by
    obtain ⟨-, hhi⟩ := nPad_bounds hr1
    have hlt : 2 ^ wLog w < 2 ^ 11 := by
      calc 2 ^ wLog w < 2 * w.rows.length := hL ▸ hhi
        _ ≤ 2 ^ 11 := by norm_num; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hsl := wSyms_len hw
  rw [opens_eq hw]
  refine (dv_completeAtB_z fs cert hrf hS hr1 hw.2.1 hL hsl (wDot hw) s).mono le_rfl
    fun t ht => ⟨dvNH_of_zC ht, fun rd args rets hv => ?_⟩
  obtain ⟨k3, args3, v3, t3, e⟩ := dv_pops hr1 hr hL10 ht hv
  rw [e, blobL_pops (fun j tc args' rets' _ htc hv' => blob_pops (hsl j) htc hv') _ 0 k3 args3 [] (by omega) t3 v3,
    daPopsW, daSymPops, List.range_eq_range']

end
end LeanVM.Guest.B1.Da
