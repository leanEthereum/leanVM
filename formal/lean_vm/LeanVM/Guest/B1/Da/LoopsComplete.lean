/-
  LeanVM.Guest.B1.Da.LoopsComplete

  The DA loops, completely: each block holds on the words an honest run leaves in memory, so each
  loop runs to its end.
-/

module

public import LeanVM.Guest.B1.Da.LoopsCChk
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.BlobChk
public import LeanVM.Guest.B1.Da.Help
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.Value.KeccakConst
public import LeanVM.Guest.Data.NameStrings

/-!
# The loops, completely

The blocks (`LoopBlock`) of `da_verify_loop0` (blob `x`'s check, its root at `roots·x²`) and
`da_pad_loop0` (a padding blob's root), each from the memory words it reads and writes;
`loopPre_of_body` reads a block off a body checked as a block and its closing tail call.
`cellL_rel`: a blob's cell loop `da_verify_blob_loop0`, bounded by the constant `g^128`, runs from
every counter to its end when each cell's block holds (`CellBlk`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-! ## Blocks off bodies -/

theorem splitLoopF_append {c : V} {f : String} {args : List V} :
    ∀ pre : List Stmt, pre.all Stmt.flat = true →
      splitLoopF (pre ++ [.callIf c f args, .ret []]) = some (pre, c, f, args)
  | [], _ => rfl
  | [s], h => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h
    simp [splitLoopF, h]
  | s :: t :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := splitLoopF_append (c := c) (f := f) (args := args) (t :: rest)
      (by simp only [List.all_cons, Bool.and_eq_true]; exact h.2)
    obtain ⟨u, rest', hu⟩ : ∃ u rest', rest ++ [Stmt.callIf c f args, Stmt.ret []] = u :: rest' := by
      cases rest <;> exact ⟨_, _, rfl⟩
    simp only [List.cons_append, hu] at ih ⊢
    rw [show splitLoopF (s :: t :: u :: rest') = if Stmt.flat s then
        (splitLoopF (t :: u :: rest')).map (fun p => (s :: p.1, p.2)) else none from rfl,
      ite_pos' h.1, ih]
    rfl

theorem loopPre_of_body {fn : Fn} {pre : List Stmt} {c : V} {f : String} {args : List V}
    (h : fn.body = pre ++ [.callIf c f args, .ret []]) (hf : pre.all Stmt.flat = true) :
    loopPre fn = pre := by
  simp [loopPre, h, splitLoopF_append pre hf]

theorem find_blobL : coreProgram.find? name% «da_verify_loop0» = some (coreProgram.getD
    idx% «da_verify_loop0» default) :=
  find_of_idx dv_loops_idx.1

theorem find_padL : coreProgram.find? name% «da_pad_loop0» = some (coreProgram.getD
    idx% «da_pad_loop0» default) :=
  find_of_idx dv_loops_idx.2

/-! ## The blocks -/

set_option maxRecDepth 20000 in
/-- **Blob `x`** (`da_verify_loop0`): its check on the weights, its root at `roots·x²`. -/
theorem blobL_block {x N w roots b0 b1 : E} (hc : coreProgram.Rel rd "da_verify_blob" [w] [b0, b1])
    (h0 : LoadHolds rd (roots * (x * x)) 0 b0) (h1 : LoadHolds rd (roots * (x * x)) 1 b1) :
    LoopBlock rd (coreProgram.getD idx% «da_verify_loop0» default) x N [w, roots] := by
  obtain ⟨⟨hs, hl⟩, -, -⟩ := dv_loops_shape
  refine ⟨Val.ofArgs [x, N, w, roots, b0, b1, x * x, roots * (x * x), word 2 0, x * word 2 0,
    x * word 2 0 + N, word 2 0, x * word 2 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body dv_loops_body.1 (by decide)]
  intro st hst
  simp only [blobLPre, stepAtC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, and_true]
  exacts [hc, h0, h1]

set_option maxRecDepth 20000 in
/-- **A padding blob's root** (`da_pad_loop0`) at `roots·n_blob²·x²`. -/
theorem padL_block {x N roots nb : E}
    (h0 : LoadHolds rd (roots * (nb * nb) * (x * x)) 0 (digestHalves daPadBlobDigest).1)
    (h1 : LoadHolds rd (roots * (nb * nb) * (x * x)) 1 (digestHalves daPadBlobDigest).2) :
    LoopBlock rd (coreProgram.getD idx% «da_pad_loop0» default) x N [roots, nb] := by
  obtain ⟨-, ⟨hs, hl⟩, -⟩ := dv_loops_shape
  have e := daPadBlob_cells
  simp only [Prod.ext_iff] at e
  rw [← e.1] at h0
  rw [← e.2] at h1
  refine ⟨Val.ofArgs [x, N, roots, nb, nb * nb, roots * (nb * nb), x * x,
    roots * (nb * nb) * (x * x), word 8002054802297438051 4108169256045952147,
    word 12830724869163462953 1721925254677230945, word 2 0, x * word 2 0,
    x * word 2 0 + N, word 2 0, x * word 2 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body dv_loops_body.2.1 (by decide)]
  intro st hst
  simp only [padLPre, stepAtC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  exacts [h0, h1]

/-! ## A blob's cell loop -/

/-- **Cell `k`'s block's words**: the cell's check on `weights[k]`, the running sum's step at
`base·g^k` (words `512`, `513`), the digest at the leaf `base·g^(2k)`. -/
def CellBlk (rd : Reader) (w base : E) (k : ℕ) : Prop :=
  ∃ lv d0 d1 s prev : E, coreProgram.Rel rd "da_verify_cell" [lv] [d0, d1, s] ∧
    LoadHolds rd (w * gen ^ k) 0 lv ∧ LoadHolds rd (base * gen ^ k) 512 prev ∧
    LoadHolds rd (base * gen ^ k) 513 (prev + s) ∧
    LoadHolds rd (base * (gen ^ k * gen ^ k)) 0 d0 ∧ LoadHolds rd (base * (gen ^ k * gen ^ k)) 1 d1

set_option maxRecDepth 20000 in
/-- **One cell**: the loop at `g^k` runs when its block's words hold and, unless `k + 1 = 128`,
the loop at `g^(k+1)` runs. -/
theorem cellL_step {w base : E} {k : ℕ} (hk : k < 128) (hb : CellBlk rd w base k)
    (hn : k + 1 < 128 → coreProgram.Rel rd name% «da_verify_blob_loop0» [gen ^ (k + 1), w, base] []) :
    coreProgram.Rel rd name% «da_verify_blob_loop0» [gen ^ k, w, base] [] := by
  obtain ⟨lv, d0, d1, s, prev, hc, h1, h2, h3, h4, h5⟩ := hb
  have hpar := dv_loops_shape.2.2
  refine (rel_iff_sem find_c _ _).mpr ⟨Val.ofArgs [gen ^ k, w, base, w * gen ^ k, lv, d0, d1, s,
    base * gen ^ k, prev, prev + s, gen ^ k * gen ^ k, base * (gen ^ k * gen ^ k), word 2 0,
    gen ^ k * word 2 0, word 325 0, gen ^ k * word 2 0 + word 325 0, word 2 0, gen ^ k * word 2 0],
    by rw [hpar]; rfl, ?_⟩
  rw [dv_loops_body.2.2, cellLBody, holdsList_append]
  refine holdsList_flat_of cellLPre (by decide) _ _ (fun st hst => ?_) ?_
  · simp only [cellLPre, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
      List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, and_true]
    exacts [h1, hc, h2, h3, h4, h5]
  · have hg : word 2 0 = gen := by rw [show (2 : ℕ) = 2 ^ 1 from rfl, word_two_pow (by norm_num), pow_one]
    simp only [Stmt.HoldsList, Stmt.Holds, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero,
      List.map_cons, List.map_nil, hg, word_g128, gen_pow_mul_gen]
    refine ⟨gen_pow_add_isInK _ _, fun hne => ?_, trivial⟩
    exact hn (by
      by_contra hc'
      exact hne (by rw [show k + 1 = 128 by omega]; exact e_add_eq_zero_iff.mpr rfl))

/-- **A blob's cell loop runs** from every counter `k < 128` to its end, each cell's block holding. -/
theorem cellL_rel {w base : E} (hb : ∀ k < 128, CellBlk rd w base k) :
    ∀ k < 128, coreProgram.Rel rd name% «da_verify_blob_loop0» [gen ^ k, w, base] [] := by
  have key : ∀ t k, k + 1 + t = 128 →
      coreProgram.Rel rd name% «da_verify_blob_loop0» [gen ^ k, w, base] [] := by
    intro t
    induction t with
    | zero => exact fun k hk => cellL_step (by omega) (hb k (by omega)) fun h => absurd h (by omega)
    | succ t ih => exact fun k hk => cellL_step (by omega) (hb k (by omega)) fun _ => ih (k + 1) (by omega)
  exact fun k hk => key (128 - k - 1) k (by omega)

end
end LeanVM.Guest.B1.Da
