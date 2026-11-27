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
import LeanVM.Guest.StmtsAppend

/-!
# The loops, completely

The blocks (`LoopBlock`) of `da_verify_loop0` (blob `x`'s check, its root at `roots·x²`) and
`da_pad_loop0` (a padding blob's root), each from the memory words it reads and writes;
`loopPre_of_body` reads a block off a body checked as a block and its closing tail call.
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
      splitLoopF (pre ⧺ [.callIf c f args, .ret []]) = some (pre, c, f, args)
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
    (h : fn.body = pre ⧺ [.callIf c f args, .ret []]) (hf : pre.all Stmt.flat = true) :
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

end
end LeanVM.Guest.B1.Da
