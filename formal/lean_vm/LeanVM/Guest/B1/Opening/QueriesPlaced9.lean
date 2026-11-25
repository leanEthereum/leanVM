/-
  LeanVM.Guest.B1.Opening.QueriesPlaced9

  `opening_queries`' body in pieces: its start, its loop's call, its end.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced8
import LeanVM.Guest.StmtsAppend

/-!
# The function's body in pieces

`oqMainT_eq`: the body is its start (`oqMainA`), the loop's call (`oqCallArgs`), its end
(`oqMainEnd`: the chain's end read, or `0` at the final level) and its return (`oqMainRet`).
`oqMainRest`: the end's honest values. `fn_loop_main`: the function is no loop.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem fn_loop_main {P : Program} {s : Oq} {name loop : String} {fm : Fn}
    (hfm : P.find? name = some fm) (hbm : fm.body = oqMainT s loop) :
    P.loop name = false := by
  rw [Program.loop_of_find? hfm, Fn.loop, hbm]
  unfold oqMainT
  by_cases hf : s.final = 1 <;> simp [hf]

/-- The loop's call's arguments: its start and guard, the positions and windows (at level 0
moved past the odd query), the caller's pointers, the chain, `λ⁻¹`. -/
def oqCallArgs (s : Oq) : List V :=
  [.n (oqMK s + 2), .n oqMN, .n (if s.base = 1 then oqMK s - 2 else oqMPos),
    .n (if s.base = 1 then oqMK s - 1 else oqMQp), .n oqMCap, .n oqMFlags, .n oqMCoefs, .n oqMHs, .n 11,
    .n oqMLamInv]

/-- The function's tail after its loop: the chain's end read and returned, or (final level) `0`. -/
def oqMainEnd (s : Oq) (k : ℕ) : List Stmt :=
  if s.final = 1 then [.atom (.const (.n (k + 3)) (word 0 0))]
  else [.atom (.mul (.n (k + 3)) (.n 11) (.n oqMN)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
    .atom (.copy (.n (k + 5)) (.n (k + 4)))]

/-- The function's returned value. -/
def oqMainRet (s : Oq) (k : ℕ) : ℕ := if s.final = 1 then k + 3 else k + 5

/-- The function's values after `1, 1 + nG, 1`: `0`, or the chain's end's pointer and value. -/
def oqMainRest (s : Oq) (ch nG hN : E) : List E :=
  if s.final = 1 then [word 0 0] else [ch * nG, hN, hN]

theorem oqMainT_eq (s : Oq) (loop : String) :
    oqMainT s loop = oqMainA s ++ (.callIf (.n (oqMK s + 1)) loop (oqCallArgs s) ::
      (oqMainEnd s (oqMK s) ⧺ [.ret [.n (oqMainRet s (oqMK s))]])) := by
  unfold oqMainT oqMainEnd oqMainRet oqCallArgs
  by_cases hf : s.final = 1 <;> simp [hf]

theorem oqMainEnd_atoms (s : Oq) (k : ℕ) : AllAtoms (oqMainEnd s k) := by
  unfold oqMainEnd
  split
  · exact allAtoms_cons allAtoms_nil
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))

theorem oqMainEnd_flatM (s : Oq) (k : ℕ) : (oqMainEnd s k).all Stmt.flatM = true := by
  unfold oqMainEnd; split <;> rfl

theorem oqMainEnd_allocSz (s : Oq) (k : ℕ) : (oqMainEnd s k).filterMap Stmt.allocSz = [] := by
  unfold oqMainEnd; split <;> rfl

theorem oqMainEnd_addrS (s : Oq) (k : ℕ) : (oqMainEnd s k).filterMap Stmt.addrS = [] := by
  unfold oqMainEnd; split <;> rfl

end
end LeanVM.Guest.B1
