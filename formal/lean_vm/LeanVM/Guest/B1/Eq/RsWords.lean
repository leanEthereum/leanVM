/-
  LeanVM.Guest.B1.Eq.RsWords

  `rs_eq_run`'s body, read for its words (it has no words certificate: its dispatch).
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«rs_eq_run»
import LeanVM.Guest.Value.FieldBits
import LeanVM.Guest.StmtsAppend

/-!
# `rs_eq_run`'s body

Its body is flat (`rsBody = rsPre0 ++ rsD :: [copy, ret]`), so its walk's events are its statements' (the dispatch `rsD` names a callee, `rs_dispOk`) and its frames are `rs_eq_run_loop0`'s and
the remainder's `rs_eq_rows__L{r}` (`rs_callSF`, `rsCalls`); its one `HeapBuf` is the chain (`rs_allocSz`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_run`'s statements before its `ret`. -/
def rsPre : List Stmt := rsA ⧺ (rsAlloc ++ (rsInits ++ rsT))

/-- Its statements before the remainder's dispatch. -/
def rsPre0 : List Stmt := rsA ⧺ (rsAlloc ++ (rsInits ++ (rsG ++ rsT0)))

theorem rsBody_split : rsBody = rsPre ⧺ [.ret [.n (val% «rs_eq_run» "s12#0")]] := by
  simp only [rsBody, rsPre, List.append_assoc]

theorem rsPre_eq : rsPre = rsPre0 ++ [rsD, .atom (.copy (.n (val% «rs_eq_run» "s12#0")) (.n (val% «rs_eq_run» "last")))] := by
  simp only [rsPre, rsPre0, rsT, List.append_assoc]

theorem rs_flat : rsPre.all Stmt.flat = true := by decide +kernel

theorem rsA_atoms : rsA.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem rs_noDispB : rsPre0.all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem rs_dispOk0 (σ : Val) : ∀ s ∈ rsPre0, DispOk σ s := fun s hs ↦ by
  have := List.all_eq_true.mp rs_noDispB s hs
  cases s <;> simp_all [DispOk]

theorem rs_dispOk {σ : Val} (h : ∃ j < 8, σ (.n (val% «rs_eq_run» "r_g@3")) = ofK (addressOfIndex j)) :
    ∀ s ∈ rsPre, DispOk σ s := by
  intro s hs
  rw [rsPre_eq] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hs | rfl | rfl
  · exact rs_dispOk0 σ s hs
  · obtain ⟨j, hj, hx⟩ := h
    exact ⟨j, by simpa using hj, by omega, hx⟩
  · trivial

theorem rs_callSF (σ : Val) : rsPre.filterMap (Stmt.callSF σ) =
    [(some (.n (val% «rs_eq_run» "s8#1")), name% «rs_eq_run_loop0», [.n (val% «rs_eq_run» "s8#2"), .n (val% «rs_eq_run» "q_g@3"), .n (val% «rs_eq_run» "chain"), .n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1")], []),
      (none, ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
        "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD
          (logG (σ (.n (val% «rs_eq_run» "r_g@3")))) "", [.n (val% «rs_eq_run» "row"), .n (val% «rs_eq_run» "last~1"), .n (val% «rs_eq_run» "last~2")], [.n (val% «rs_eq_run» "last")])] := rfl

theorem rs_allocSz : rsPre.filterMap Main.Stmt.allocSz =
    [(.n (val% «rs_eq_run» "chain"), .inr (.n (val% «rs_eq_run» "chain~7")))] := rfl

/-- `rs_eq_run`'s frames: `rs_eq_run_loop0`'s (entered unless `q = 0`), the remainder's. -/
noncomputable def rsCalls (σ : Val) : List Call :=
  [⟨name% «rs_eq_run_loop0», [.n (val% «rs_eq_run» "s8#2"), .n (val% «rs_eq_run» "q_g@3"), .n (val% «rs_eq_run» "chain"), .n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1")], [], decide (σ (.n (val% «rs_eq_run» "s8#1")) ≠ 0)⟩,
    ⟨["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD (logG (σ (.n (val% «rs_eq_run» "r_g@3")))) "",
      [.n (val% «rs_eq_run» "row"), .n (val% «rs_eq_run» "last~1"), .n (val% «rs_eq_run» "last~2")], [.n (val% «rs_eq_run» "last")], true⟩]

theorem rsNames_getD (r : ℕ) (hr : r < 8) :
    ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD r "" = rsEqRowsNames.getD r "" := by
  interval_cases r <;> rfl

variable {fs : String → ℕ}

end
end LeanVM.Guest.B1
