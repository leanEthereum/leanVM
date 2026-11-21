/-
  LeanVM.Guest.B1.Eq.RsWords

  `rs_eq_run`'s body as flat blocks: its split around the remainder's dispatch, its flatness, its
  dispatch's selector, its calls and its allocation.
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Core.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `rs_eq_run`'s body, flat

Its body is flat (`rsBody = (rsA ++ rsT) ++ [ret]`, `rs_flat`): its statements are its walk's
events once the remainder's selector `σ 22` names a callee (`rs_dispOk`); its frames are
`rs_eq_run_loop0`'s and the remainder's `rs_eq_rows__L{r}` (`rs_callSF`, `rsNames_getD`), its one
allocation its chain (`rs_allocSz`). Its weight's completeness (`Ring/WeightComplete.lean`) reads
them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.Memory LeanVM.Core.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_run`'s atoms up to its chain: the count's bits, `r_g`, `q_g`, the check, the chain's
size and allocation. -/
def rsA : List Stmt := rsHead

/-- Row `0`'s stores, `rs_eq_run_loop0`'s call and the remainder's pointers. -/
def rsT0 : List Stmt := rsOnes ++
  [.atom (.const (.n 114) (word 1 0)), .atom (.add (.n 115) (.n 114) (.n 36)),
    .atom (.const (.n 116) (word 1 0)),
    .callIf (.n 115) name% «rs_eq_run_loop0» [.n 116, .n 36, .n 49, .n 0, .n 1],
    .atom (.mul (.n 117) (.n 36) (.n 36)), .atom (.mul (.n 118) (.n 117) (.n 117)),
    .atom (.mul (.n 119) (.n 118) (.n 118)), .atom (.mul (.n 120) (.n 36) (.n 36)),
    .atom (.mul (.n 121) (.n 120) (.n 120)), .atom (.mul (.n 122) (.n 121) (.n 121)),
    .atom (.mul (.n 123) (.n 122) (.n 122)), .atom (.mul (.n 124) (.n 123) (.n 123)),
    .atom (.mul (.n 125) (.n 124) (.n 124)), .atom (.mul (.n 126) (.n 49) (.n 125)),
    .atom (.mul (.n 127) (.n 0) (.n 119)), .atom (.mul (.n 128) (.n 1) (.n 119))]

/-- The remainder's dispatch. -/
def rsD : Stmt :=
  .dispatch (.n 22) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
    "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n 126, .n 127, .n 128]
    [.n 129]

/-- `rs_eq_run`'s statements after `rsA`, before its `ret`. -/
def rsT : List Stmt := rsT0 ++ [rsD, .atom (.copy (.n 130) (.n 129))]

theorem rsBody_split : rsBody = (rsA ++ rsT) ++ [.ret [.n 130]] := by
  simp only [rsBody, rsA, rsT, rsT0, List.append_assoc]; rfl

theorem rs_flat : (rsA ++ rsT).all Stmt.flat = true := by decide +kernel

theorem rs_noDispB : (rsA ++ rsT0).all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem rs_dispOk0 (σ : Val) : ∀ s ∈ rsA ++ rsT0, DispOk σ s := fun s hs ↦ by
  have := List.all_eq_true.mp rs_noDispB s hs
  cases s <;> simp_all [DispOk]

theorem rs_dispOk {σ : Val} (h : ∃ j < 8, σ (.n 22) = ofK (addressOfIndex j)) :
    ∀ s ∈ rsA ++ rsT, DispOk σ s := by
  intro s hs
  simp only [rsT, ← List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with (hs | hs) | rfl | rfl
  · exact rs_dispOk0 σ s (List.mem_append_left _ hs)
  · exact rs_dispOk0 σ s (List.mem_append_right _ hs)
  · obtain ⟨j, hj, hx⟩ := h
    exact ⟨j, by simpa using hj, by omega, hx⟩
  · trivial

theorem rs_callSF (σ : Val) : (rsA ++ rsT).filterMap (Stmt.callSF σ) =
    [(some (.n 115), name% «rs_eq_run_loop0», [.n 116, .n 36, .n 49, .n 0, .n 1], []),
      (none, ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
        "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD
          (logG (σ (.n 22))) "", [.n 126, .n 127, .n 128], [.n 129])] := rfl

theorem rs_allocSz : (rsA ++ rsT).filterMap Main.Stmt.allocSz = [(.n 49, .inr (.n 48))] := rfl

theorem rsNames_getD (r : ℕ) (hr : r < 8) :
    ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD r "" = rsEqRowsNames.getD r "" := by
  interval_cases r <;> rfl

end
end LeanVM.Guest.B1
