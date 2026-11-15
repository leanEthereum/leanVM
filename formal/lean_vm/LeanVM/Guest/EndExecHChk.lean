/-
  LeanVM.Guest.EndExecHChk

  The kernel's checks of the deployed guest's advised buffers: no `allocAdvice` outside five
  functions, and those five's advised buffer indices.
-/

module

public import LeanVM.Guest.Bridge.AllocAdv
public import LeanVM.Guest.Bridge.AllocCur
public import LeanVM.Guest.Memory.HeapSlots

/-!
# The advised buffers, checked

`noAdv_all`: no compiled function but `main`, `claim_list_digest`, `da_verify`, `verify_sub` and
`verify_tables` has an `allocAdvice` hint. `advAt_main` and the rest: the indices, among those five's
buffer hints, of their `allocAdvice`s (`advAt`) are `heapSlots`' of their names; `idx_main` and the
rest name their compiled indices.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (fnAl adviceOf isAdv bufsOf allocHints)

@[expose] public section

/-- The indices, from `k`, of the advised hints among buffer hints (`EndExec.advIdx`, which needs the
alignment track's imports). -/
def advAtFrom : ℕ → List (ℕ × Prover.Exec.Hint) → List ℕ
  | _, [] => []
  | k, q :: l => if isAdv q.2 then k :: advAtFrom (k + 1) l else advAtFrom (k + 1) l

/-- The indices of the advised hints among buffer hints. -/
def advAt (l : List (ℕ × Prover.Exec.Hint)) : List ℕ := advAtFrom 0 l

theorem idx_main : B2C.idxOf "main" = some (fn_idx% «main») := by decide +kernel
theorem idx_cld : B2C.idxOf "claim_list_digest" = some (fn_idx% «claim_list_digest») := by decide +kernel
theorem idx_dv : B2C.idxOf "da_verify" = some (fn_idx% «da_verify») := by decide +kernel
theorem idx_vs : B2C.idxOf "verify_sub" = some (fn_idx% «verify_sub») := by decide +kernel
theorem idx_vt : B2C.idxOf "verify_tables" = some (fn_idx% «verify_tables») := by decide +kernel

/-- The compiled indices of the functions with advised buffers. -/
def advFns : List ℕ :=
  [fn_idx% «main», fn_idx% «claim_list_digest», fn_idx% «da_verify», fn_idx% «verify_sub»,
    fn_idx% «verify_tables»]

/-- **No other compiled function has an `allocAdvice` hint.** -/
theorem noAdv_all : ∀ j < nFns, j ∉ advFns → (allocHints (adviceOf j)).all (fun q ↦ !isAdv q.2) = true := by
  decide +kernel

theorem advAt_main : advAt (bufsOf (fnAl (fn_idx% «main»)).X (fnAl (fn_idx% «main»)).d) = heapSlots "main" := by
  decide +kernel

theorem advAt_cld : advAt (bufsOf (fnAl (fn_idx% «claim_list_digest»)).X (fnAl (fn_idx% «claim_list_digest»)).d) =
    heapSlots "claim_list_digest" := by
  decide +kernel

theorem advAt_dv : advAt (bufsOf (fnAl (fn_idx% «da_verify»)).X (fnAl (fn_idx% «da_verify»)).d) =
    heapSlots "da_verify" := by
  decide +kernel

theorem advAt_vs : advAt (bufsOf (fnAl (fn_idx% «verify_sub»)).X (fnAl (fn_idx% «verify_sub»)).d) =
    heapSlots "verify_sub" := by
  decide +kernel

theorem advAt_vt : advAt (bufsOf (fnAl (fn_idx% «verify_tables»)).X (fnAl (fn_idx% «verify_tables»)).d) =
    heapSlots "verify_tables" := by
  decide +kernel

end

end LeanVM.Guest.EndExec
