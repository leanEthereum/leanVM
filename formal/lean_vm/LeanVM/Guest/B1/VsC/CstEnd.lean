/-
  LeanVM.Guest.B1.VsC.CstEnd

  `check_stack_terminal`'s callees' ends, bounded when every frame is small.
-/

module

public import LeanVM.Guest.B1.VsC.RingRowsA
public import LeanVM.Guest.B1.VsC.EqChainA
public import LeanVM.Guest.B1.VsC.EndBnd
import LeanVM.Guest.ValRef

/-!
# `check_stack_terminal`'s callees' ends, bounded

`rs_eq_run`'s (`rsEnd`) and `ring_rows`' (`rgEnd`) ends within `2^21` of their cursors on counts up to
`40`, `eq_prefix_chain`'s (`epcEnd`) within `2^17`, every frame below `2^16`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool}

theorem rsEnd_le (hfs : FsSmall fs) {count : ℕ} (h : count ≤ 40) (c : ℕ) : rsEnd fs al count c ≤ c + 2 ^ 21 := by
  have a1 := allocBase_le (al name% «rs_eq_run_loop0») (c + 64 * (count / 8 + 2))
  have b1 := llBlk_le hfs name% «rs_eq_run_loop0» (count / 8) 0
  have l1 := llEnd_le (al := al) hfs "rs_eq_rows__L8" (count / 8) 0
    (allocBase (al name% «rs_eq_run_loop0») (c + 64 * (count / 8 + 2)) + llBlk fs name% «rs_eq_run_loop0» (count / 8) 0)
  have s1 := step_le hfs (al (rsEqRowsNames.getD (count % 8) "")) (rsEqRowsNames.getD (count % 8) "")
    (llEnd fs al "rs_eq_rows__L8" (count / 8) 0
      (allocBase (al name% «rs_eq_run_loop0») (c + 64 * (count / 8 + 2)) + llBlk fs name% «rs_eq_run_loop0» (count / 8) 0))
  simp only [rsEnd]
  omega

theorem rgEnd_le (hfs : FsSmall fs) {count : ℕ} (h : count ≤ 40) (c : ℕ) : rgEnd fs al count c ≤ c + 2 ^ 21 := by
  have a1 := allocBase_le (al name% «ring_rows_loop0») c
  have b1 := llBlk_le hfs name% «ring_rows_loop0» (count / 8) 0
  have l1 := llEnd_le (al := al) hfs "rs_eq_rows_all__L8" (count / 8) 0
    (allocBase (al name% «ring_rows_loop0») c + llBlk fs name% «ring_rows_loop0» (count / 8) 0)
  have s1 := step_le hfs (al (rsEqRowsAllNames.getD (count % 8) "")) (rsEqRowsAllNames.getD (count % 8) "")
    (llEnd fs al "rs_eq_rows_all__L8" (count / 8) 0
      (allocBase (al name% «ring_rows_loop0») c + llBlk fs name% «ring_rows_loop0» (count / 8) 0))
  simp only [rgEnd]
  omega

theorem epcEnd_le (hfs : FsSmall fs) (n c : ℕ) : epcEnd fs al n c ≤ c + 2 ^ 17 :=
  step_le hfs _ _ c

end
end LeanVM.Guest.B1.VsC
