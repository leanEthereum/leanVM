/-
  LeanVM.Guest.B2C.RunsConsec

  The deployed certificates' frame runs hold their values in consecutive cells
  (`B1.RunsConsec cert`), from the sharing check's lists (`FnStatic.run`).
-/

module

public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B1.Bits.QueryWindowsAt

/-!
# The deployed frame runs, consecutive

The sharing check confirms, once per function, that value `k` of a frame run sits `k` cells past
the run's first (`FnStatic.run`), so the deployed certificates meet `B1.RunsConsec`, the fact
`decode_query_windows`' placed form reads of its run's tails (`B1.qwDecodeAtD_holds`). A module
of its own, so the placed proofs never import the certificates.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Every deployed frame run's cells are consecutive.** -/
theorem runsConsec : B1.RunsConsec cert := by
  intro f fn hf p r rs hm k hk
  obtain ⟨j, hj, hc, -, hcert⟩ := idx_of_find hf
  have FS := fnStatic_of hj
  rw [← hc, blockAtoms_eq] at hm
  rw [hcert, hcert]
  exact (FS.run p r rs hm k hk).2.1

end
end LeanVM.Guest.B2C
