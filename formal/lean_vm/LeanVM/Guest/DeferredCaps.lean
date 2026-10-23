/-
  LeanVM.Guest.DeferredCaps

  `DeferredCaps`: an accepted run's openings agree in its stacked opening's caps when they agree
  in its whole run's.
-/

module

public import LeanVM.Guest.EndCompleteAssembly
public import LeanVM.Guest.B1.Whir.OsDeferred

/-!
# The opening's caps from the run's (TRIAGE #36)

`deferredCaps : DeferredCaps`: on a run `D.Ok`, the deferring verifier run on `D.proof` from the
seed's chain state passes through every phase to the stacked opening at `D.cvL`, `D.xsW`, `D.os`,
the committed root alone (`os_deferred_queries`), so the opening's query steps are among the run's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.End (bytecode bytecode_length)

@[expose] public section

/-- **The opening's caps agree when the run's do.** -/
theorem deferredCaps : DeferredCaps := by
  intro D hok hall b hb
  apply hall
  have htau : (VerifySub.layoutOf bytecode D.logMem D.rows).tableLogHeights.getD opBlake2s 0 = D.tau := by
    simp only [VerifySub.VsData.tau, VerifySub.VsData.hs]
    simp [VerifySub.layoutOf, opBlake2s]
  have hT := hok.tables (.claimed D.fresh) (by
    rw [VerifySub.layoutOf_logBytecode bytecode_length]
    exact VerifySub.bytecodeAt_claimed D.fresh bytecode)
  have hF := hok.flock (.claimed D.fresh) (VerifySub.matricesAt_claimed D.fresh)
  rw [← htau] at hF
  exact os_deferred_queries bytecode_length D.seed D.pi D.fresh hok.logMem_ge hok.logMem_le hok.rate_ge
    hok.rate_le hok.rows_length
    (fun n hn => (VerifySub.le_two_pow_log2Ceil n).trans
      (Nat.pow_le_pow_right (by decide) (by have := hok.rows_log n hn; omega)))
    hok.stack_ge hok.stack_le (x0 := D.x0) (x1 := D.x1) rfl rfl hok.gkr hT hF b hb

end
end LeanVM.Guest.B1.Main
