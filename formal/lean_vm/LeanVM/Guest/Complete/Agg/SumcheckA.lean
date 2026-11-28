module

public import LeanVM.Guest.Complete.LeafA
public import LeanVM.Guest.Complete.PureA
public import LeanVM.Guest.Complete.AggFree
public import LeanVM.Guest.B1.Sumcheck.Batch
import LeanVM.Guest.CoreRef

/-!
# `batch_sumcheck__L25`, placed

The batching sumcheck's core body is atoms then a `ret`: it allocates nothing, takes no
`frameAddr`, and reads only its rounds (`50` words at its sixth argument) and writes its point
(`25` words at its eighth), `loadOkB [(5, 50), (7, 25)]` by the kernel. So it is a pure straight
leaf, and its layout-free completeness places it at every position (`agg_bs_callCompletesA`, by
`callCompletesA_of_loadOk`), loading from those two arrays.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VsC

@[expose] public section

theorem find_bs : coreProgram.find? "batch_sumcheck__L25" = some fn% «batch_sumcheck__L25» :=
  coreProgram_find?_at (j := idx% «batch_sumcheck__L25») rfl

theorem bs_pureIn : coreProgram.PureIn ["batch_sumcheck__L25"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_bs] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

theorem bs_not_loop : coreProgram.loop "batch_sumcheck__L25" = false := by decide +kernel

/-- **The batching sumcheck completes placed** at every position, on nine arguments whose sixth
points to the rounds and eighth to the point, on memories where its meaning holds: block its
frame, ending at its cursor, loading from those `50` and `25` cells, popping nothing, every node
exact. -/
theorem agg_bs_callCompletesA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    (hwf : coreProgram.Wf) (k : ℕ) {args rets : List E} (hlen : args.length = 9) {bm bp : ℕ}
    (hm : args.getD 5 0 = ptrAt bm) (hp : args.getD 7 0 = ptrAt bp) {Pre : Reader → Prop}
    (hpre : ∀ rd, Pre rd → MeaningBatchSumcheck 25 rd args rets) :
    CallCompletesA fs al cert k "batch_sumcheck__L25" args rets (argRegion args [(5, 50), (7, 25)])
      (fun _ _ _ => False) (fun _ => True) Pre FreePost :=
  callCompletesA_of_loadOk bs_pureIn List.mem_cons_self bs_not_loop find_bs (by rw [hlen]; rfl)
    (by decide +kernel) (by decide +kernel)
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [hlen])
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨bm, hm⟩
      · exact ⟨bp, hp⟩)
    (callCompletes0_free hwf agg_bs_free.1 agg_bs_free.2 fun rd _ hp' =>
      (batch_sumcheck_holds rd args rets).mpr (hpre rd hp'))

end
end LeanVM.Guest.Complete.Agg
