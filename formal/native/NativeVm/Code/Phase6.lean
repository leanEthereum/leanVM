module

public import NativeVm.Code.Phase6.Run

/-!
# Phase 6: `KECCAK`'s validity by GKR

The code of `Model.keccakPhase`, proved against it (`phase6_ok : Phase6Ok phase6`).

Phase 6 keeps its working values in the scratch region, seen as elements of `E`
(`NativeVm.Code.P6.Scr`, the layout `Phase6/Lay.lean`), `rbp` at the scratch. `setupC` points `rbp`
there and writes the constant tables (`Phase6/Tables.lean`); `runC` copies `KECCAK`'s point and
output lanes in (`Phase6/First*.lean`), samples the segment and lane challenges, reads the committed
outputs' claim, builds the first claim, runs the `KECCAK_DEPTH` layers (`Phase6/Layer*.lean`), the
two openings, the last sumcheck and the final check (`Phase6/Tail.lean`, `Phase6/Open*.lean`), and
writes `KeccakOutAt` and the committed outputs' column claim (`Phase6/Out*.lean`). Until the results
are written, the code writes only the scratch (`rs6`), so the column claims survive; the whole phase
writes only its regions (`rsAll`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Code.P6

/-- **Phase 6**: `KECCAK`'s validity by GKR. -/
def phase6 : Stmt := blk [blk setupC, blk runC]

/-- **Phase 6 computes `keccakPhase`.** -/
theorem phase6_ok : Phase6Ok phase6 := by
  intro env inp t s0 layout rate ev acc hc hin hlay hev hcl hacc
  have hacc' : acc.size < claimCap := by
    rw [claimCap_val]; unfold busClaimCount publicClaimCount at hacc; rw [tableClaimCount_val] at hacc
    omega
  apply runs_of_refines
  refine Refines.pre_blk (P' := fun t' s ↦ ∃ g, St env s0 g t' s ∧ Cn g)
    (fun t' s ⟨ht, hs⟩ ↦ by subst ht hs; exact setup_spec hin hc) ?_
  intro t' s ⟨g, hst, hcn⟩
  exact WP.mono (run_refines env inp s0 hin hlay hev hcl hacc' g hcn t' s hst)
    (fun _ ⟨r, t'', hr, h1, h2, h3⟩ ↦ ⟨r, t'', hr, h1, h2, h3⟩)
    (fun _ ⟨hr, hk⟩ ↦ ⟨hr, kept_all hk⟩)

/-- info: 'NativeVm.Code.phase6_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase6_ok

end NativeVm.Code
