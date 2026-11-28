module

public import LeanVM.Guest.Complete.LeafA
public import LeanVM.Guest.Complete.PureA
public import LeanVM.Guest.Complete.OfRel
import LeanVM.Guest.CoreRef

/-!
# `statement_digest`, placed

`statement_digest`'s core body is atoms then a `ret`: its two `StackBuf`s are frame cells, it
takes no `frameAddr` and allocates nothing, and it reads only its last argument's `26` deferred
cells (`loadOkB [(8, 26)]`, by the kernel). So it is a pure straight leaf, and its layout-free
completeness places it at every position, loading from the deferred cells
(`statement_digest_callCompletesA`, by `callCompletesA_of_loadOk`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VsC

@[expose] public section

theorem statement_digest_pureIn : coreProgram.PureIn ["statement_digest"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [Digest.find_statement_digest] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

theorem statement_digest_not_loop : coreProgram.loop "statement_digest" = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem statement_digest_free : NoWitG "statement_digest" ∧ ExactFreeG "statement_digest" :=
  free_of (by decide +kernel : freeAt "statement_digest" idx% «statement_digest» = true)

/-- **`statement_digest` completes placed** at every position, on nine arguments whose last points
to the deferred cells, on memories where its meaning holds: block its frame, ending at its cursor,
loading from the `26` cells at its last argument, popping nothing, every node exact. -/
theorem statement_digest_callCompletesA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    (hwf : coreProgram.Wf) (k : ℕ) {args rets : List E} (hlen : args.length = 9) {b : ℕ}
    (hb : args.getD 8 0 = ptrAt b) {Pre : Reader → Prop}
    (hm : ∀ rd, Pre rd → Digest.MeaningStatementDigest rd args rets) :
    CallCompletesA fs al cert k "statement_digest" args rets (argRegion args [(8, 26)]) (fun _ _ _ => False)
      (fun _ => True) Pre FreePost :=
  callCompletesA_of_loadOk statement_digest_pureIn List.mem_cons_self statement_digest_not_loop
    Digest.find_statement_digest (by rw [hlen]; rfl) (by decide +kernel) (by decide +kernel)
    (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp [hlen])
    (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact ⟨b, hb⟩)
    (callCompletes0_free hwf statement_digest_free.1 statement_digest_free.2 fun rd _ hp =>
      Digest.statement_digest_complete rd args rets (hm rd hp))

end
end LeanVM.Guest.Complete
