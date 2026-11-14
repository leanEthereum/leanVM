/-
  LeanVM.Guest.B2C.B2Final

  B2's completeness at the deployed instance, and the guest's completeness within any budget from
  `main`'s completeness within it.
-/

module

public import LeanVM.Guest.B2C.CplSpec
public import LeanVM.Guest.B2C.B2
public import LeanVM.Guest.B2C.Cplw
public import LeanVM.Guest.B2C.FrameAll
public import LeanVM.Guest.B2C.KFacts
public import LeanVM.Guest.B2C.Chained
public import LeanVM.Guest.B2C.Chain

/-!
# B2's completeness at the deployed instance

The instance is the certificates' (`B2C.fs`, `B2C.H`, `B2C.C`, `B2C.cert`) with the counts
`B2C.cnt` (each instance's path count at each opcode, plus the jump table's `SET`s, `jtSets`).
Every compiled function runs by the kernel's completeness checks (`cplRun_all`, `Cplw.cplOk_all`),
and every running instance's frame holds what its check reads (`frameHolds_all`; the chained
`match`es' targets by `Chained.chainOk_all`, `chainApart_of`), so the honest
memory runs from `main`'s entry to the end (`b2cB2`) within the counts (`b2cCount`). With the
checker's facts (`kFactsAll`), the counts' invariance under the re-choice of temporaries
(`cntRetemp`, by `coreProgram_fresh`) and the jump table in `main`'s cells (`tableC_node`), every
piece of `End.CompleteParts` but `main`'s completeness is proved:

`guest_complete_b2c : MainComplete fs cert cnt b → GuestCompleteWithin b`, for every budget `b`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.End (mainEntry GuestCompleteWithin MainComplete Budget)

@[expose] public section

/-- **Every compiled function runs** (`B2Hyps.run`), from the kernel's completeness checks. -/
theorem cplRun_all : ∀ j, 1 ≤ j → j < nFns → CplRun j := cplRun_of_ok Cplw.cplOk_all

/-- **B2's hypotheses**: every function runs, and every running instance's frame holds what the
check reads (the call sites of a path apart, by the completeness checks). -/
theorem b2Hyps : B2Hyps := ⟨cplRun_all, frameHolds_all (sitesApart_all_of Cplw.cplOk_all)
  fun j h1 h2 ↦ chainApart_of (Cplw.cplOk_all j h1 h2) (End.winOk_of h1 h2) (Chained.chainOk_all j h1 h2)⟩

/-- **B2**: the honest memory runs from `main`'s entry to the end. -/
theorem b2cB2 : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guestProgram (honest coreProgram fs H C hdr T) ⟨addressOfIndex mainEntry, 1⟩ (Registers.final guestProgram) :=
  b2_complete b2Hyps

/-- **B2, counted**: a run of the honest memory to the end is within the counts. -/
theorem b2cCount : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guestProgram (honest coreProgram fs H C hdr T) n Registers.initial = some (Registers.final guestProgram) →
        ∀ op, (⟨_, honest coreProgram fs H C hdr T, n⟩ : Execution guestProgram).opcodeCount op ≤ cnt T op :=
  b2_count b2Hyps

/-- **Every piece of completeness but `main`'s**, at the deployed instance. -/
theorem completeParts_b2c {b : Budget} (hm : MainComplete fs cert cnt b) :
    End.CompleteParts fs H C cert cnt b where
  main := hm
  kfacts := kFactsAll
  cntRetemp := cntRetemp coreProgram_fresh
  table := fun _ _ _ _ ht ↦ tableC_node ht
  b2 := b2cB2
  count := b2cCount

/-- **The guest's completeness within a budget `b`, from `main`'s completeness within it** at the
deployed frame sizes and certificate cells: `NodeRelation` within the limits, the caps agreeing, no zero
challenge where the guest divides and the node within `b` give a valid execution of the guest on
the statement's digest of committed size at most `2^30`. -/
theorem guest_complete_b2c {b : Budget} (hm : MainComplete fs cert cnt b) : GuestCompleteWithin b :=
  End.guest_complete_of_parts (completeParts_b2c hm)

end
end LeanVM.Guest.B2C
