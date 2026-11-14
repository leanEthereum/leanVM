/-
  LeanVM.Guest.Backend.Guest.World

  The back end's correctness at the aggregation guest, for `coreProgram`, given that the back end
  compiles the guest to the statement's bytecode.
-/

module

public import LeanVM.Guest.Backend.Guest.Traced
public import LeanVM.Guest.Backend.Sound.Main
public import LeanVM.Guest.CoreData
public import Statement.LeanVmGuest

/-!
# The guest's world

The back end's input for the guest, `guestTraced`, is `coreProgram`'s function `j` with entry `j`
of `GuestData.guestInfo` (`Guest/Traced.lean`, written by `lake exe guest-traced`): the allocation
trace of its expansion, every value renamed as `coreProgram` names it, its return cells and its
`loopSource`. So the core program of the guest's world is `coreProgram` by construction
(`guestWorld_core`), and no theorem about renumbering is needed: the back end's correctness holds
for any traced program it accepts, whatever the trace.

`GuestCompiles fns slots` is the one equation between the back end and the statement's data: the
back end compiles `guestTraced` to the labelled functions `fns` and jump table slots `slots`, which
assemble to the functions of `Statement/Data/` (`Data.functions`), padded to `2^19` slots.
`lake exe guest-traced --check` evaluates it, compiled, and finds it true.

`guest_program_sound`: given it and every function's obligations, on a memory where a run of the
statement's `guestProgram` from `(g^0, 1)` halts, `main`'s core body, `coreProgram`'s first
function, holds at frame `1` under the valuation by places, its calls located.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestData

@[expose] public section

/-- **The back end's input for the guest**: `coreProgram`'s functions, each with its trace, its
return cells and its `loopSource`. -/
noncomputable def guestTraced : List TracedFn :=
  (coreProgram.zip guestInfo).map fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

/-- **The back end's input for the guest has `coreProgram`'s functions.** -/
theorem guestTraced_core : guestTraced.map (·.core) = coreProgram := by
  rw [guestTraced, List.map_map]
  exact List.map_fst_zip (by rw [coreProgram_length, guestInfo_length])

/-- **The guest as a compiled program on a memory**: the back end's input `guestTraced`, its
output `fns` and `slots`, padded to `2^19` slots, a memory `L` and the preconditions `U` its
callers are asked for. -/
noncomputable def guestWorld {κ : ℕ} (fns : List Lowered) (slots : Array KVal) (L : MemoryImage κ)
    (U : String → List E → Prop) : World κ :=
  ⟨guestTraced, fns, slots, 19, by decide, L, U⟩

/-- **The back end compiles the guest to the statement's bytecode.** -/
def GuestCompiles (fns : List Lowered) (slots : Array KVal) : Prop :=
  lowerProgram guestTraced = .ok (fns, slots) ∧ (assemble fns slots).toFunctions = Data.functions ∧
    (assemble fns slots).size = 2 ^ 19

variable {κ : ℕ} {fns : List Lowered} {slots : Array KVal} {L : MemoryImage κ}
  {U : String → List E → Prop}

theorem guestWorld_p : (guestWorld fns slots L U).p = guestTraced := rfl

/-- **The guest's world has `coreProgram` as its core program.** -/
theorem guestWorld_core : (guestWorld fns slots L U).core = coreProgram := guestTraced_core

theorem guestWorld_compiled (h : GuestCompiles fns slots) : (guestWorld fns slots L U).Compiled :=
  ⟨h.1, h.2.2⟩

theorem guestWorld_prog (h : GuestCompiles fns slots) :
    (guestWorld fns slots L U).prog = guestProgram := by
  simp only [World.prog, Assembled.program, guestWorld, h.2.1]
  rfl

/-- **At the guest**: given `GuestCompiles` and every function's obligations, a halting run of the
statement's `guestProgram` from `(g^0, 1)` makes `main`'s core body hold at frame `1`. -/
theorem guest_program_sound (h : GuestCompiles fns slots) (hκ : κ < 64)
    (hobl : ∀ tf ∈ guestTraced, (guestWorld fns slots L U).Obligations tf)
    (hU : ∀ tf ∈ guestTraced, tf.core.name = "main" → U "main" (frameWords L 1 2 (sigOf tf).1))
    {k : ℕ} (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) :
    (guestWorld fns slots L U).MainHolds :=
  program_sound (W := guestWorld fns slots L U) (guestWorld_compiled h) hκ hobl hU
    (guestWorld_prog h ▸ hs)

end
end LeanVM.Guest.Backend
