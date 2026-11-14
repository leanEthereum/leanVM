/-
  LeanVM.Guest.Backend.Sound.Guest

  The back end's correctness at the aggregation guest, given that the back end compiles the
  guest's source to the statement's bytecode.
-/

module

public import LeanVM.Guest.Backend.Sound.Main
public import LeanVM.Guest.Data.Source
public import Statement.LeanVmGuest

/-!
# At the guest

`GuestCompiles` is the one equation between the back end and the statement's data: the back end
compiles the guest's source (`Data.guest`) to the functions of `Statement/Data/`
(`Data.functions`), padded to `2^19` slots. `lake exe guest-backend check` evaluates it, compiled,
and finds it true; it is test evidence, not a theorem, because `Backend.compile` is not
kernel-evaluable (its `Std` maps) and nothing else proves an equation between two programs of
460,073 instructions. It is stated here so that the theorem below names exactly what a proof of
it, or a kernel-checked certificate of it, would give.

`guest_program_sound`: given it, on a memory where a run of the statement's `guestProgram` from
`(g^0, 1)` halts, `main`'s core body holds at frame `1` under the valuation by places, for the
core program the back end's own front end gives (`ExpandTrace.expandProgram Data.guest`). The
proofs of `formal/lean_vm` are about `coreProgram`, which is that program with its values
renumbered (`Guest/CoreData.lean`); carrying the theorem across the renumbering is not done.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The back end compiles the guest to the statement's bytecode.** -/
def GuestCompiles (traced : List TracedFn) (fns : List Lowered) (slots : Array KVal) : Prop :=
  ExpandTrace.expandProgram Data.guest = .ok traced ∧ lowerProgram traced = .ok (fns, slots) ∧
    (assemble fns slots).toFunctions = Data.functions ∧ (assemble fns slots).size = 2 ^ 19

/-- The guest as a compiled program on a memory. -/
def guestWorld {κ : ℕ} (traced : List TracedFn) (fns : List Lowered) (slots : Array KVal)
    (L : MemoryImage κ) (U : String → List E → Prop) : World κ :=
  ⟨traced, fns, slots, 19, by decide, L, U⟩

theorem guestWorld_prog {κ : ℕ} {traced : List TracedFn} {fns : List Lowered} {slots : Array KVal}
    (h : GuestCompiles traced fns slots) (L : MemoryImage κ) (U : String → List E → Prop) :
    (guestWorld traced fns slots L U).prog = guestProgram := by
  simp only [World.prog, Assembled.program, guestWorld, h.2.2.1]
  rfl

/-- **(d) At the guest**: given `GuestCompiles`, every function's placement sound and every
function's obligations holding, a halting run of the statement's `guestProgram` from `(g^0, 1)`
makes `main`'s core body hold at frame `1`. -/
theorem guest_program_sound {κ : ℕ} {traced : List TracedFn} {fns : List Lowered}
    {slots : Array KVal} (h : GuestCompiles traced fns slots) (L : MemoryImage κ) (hκ : κ < 64)
    (U : String → List E → Prop)
    (hpl : ∀ tf ∈ traced, (guestWorld traced fns slots L U).PlacedSoundly tf)
    (hobl : ∀ tf ∈ traced, (guestWorld traced fns slots L U).Obligations tf)
    (hU : ∀ tf ∈ traced, tf.core.name = "main" → U "main" (frameWords L 1 2 (sigOf tf).1))
    {k : ℕ} (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) :
    (guestWorld traced fns slots L U).MainHolds :=
  program_sound_of (W := guestWorld traced fns slots L U) ⟨h.2.1, h.2.2.2⟩ hκ hpl hobl hU
    (guestWorld_prog h L U ▸ hs)

end
end LeanVM.Guest.Backend
