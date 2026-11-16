/-
  LeanVM.Guest.Backend.Guest.Cpl.WholeCore
  Whole-program completeness at the guest from a run of its core IR: the compiled guest runs on
  the honest memory of the run, its temporaries re-chosen.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgramCoreDone
public import LeanVM.Guest.Backend.Guest.Cpl.Whole

/-!
# Whole-program completeness at the guest from a core run

`guest_core_complete` is `program_complete_core` at `W0`, the guest compiled by the back end
(`W0_compiled`), every function passing the per-function conditions (`guestConds`), counting no
arms separately. Its hypotheses are the run of the guest's core IR only.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The guest is complete through the back end from a run of its core IR**: for every run `T`
of `main` on a memory `M`, its free values where the back end puts them, loading from its own data
or the public input `hdr`, of at most `2^30` words and its equations in the memory, its
temporaries re-chosen, the compiled guest runs on the honest memory from `main`'s entry at frame
`g^0` to the final registers, within each running instance's placed path maxima summed over the
call tree. -/
theorem guest_core_complete : ∀ (hdr : E × E) (T : Tree)
    (M : MemoryImage (logMem (T.total W0.fsB))), T.name = "main" →
    T.Valid W0.core M.read [] [] → T.BufsOk W0.core →
    T.Placed W0.core W0.fsB W0.cellB 0 → T.LoadsIn W0.core W0.fsB W0.cellB (fun i => i < 2) 0 →
    M.read (addressOfIndex 0) = some hdr.1 → M.read (addressOfIndex 1) = some hdr.2 →
    T.total W0.fsB ≤ 2 ^ 30 →
    (∀ q ∈ T.eqns W0.core, ∃ i : Fin (2 ^ logMem (T.total W0.fsB)), q.1 = addressOfIndex i) →
    ∃ ν : ℕ → String → Val → V → E, ∃ c : Opcode → ℕ,
      RunC W0.prog (W0.honestB hdr (T.retemp W0.core W0.fsB ν 0))
        ⟨addressOfIndex (W0.ent "main"), 1⟩ (Registers.final W0.prog) c ∧
      ∀ op, c op ≤ W0.progCost (fun _ => false) (T.retemp W0.core W0.fsB ν 0) op :=
  Complete.program_complete_core W0 W0_compiled guestConds (fun _ => false)

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_core_complete
