import Rv64Verifier.Sym.Api
import Rv64Verifier.Frame

/-!
# Reading a block's expectation

The generated blocks (`scripts/Gen.lean`) state every register and every written doubleword of a
block's final state. `Expect.reg x r` is register `r`'s final expression and `Expect.Holds.reg`
its value; `Expect.Holds.memAt` reads the `i`-th written doubleword. `BlockSpec.reaches` turns a
block into a `Reaches` step for `Frame`'s contracts.
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

/-- Register `r`'s final expression in `x`, `.reg r` if `x` does not list it. -/
def Expect.reg (x : Expect) (r : Reg) : E :=
  ((x.regs.find? fun p ↦ Reg.beqN p.1 r).map Prod.snd).getD (.reg r)

theorem Expect.Holds.reg {x : Expect} {s t : MachineState} (h : x.Holds s t) (r : Reg)
    (hr : (x.regs.find? fun p ↦ Reg.beqN p.1 r).isSome = true) :
    t.getReg r = (x.reg r).eval s := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hr
  have hmem := List.mem_of_find?_eq_some hp
  have hr' : p.1 = r := Reg.beqN_eq (by simpa using List.find?_some hp)
  rw [Expect.reg, hp, Option.map_some, Option.getD_some, ← hr']
  exact h.2.1 p hmem

/-- The `i`-th doubleword `x` reads back from the final memory. -/
theorem Expect.Holds.memAt {x : Expect} {s t : MachineState} (h : x.Holds s t) (i : Nat)
    (hi : i < x.mem.length) : t.getMem ((x.mem[i]).1.eval s) = (x.mem[i]).2.eval s :=
  h.2.2.1 _ (List.getElem_mem hi)

theorem Expect.Holds.pc {x : Expect} {s t : MachineState} (h : x.Holds s t) : t.pc = x.pc.eval s :=
  h.1

theorem Expect.Holds.frame {x : Expect} {s t : MachineState} (h : x.Holds s t) (a : Word)
    (ha : ∀ k ∈ x.writes, a ≠ k.eval s) : t.getMem a = s.getMem a :=
  h.2.2.2 a ha

theorem BlockSpec.reaches {code : Code} {entry : Word} {k : Nat} {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop} (h : BlockSpec code entry k P Q) {s : MachineState}
    (hpc : s.pc = entry) (hP : P s) : ∃ t, Reaches code s t ∧ Q s t :=
  let ⟨t, ht, hq⟩ := h s hpc hP
  ⟨t, ⟨k, ht⟩, hq⟩

end Rv64Verifier.Sym
