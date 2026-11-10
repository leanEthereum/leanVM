import Rv64Verifier.Proofs.Walk.AtR17

/-!
# `walk`'s contract, assembled

`walk_spec_of`: the front (entry to `0x800035f0`, `AtR17`, or an `Err` return, or a dead end)
and the tail (from `AtR17` to the return, or a dead end) give `WalkSpec OI`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Protocol.Compile Rv64Verifier.Model

theorem walk_spec_of {OI : MachineState → Word → List (List Opening) → Prop}
    (hFront : ∀ s, s.pc = 0x80000ef8 → WalkPre s → ∃ u, Reaches Image.code s u ∧
      ((∃ layout rows lir bus, AtR17 OI s u layout rows lir bus) ∨ Done OI s u ∨
        Dead Image.code u))
    (hTail : ∀ s u (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64)) (lir : BitVec 64)
      (bus : BusResultRust), WalkPre s → AtR17 OI s u layout rows lir bus →
      ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t)) :
    WalkSpec OI := by
  intro s hpc hpre
  obtain ⟨u, hr, ⟨layout, rows, lir, bus, h⟩ | hd | hd⟩ := hFront s hpc hpre
  · obtain ⟨t, hr', ht | ht⟩ := hTail s u layout rows lir bus hpre h
    · exact ⟨t, hr.trans hr', Or.inl ht⟩
    · exact ⟨t, hr.trans hr', Or.inr ht⟩
  · exact ⟨u, hr, Or.inl hd⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Walk
