import Rv64Verifier.Proofs.Pcs.VsoWords

/-!
# `verify_stacked_opening`'s level loop: what the opening keeps for the rows

From the fold rounds' end `t` to the slices: the level's folds (`Vec<E>` at `S - 640`) and the heap
allocated before `t` are kept (`Merkled.keep`, `Slices.keep`), for `eq_kernel` at `0x8000b13c`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A doubleword of the level folds' header, or of the heap allocated before `t`. -/
def OldAt (s t : MachineState) (y : Word) : Prop :=
  (s.getReg .x2 - 640).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat ∨
    heapNext s ≤ y.toNat ∧ y.toNat + 8 ≤ heapNext t

/-- **The opening, the queries, `lam` and the Merkle checks keep `OldAt`.** -/
theorem Merkled.keep {s : MachineState} {x : LCtx} {h t u v w m : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs) {y : Word}
    (hy : OldAt s t y) : m.getMem y = t.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hIf := hpre.self.free
  simp only [Outside] at hIf
  obtain ⟨T0, hl⟩ := hm.lo
  have m1 := hm.op.mono
  have m2 := hm.qo.mono
  have m3 := hl.mono
  have m4 := hm.mo.mono
  have hhi := (hm.mo.inv.heap hpre.heap).hi
  simp only [OldAt] at hy
  have e1 : u.getMem y = t.getMem y := hm.op.fr y fun i hi hw ↦ by
    rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;>
      rcases hy with hy | hy <;> first
      | addr_omega [hw, hi, hy, hb, hhi, m1, m2, m3, m4]
      | addr_omega [hw, hi, hy, hb, hnx, hhi, m1, m2, m3, m4]
      | (simp only [W] at hw
         rcases hIf.1 with h' | h' <;>
           addr_omega [hw, hi, hy, hS, hIs, hb, h', hhi, m1, m2, m3, m4])
  have e2 : v.getMem y = u.getMem y := hm.qo.fr y fun i hi hw ↦ by
    rcases hw with (hw | hw | hw | hw) | (hw | hw | hw | hw | hw | hw | hw) <;>
      rcases hy with hy | hy <;> first
      | addr_omega [hw, hi, hy, hb, hhi, m1, m2, m3, m4]
      | addr_omega [hw, hi, hy, hb, hnx, hhi, m1, m2, m3, m4]
      | (simp only [W] at hw
         rcases hIf.1 with h' | h' <;>
           addr_omega [hw, hi, hy, hS, hIs, hb, h', hhi, m1, m2, m3, m4])
  have e3 : w.getMem y = v.getMem y := hl.fr y fun i hi hw ↦ by
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;>
      rcases hy with hy | hy <;> first
      | addr_omega [hw, hi, hy, hb, hhi, m1, m2, m3, m4]
      | addr_omega [hw, hi, hy, hb, hnx, hhi, m1, m2, m3, m4]
      | (rcases hIf.1 with h' | h' <;>
           addr_omega [hw, hi, hy, hS, hIs, hb, h', hhi, m1, m2, m3, m4])
  have e4 : m.getMem y = w.getMem y := hm.mo.fr y fun i hi hw ↦ by
    rcases hw with (hw | hw | hw) | ((hw | hw | hw | hw) | hw | hw | hw) <;>
      rcases hy with hy | hy <;> first
      | addr_omega [hw, hi, hy, hb, hhi, m1, m2, m3, m4]
      | addr_omega [hw, hi, hy, hb, hnx, hhi, m1, m2, m3, m4]
      | (rcases hIf.1 with h' | h' <;>
           addr_omega [hw, hi, hy, hS, hIs, hb, h', hhi, m1, m2, m3, m4])
  rw [e4, e3, e2, e1]

/-- **The slices keep `OldAt`.** -/
theorem Slices.keep {s t m t' : MachineState} (hpre : VsoPre s) (hsl : Slices s m t')
    (htm : heapNext t ≤ heapNext m) {y : Word} (hy : OldAt s t y) : t'.getMem y = m.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hsl.heap.hi
  have hmo := hsl.mono
  simp only [OldAt] at hy
  exact hsl.fr y fun i hi hw ↦ by
    rcases hw with hw | hw | hw | hw | hw <;> rcases hy with hy | hy <;> first
      | addr_omega [hw, hi, hy, hb, hhi, hmo, htm]
      | addr_omega [hw, hi, hy, hb, hnx, hhi, hmo, htm]

end Rv64Verifier.Proofs.Pcs.Vso
