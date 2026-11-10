import Rv64Verifier.Proofs.Bus.VbbTail65

/-!
# `verify_bus_balance`'s side loop: the side's total

The tree's values at `S - 1280`, below `z`'s `NEXT` (`treeAt`); the total's limbs as the code XORs
them (`total_eq`); `0x80007480` pushes the total and the next side's head holds the invariant
(`pushTot`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The tree's values, at any state of the iteration from the head `h`. -/
theorem treeAt {bev : MachineState → Word → List E → Option E} {s z w v h₀ h t : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} {P : Word} {n : Nat}
    {acc : List (List Form) × List E} {i : Nat} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (Sd : Sides s z h₀ h P n acc)
    (Ct : Cur s z h t) (hi : i < 3) :
    t.getMem (s.getReg .x2 - 1280) = vecPtr z (s.getReg .x2 - 176) ∧
      HeapArr (vecPtr z (s.getReg .x2 - 176)) 3 ∧ (vecPtr z (s.getReg .x2 - 176)).toNat + 72 ≤
        heapNext z ∧
      eAt t (vecPtr z (s.getReg .x2 - 176) + BitVec.ofNat 64 (24 * i)) = state.values.getD i 0 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have Ih := Sd.inv
  have hzh := Sd.mat.mono
  have stZH := (C.rows1.step.trans C.setup.step).trans Sd.step
  have hz1280 : h.getMem (s.getReg .x2 - BitVec.ofNat 64 1280) =
      z.getMem (s.getReg .x2 - BitVec.ofNat 64 1280) :=
    stZH.slot' hpre (by omega) (by omega) fun y hy hy' ↦ by
      simp only [RowsW, SetupW, LoopW] at hy'
      rcases hy' with ((hy' | hy' | hy') | (hy' | hy')) | (hy' | hy' | hy' | hy' | hy' | hy' | hy' |
        hy') <;> addr_omega [hy, hy', hb1]
  have ht1280 : t.getMem (s.getReg .x2 - BitVec.ofNat 64 1280) =
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 1280) :=
    Ct.slot hpre (by omega) (by omega) fun y hy hy' ↦ by
      simp only [SlotW] at hy'
      rcases hy' with hy' | hy' | hy' | hy' | hy' | hy' | hy' <;> addr_omega [hy, hy', hb1]
  have F := C.fps
  have NV := F.values
  have hl := NV.vec.len
  have hb := NV.buf
  have he := NV.elems
  simp only [vecEs] at he
  have h3 : (vecLen z (s.getReg .x2 - 176)).toNat = 3 := by
    rw [← C.vlen, ← he, eListAt_length]
  have hlo := hpre.heap.lo
  have hzE := F.inv.heap.hi
  have hsz := F.inv.mono
  simp only [NewBuf] at hb
  rw [h3] at hl
  have hb' : heapNext s ≤ (vecPtr z (s.getReg .x2 - 176)).toNat ∧
      (vecPtr z (s.getReg .x2 - 176)).toNat + 72 ≤ heapNext z := by
    rcases hb.2 with h0 | h0
    · omega
    · exact ⟨h0.1, by omega⟩
  refine ⟨(ht1280.trans hz1280).trans F.valuesPtr, ⟨hb.1, le_trans hlo hb'.1, by
    have := hb'.2; simp only [heapNext, heapEnd] at this hzE ⊢; omega⟩, hb'.2, ?_⟩
  rw [← he, h3, eListAt_getD _ _ hi]
  have hk := heapKeptZ hpre C Sd
  have w (j : Nat) (hj : j + 8 ≤ 24) :
      t.getMem (vecPtr z (s.getReg .x2 - 176) + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) =
        z.getMem (vecPtr z (s.getReg .x2 - 176) + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) := by
    have b1 := hb'.1
    have b2 := hb'.2
    simp only [heapStart, heapNext, heapEnd] at b1 b2 hzE hsz hlo
    rw [Ct.low hpre Ih hzh (by simp only [heapStart]; addr_omega [b1, b2, hi, hj, hzE, hlo])
      (by simp only [heapNext]; addr_omega [b1, b2, hi, hj, hzE])]
    exact hk _ (by simp only [heapNext]; addr_omega [b1, b2, hi, hj, hzE, hsz, hlo])
      (by simp only [heapNext]; addr_omega [b1, b2, hi, hj, hzE])
  exact eAt_congr (by simpa using w 0 (by omega)) (w 8 (by omega)) (w 16 (by omega))

theorem SideW.loopW {s z u : MachineState} (hu : HeapOk u) {a : Word} (ha : SideW s z u a) :
    LoopW s z a := by
  have hE := hu.hi
  rcases ha with ha | ⟨a1, a2⟩
  · simp only [SlotW] at ha
    simp only [LoopW]
    rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by omega⟩))))))

/-- The total as the code XORs its limbs. -/
theorem total_eq (r0 r1 r2 o0 o1 o2 k0 k1 k2 t0 t1 t2 : Word) :
    eOf3 ((((r0 ^^^ o0) ^^^ k0) ^^^ t0) ^^^ 1) (((o1 ^^^ r1) ^^^ k1) ^^^ t1)
      (((o2 ^^^ r2) ^^^ k2) ^^^ t2) =
      eOf3 t0 t1 t2 + eOf3 k0 k1 k2 + (eOf3 o0 o1 o2 + 1) + eOf3 r0 r1 r2 := by
  rw [eOf3_xor1, eOf3_xor, eOf3_xor, BitVec.xor_comm o1 r1, BitVec.xor_comm o2 r2, eOf3_xor,
    sideTotal_code]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
