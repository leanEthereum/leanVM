import Rv64Verifier.Proofs.Bus.VbbTail27

/-!
# `verify_bus_balance` past the GKR loop: the way into the side loop

`restToSides` with the empty buffers' pointers (`Ptrs`): the point's and each claim's point's lie
below `NEXT` (`PtrLo`, carried from their allocation), every form of the forms' rows holds the
dangling pointer `8` (`RowOk.cells`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript
  Rv64Verifier.MultilinearContracts Rv64Verifier.FieldContracts

/-- `Ptrs` from the stages' facts. -/
theorem ptrsOf {bev : MachineState → Word → List E → Option E} {s z w v : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    (F : Fps bev s z k state mem mf bf bv) (R1 : Rows1 s z w v) :
    Ptrs s z v (w.getReg .x23) (w.getReg .x25).toNat := by
  refine ⟨F.pointLo, fun i hi ↦ ?_, fun i hi j hj ↦ ?_⟩
  · have h5 : (z.getMem (s.getReg .x2 - 824)).toNat = 5 := by rw [F.len]; rfl
    have hl : i < (allClaims s state mem mf bf).length := by
      rw [← F.claims.claims.len, h5]; exact hi
    exact (F.claims.claims.claims i hl).lo
  · rw [((R1.rows i hi).cells j hj).2.2]
    have := R1.inv.heap.lo
    simp only [heapStart] at this
    show 8 ≤ heapNext v
    omega

/-- **The way into the side loop.** -/
theorem sidesEntry (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) (hA : AllocSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hI : IndexMleSpec) (hC : SliceConcatSpec)
    {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E}
    (hB : Vbb.BytecodeEvalSpec BcOk bev) (hBT : BcTransfer BcOk bev)
    (hP : PowSpec) (hF : FingerprintsSpec)
    (hR : ReserveFreshSpec 0x80004aec 24 8) (hCl : Layout.Clone.CloneCapsSpec) :
    SidesEntry BcOk bev := by
  intro s q k state mem mf bf hpre hbc Sc hpc
  obtain ⟨h, hr, hd | hd | ⟨z, w, v, bv, F, R, R1, K, hpch, S⟩⟩ :=
    restToSides hT hM hA hG hI hC hB hBT hP hF hR hCl hpre hbc Sc hpc
  · exact ⟨h, hr, Or.inl hd⟩
  · exact ⟨h, hr, Or.inr (Or.inl hd)⟩
  exact ⟨h, hr, Or.inr (Or.inr ⟨z, w, v, bv, ⟨F, R, R1, K, S, ptrsOf F R1, Sc.len⟩, hpch⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
