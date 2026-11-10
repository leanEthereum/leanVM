import Rv64Verifier.Proofs.Bus.VbbTail68

/-!
# `verify_bus_balance`'s side loop: one iteration

The fold's step is the block loop's fold over all blocks and the side's total (`accAt_side`); one
iteration from the head (`sideStage`): the selectors (`sideFront`), the shifted fingerprints
(`sideShift`), `known` (`sideDot`), into the block loop (`blkEnter`), all blocks (`blkLoop`,
`Blk.tl`), the tail (`sideTail`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts

theorem blkFold_all (point : List E) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (forms : List (List Form)) :
    blkFold point i sd forms (min sd.2.1.tables.length sd.1.length) =
      ((tbSel sd point).zip sd.1).foldl (busBlockStepRust point i sd.2.2.2.1 sd.2.2.2.2)
        (forms, 0) := by
  simp only [blkFold]
  rw [List.take_of_length_le (by simp [tbSel, List.length_zip])]

theorem accAt_side (s : MachineState) (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E)
    {i : ℕ} (hi : i < 3) :
    accAt s k state mem mf bf bv (i + 1) =
      ((blkFold state.point i ((sidesOf s k state mem mf bf bv).getD i noSide)
          (accAt s k state mem mf bf bv i).1
          (min ((sidesOf s k state mem mf bf bv).getD i noSide).2.1.tables.length
            ((sidesOf s k state mem mf bf bv).getD i noSide).1.length)).1,
        (accAt s k state mem mf bf bv i).2 ++
          [sideTot ((sidesOf s k state mem mf bf bv).getD i noSide) state.point state.values i
            (blkFold state.point i ((sidesOf s k state mem mf bf bv).getD i noSide)
              (accAt s k state mem mf bf bv i).1
              (min ((sidesOf s k state mem mf bf bv).getD i noSide).2.1.tables.length
                ((sidesOf s k state mem mf bf bv).getD i noSide).1.length)).2]) := by
  rw [accAt_succ s k state mem mf bf bv hi, blkFold_all]
  rfl

/-- One iteration of the side loop. -/
theorem sideStage (hT : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    (hEA : EqAboveSpec) (hD : DotSpec) (hC : BlkCallees) (hG : GrowOneFreshSpec 0x80011c78 24 8)
    (bev : MachineState → Word → List E → Option E) : SideStage bev := by
  intro s z w v h₀ h k state mem mf bf bv i hpre C hi hpc hx22 Sd
  have hsz : heapNext s ≤ heapNext z := C.fps.inv.mono
  have Ih := Sd.inv
  have hzh := Sd.mat.mono
  have SO := sideOk hpre C Sd hi
  obtain ⟨u, hru, hd | ⟨pcu, F⟩⟩ :=
    sideFront hT hR hEA hpre hsz Ih hzh (sideEnv hpre C Sd) SO (pointAt hpre C Sd) hi hx22 hpc
  · exact ⟨u, hru, Or.inl hd⟩
  obtain ⟨w', hrw, hd | ⟨q, pcw, S⟩⟩ := sideShift hT hR hpre hsz Ih hzh SO F pcu
  · exact ⟨w', hru.trans hrw, Or.inl hd⟩
  obtain ⟨t, hrt, hd | ⟨pct, D⟩⟩ := sideDot hD hpre hsz Ih F S pcw
  · exact ⟨t, hru.trans (hrw.trans hrt), Or.inl hd⟩
  have tl : ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ (t'.pc = 0x80007b24 ∧
      ∃ e, Tl s z h e t' i ((sidesOf s k state mem mf bf bv).getD i noSide) state.point
        (w.getReg .x23) (w.getReg .x25).toNat (accAt s k state mem mf bf bv i).1
        (accAt s k state mem mf bf bv i).2)) := by
    obtain ⟨e, hre, ⟨pce, hm, En, X, B⟩ | ⟨pce, -, T⟩⟩ := blkEnter hpre C Sd SO F D hi pct
    · obtain ⟨t', hr', hd | ⟨B', pc'⟩⟩ := blkLoop hC hpre hsz (hPb_of C) Ih hzh En
        (min ((sidesOf s k state mem mf bf bv).getD i noSide).2.1.tables.length
          ((sidesOf s k state mem mf bf bv).getD i noSide).1.length - 1) 0 e (by omega) B pce
      · exact ⟨t', hre.trans hr', Or.inl hd⟩
      · exact ⟨t', hre.trans hr', Or.inr ⟨pc', e, Blk.tl hpre Ih En X B'⟩⟩
    · exact ⟨e, hre, Or.inr ⟨pce, e, T⟩⟩
  obtain ⟨t', hrt', hd | ⟨pc', e, T⟩⟩ := tl
  · exact ⟨t', hru.trans (hrw.trans (hrt.trans hrt')), Or.inl hd⟩
  obtain ⟨h', hrh, hd | ⟨Sd', hpc'⟩⟩ := sideTail hG hpre C Sd hi T pc'
  · exact ⟨h', hru.trans (hrw.trans (hrt.trans (hrt'.trans hrh))), Or.inl hd⟩
  refine ⟨h', hru.trans (hrw.trans (hrt.trans (hrt'.trans hrh))), Or.inr ⟨?_, hpc'⟩⟩
  rw [accAt_side s k state mem mf bf bv hi]
  exact Sd'

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
