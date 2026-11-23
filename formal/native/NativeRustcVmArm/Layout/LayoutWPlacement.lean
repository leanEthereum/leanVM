module

public import NativeRustcVmArm.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmArm.Layout.LayoutWPlacement.Exec
public import NativeRustcVmArm.Layout.Common

/-!
# `LayoutW::placement`

One environment, region 0 the column's `PlacementAt`: `b0` reads `present`; `0` (`none`) goes to
`b2`, which returns zeros (`Placement`'s default), else `b1` returns the variable count and the
index.
-/

namespace NativeRustcVmArm.Layout.LayoutWPlacement

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LayoutWPlacement
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off)

public section

/-- `Layout.placement` of a column that has a slot. -/
theorem placement_eq (L : LayoutW) {c : Nat} (hc : c < L.placements.size) :
    L.placement c = L.placements[c].getD default := by
  simp [LayoutW.placement, Array.getElem?_eq_getElem hc]

variable [Host] {k : Nat}

/-- **`LayoutW::placement`'s contract.** -/
theorem layoutWPlacement_spec (hp : Placed code k) (L : LayoutW) :
    Spec (Labels.label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L) := by
  rintro m ⟨hc, hL, hmap, hnw⟩
  have hcs : m.regs.X1.toNat < L.placements.size := by rw [hL.placements_size]; exact hc
  have hc158 : m.regs.X1.toNat < 158 := hc
  have hP := hL.placements _ hcs
  have hpl := placement_eq L hcs
  generalize L.placements[m.regs.X1.toNat] = o at hP hpl
  have hle : 24 * m.regs.X1.toNat + 144 ≤ layoutBytes := by
    simp only [layoutBytes, placementBytes, columnCountW]; omega
  have hpa : off m.regs.X0.toBitVec (120 + placementBytes * m.regs.X1.toNat) =
      m.regs.X0.toBitVec + BitVec.ofNat 64 (24 * m.regs.X1.toNat) + BitVec.ofNat 64 120 := by
    rw [off, NativeRustcVm.addr_add_add, placementBytes, Nat.add_comm]
  rw [hpa] at hP
  let env := Env.ofMachine m [(m.regs.X0.toBitVec + BitVec.ofNat 64 (24 * m.regs.X1.toNat), 144)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨NativeRustcVm.Mapped.sub hmap hle, NativeRustcVm.NoWrap.sub hnw hle⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have halias : entryAddr.eval env = env.base 0 + BitVec.ofInt 64 0 := by
    simp only [entryAddr, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, env,
      Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    have h0 : (BitVec.ofInt 64 0).toNat = 0 := by simp
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h0]
    show (m.regs.X1.toNat * (24 % 2 ^ 64) % 2 ^ 64 + m.regs.X0.toNat) % 2 ^ 64 =
      ((m.regs.X0.toNat + 24 * m.regs.X1.toNat % 2 ^ 64) % 2 ^ 64 + 0) % 2 ^ 64
    omega
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial ⟨halias, trivial⟩
  have hload : ∀ {o' : Nat} {v : UInt64}, NativeRustcVm.WordAt m.dmem
      (m.regs.X0.toBitVec + BitVec.ofNat 64 (24 * m.regs.X1.toNat) + BitVec.ofNat 64 o') v →
      env.load 0 o' 8 = v.toBitVec := fun h ↦ load_word h
  rw [show Labels.label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.LayoutWPlacement.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.LayoutWPlacement.entryOffset) NativeRustcVmArm.Vm.LayoutWPlacement.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  sym_simp at hpc
  have hx30 : env.regs .X30 = m.regs.X30.toBitVec := rfl
  cases o with
  | none =>
    have h0 : env.load 0 120 8 = 0#64 := hload hP
    simp only [h0, show (0#64 == BitVec.ofNat 64 0) = true from rfl, ↓reduceIte] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.LayoutWPlacement.b2Offset) NativeRustcVmArm.Vm.LayoutWPlacement.label_2_at] at hpc
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b0 run_b2) hwf hpc
      hm1 fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      exact hpc2.trans (retOf_of_x30 hm2 rfl hx30)
    · apply UInt64.toBitVec_inj.mp
      refine (hm2.regs .X0 _ rfl).trans ?_
      rw [hpl]
      rfl
    · apply UInt64.toBitVec_inj.mp
      refine (hm2.regs .X1 _ rfl).trans ?_
      rw [hpl]
      rfl
    · exact NativeRustcVm.SameOutside.of_eq (hm2.dmem_eq hwf rfl) _
    · exact Match.saved hm hm2 hwf rfl (by decide)
  | some p =>
    obtain ⟨h1, hvc, hix, hwvc, hwix⟩ := hP
    have h0 : env.load 0 120 8 = 1#64 := hload h1
    rw [off, NativeRustcVm.addr_add_add] at hwvc hwix
    simp only [h0, show (1#64 == BitVec.ofNat 64 0) = false from rfl, Bool.false_eq_true,
      ↓reduceIte] at hpc
    rw [NativeRustcVmArm.Vm.LayoutWPlacement.b0_length, NativeRustcVmArm.Vm.LayoutWPlacement.b0Length] at hpc
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf hpc
      hm1 fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      exact hpc2.trans (retOf_of_x30 hm2 rfl hx30)
    · apply UInt64.toBitVec_inj.mp
      refine (hm2.regs .X0 _ rfl).trans ?_
      rw [hpl]
      exact hload hwvc
    · apply UInt64.toBitVec_inj.mp
      refine (hm2.regs .X1 _ rfl).trans ?_
      rw [hpl]
      exact hload hwix
    · exact NativeRustcVm.SameOutside.of_eq (hm2.dmem_eq hwf rfl) _
    · exact Match.saved hm hm2 hwf rfl (by decide)

end

end NativeRustcVmArm.Layout.LayoutWPlacement
