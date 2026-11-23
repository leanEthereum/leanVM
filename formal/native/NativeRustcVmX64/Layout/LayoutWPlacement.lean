module

public import NativeRustcVmX64.Layout.LayoutWPlacement.Exec
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement.Names

/-!
# `LayoutW::placement` on x86-64

One environment, region 0 the `144` bytes ending in the column's `PlacementAt`: `b0` reads
`present`; `0` (`none`) goes to `b2`, which returns zeros (`Placement`'s default), else `b1`
returns the variable count and the index. Neither writes memory; the `ret`s run from `retS`
(`leaf_ret`).
-/

namespace NativeRustcVmX64.Layout.LayoutWPlacement

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LayoutWPlacement
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off)
open NativeRustcVmX64.Transcript (after after_eq exec_after infix_of infix_take infix_drop)

public section

/-- `Layout.placement` of a column that has a slot. -/
theorem placement_eq (L : LayoutW) {c : Nat} (hc : c < L.placements.size) :
    L.placement c = L.placements[c].getD default := by
  simp [LayoutW.placement, Array.getElem?_eq_getElem hc]

theorem toBitVec_toUInt64_zero : (0 : Nat).toUInt64.toBitVec = 0#64 := rfl

variable [Host] {k : Nat}

/-- **`LayoutW::placement`'s contract.** -/
theorem layoutWPlacement_spec (hp : Placed code k) (L : LayoutW) :
    Spec (Labels.label NativeRustcVmX64.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L) := by
  rintro m ⟨hst, hc, hL, hmap, hnw⟩
  have hcs : (reg m .rsi).toNat < L.placements.size := by rw [hL.placements_size]; exact hc
  have hc158 : (reg m .rsi).toNat < 158 := hc
  have hP := hL.placements _ hcs
  have hpl := placement_eq L hcs
  generalize L.placements[(reg m .rsi).toNat] = o at hP hpl
  have hle : 24 * (reg m .rsi).toNat + 144 ≤ layoutBytes := by
    simp only [layoutBytes, placementBytes, columnCountW]; omega
  set c := (reg m .rsi).toNat with hcdef
  set ea := reg m .rdi + BitVec.ofNat 64 (24 * c) with hea
  have hpa : ∀ j, off (reg m .rdi) (120 + placementBytes * c + j) = ea + BitVec.ofNat 64 (120 + j) := by
    intro j
    rw [off, hea, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 120 + placementBytes * c + j = 24 * c + (120 + j) by simp only [placementBytes]; omega]
  let env := Env.ofMachine m [(ea, 144)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨NativeRustcVm.Mapped.sub hmap hle, NativeRustcVm.NoWrap.sub hnw hle⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have halias : entryAddr.eval env = env.base 0 + BitVec.ofInt 64 0 := by
    rw [show env.base 0 = ea from rfl, Transcript.ofInt_zero64, BitVec.add_zero, hea]
    simp only [entryAddr, raxS, Sym.eval, BinOp.apply, low_W64, ext_W64, env,
      Env.ofMachine_regs]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hcdef, NativeRustcX64.reg,
      show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl, Nat.reducePow, Nat.reduceMod]
    omega
  have halias2 : rcxS.eval env = env.base 0 + BitVec.ofInt 64 120 := by
    have h := halias
    rw [Transcript.ofInt_zero64, BitVec.add_zero] at h
    rw [show rcxS.eval env = BitVec.ofNat 64 120 + entryAddr.eval env by
      simp [rcxS, Sym.eval, BinOp.apply], h, BitVec.add_comm]
    congr 1
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨halias, halias2, trivial⟩
  have hload : ∀ {j : Nat} {v : UInt64}, NativeRustcVm.WordAt m.dmem
      (off (reg m .rdi) (120 + placementBytes * c + j)) v → env.load 0 (120 + j) 8 = v.toBitVec :=
    fun h ↦ Arrays.load_word (by rw [hpa] at h; exact h)
  have hload0 : ∀ {v : UInt64}, NativeRustcVm.WordAt m.dmem
      (off (reg m .rdi) (120 + placementBytes * c)) v → env.load 0 120 8 = v.toBitVec :=
    fun h ↦ hload (j := 0) h
  rw [show Labels.label NativeRustcVmX64.Vm.LayoutWPlacement.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.LayoutWPlacement.b0Offset) from hp.label NativeRustcVmX64.Vm.LayoutWPlacement.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st hm1 hpc ↦ ?_
  obtain ⟨hk1, hmem1, hsp1⟩ := after_eq run_b0 ▸ ok_b0
  have hd1 : st.data.dmem = m.dmem := hm1.dmem_eq hwf hmem1
  have hs1 : Saved m st.data := Match.saved hm hm1 hwf rfl hk1
  have hrsp1 : rspOf st.data = rspOf m := hm1.regs .rsp _ hsp1
  have hret1 : ∀ i < 8, st.data.dmem.get? (rspOf m + BitVec.ofNat 64 i) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 i) := fun _ _ ↦ by rw [hd1]
  simp only [PcOk] at hpc
  obtain ⟨hT, hF⟩ := Arrays.pc_cond hpc
  cases o with
  | none =>
    have h0 : env.load 0 120 8 = 0#64 := hload0 hP
    have hc : SBool.eval env (.cmp .eq .W64 (.load 0 120 8) (.lit 0)) = true := by
      rw [Arrays.eval_cmp_eq, Arrays.eval_load, Arrays.eval_lit, h0]; rfl
    have hpc2 := hT hc
    rw [hp.label NativeRustcVmX64.Vm.LayoutWPlacement.label_1_at] at hpc2
    refine Eventually.mono (leaf_retS (infix_of b2_in_code (by simp [b2]) hp) run_b2
      (after_eq run_b2 ▸ ok_b2).1 (after_eq run_b2 ▸ ok_b2).2.1 hst hpc2 hs1 hrsp1 hret1
      (Q := fun d ↦ reg d .rax = 0#64 ∧ reg d .rdx = 0#64 ∧ d.dmem = m.dmem)
      fun d hr hd ↦ ⟨(hr .rax _ (after_eq run_b2 ▸ ok_b2).2.2.1).trans rfl,
        (hr .rdx _ (after_eq run_b2 ▸ ok_b2).2.2.2).trans rfl, hd.trans hd1⟩)
      fun s ⟨h1, h2, ⟨ha, hd, hdm⟩, h4⟩ ↦
      ⟨h1, h2, ?_, ?_, fun q _ ↦ by rw [hdm], h4⟩
    · rw [ha, hpl]; rfl
    · rw [hd, hpl]; rfl
  | some p =>
    obtain ⟨h1, hvc, hix, hwvc, hwix⟩ := hP
    have h0 : env.load 0 120 8 = 1#64 := hload0 h1
    have hc : ¬SBool.eval env (.cmp .eq .W64 (.load 0 120 8) (.lit 0)) = true := by
      rw [Arrays.eval_cmp_eq, Arrays.eval_load, Arrays.eval_lit, h0]; decide
    have hpc2 := hF hc
    rw [NativeRustcVmX64.Vm.LayoutWPlacement.b0_length] at hpc2
    rw [NativeRustcVm.Transcript.off_off] at hwvc hwix
    refine exec_at (infix_of ((infix_take b1 4).trans b1_in_code (by simp [b1]))
      (by simp [b1]) hp) run_b1a hwf nofun (hpc2.trans (congrArg Host.addrOf (by rw [← NativeRustcVmX64.Vm.LayoutWPlacement.b0_length, Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.LayoutWPlacement.b0_next)))
      hm1 fun st2 hm2 hpc3 ↦ ?_
    obtain ⟨hk2, hmem2, hsp2, hax2, hdx2⟩ := after_eq run_b1a ▸ ok_b1a
    have hd2 : st2.data.dmem = m.dmem := hm2.dmem_eq hwf hmem2
    have hs2 : Saved m st2.data := Match.saved hm hm2 hwf rfl hk2
    have hrsp2 : rspOf st2.data = rspOf m := hm2.regs .rsp _ hsp2
    have hax : reg st2.data .rax = p.variableCount.toUInt64.toBitVec :=
      (hm2.regs .rax _ hax2).trans (hload (j := 8) hwvc)
    have hdx : reg st2.data .rdx = p.index.toUInt64.toBitVec :=
      (hm2.regs .rdx _ hdx2).trans (hload (j := 16) hwix)
    simp only [PcOk] at hpc3
    refine Eventually.mono (leaf_retS (infix_of ((infix_drop b1 4).trans b1_in_code (by simp [b1]))
      (by simp [b1]) hp) run_b1r (after_eq run_b1r ▸ ok_b1r).1
      (after_eq run_b1r ▸ ok_b1r).2.1 hst
      (hpc3.trans (congrArg Host.addrOf (by have : (b1.take 4).length = 4 := rfl; omega)))
      hs2 hrsp2
      (fun _ _ ↦ by rw [hd2])
      (Q := fun d ↦ reg d .rax = reg st2.data .rax ∧ reg d .rdx = reg st2.data .rdx ∧
        d.dmem = m.dmem)
      fun d hr hd ↦ ⟨(hr .rax _ (after_eq run_b1r ▸ ok_b1r).2.2.1).trans rfl,
        (hr .rdx _ (after_eq run_b1r ▸ ok_b1r).2.2.2).trans rfl, hd.trans hd2⟩)
      fun s ⟨h1, h2, ⟨ha, hd, hdm⟩, h4⟩ ↦ ⟨h1, h2, ?_, ?_, fun q _ ↦ by rw [hdm], h4⟩
    · rw [ha, hax, hpl]; rfl
    · rw [hd, hdx, hpl]; rfl

end

end NativeRustcVmX64.Layout.LayoutWPlacement
