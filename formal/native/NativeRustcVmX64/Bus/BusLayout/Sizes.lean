module

public import NativeRustcVmX64.Bus.BusLayout.Pair
public import NativeRustcVmX64.Mem

/-!
# `bus_layout`'s sizes (x86-64)

From the entry to `NativeRustcVmX64.Vm.BusLayout.label_16` (`sizes_run`): the prologue and `memset` of the sizes
(`b0`), the framework's sizes copied (`b1` to `b4`), the pairs' loop set up (`b5`) and run
(`pair_step`), the last block of an odd count (`b15` to `b19`): every size written (`SzDone`).
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout

public section

/-- At `NativeRustcVmX64.Vm.BusLayout.label_16`: every size written. -/
structure SzDone (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (st : MachineData) : Prop where
  bd : Body m0 1808 busLayoutStack slots 8 st
  rg : Rg m0 st
  r15 : (reg st .r15).toNat = nf m0 + bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + bl.length)

theorem toUInt64_toNat (w : UInt64) : w.toNat.toUInt64 = w := by
  rw [Nat.toUInt64_eq, UInt64.ofNat_toNat]

/-- `test $1, bpl`, `je`: the count even. -/
theorem test_bit0 [Labels] (x : BitVec 64) {env : Env} (hx : env.regs .rbp = x) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rbp) (.lit 1)) (.lit 0)).eval env =
      decide (x.toNat % 2 = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low, ext, Width.bits, hx]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.and_one_is_mod]
  omega

variable [Host] {k : Nat}

/-- **The odd block** `b15` to `b19`. -/
theorem odd_run (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b15Offset)) (hE : SzEnd L bl m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b20Offset) ∧
      SzDone L bl m0 st'.data) st := by
  have hpre' := hpre
  obtain ⟨hst, hnf3, -, -, hbl2, hblmax, -, hown, -, hBok, -, hLok, -⟩ := hpre
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hn54 := pre_n hpre'
  have hmb : bl.length ≤ 51 := hblmax
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hnwF := frame_noWrap hst hN
  have hblk : (reg m0 .rcx).toNat + 16 * bl.length ≤ 2 ^ 64 := hBok.1.2
  have hlay : (reg m0 .r9).toNat + layoutBytes ≤ 2 ^ 64 := hLok.1.2
  have hlay72 : 72 ≤ layoutBytes := by decide
  have hbd := hE.bd
  have hrv : ∀ (st' st'' : MachineData), (∀ r, calleeSaved r = true →
      slots.any (·.2 == r) = false → reg st'' r = reg st' r) := fun _ _ r h h' ↦ regs_vac r h h'
  -- `b15`: an odd count?
  have hwf0 := wf0 (d := st.data) hst hN hbd.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf0 nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hbd.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hk1⟩ := after_eq run_b15 ▸ ok_b15
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf0 hmem1
  have hfr1 := Frame.of_block hbd.fr hwf0 hm1 hmid1 slots_le
  have bd1 : Body m0 1808 busLayoutStack slots 8 st1.data := ⟨hfr1, by rw [hd1]; exact hbd.same⟩
  have K1 : ∀ r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15],
      reg st1.data r = reg st.data r := fun r hr ↦ hk1.reg' hm1 hr
  have hrbp : (reg st.data .rbp).toNat = bl.length := by
    rw [hE.rg.rbp]; exact hpre'.2.2.2.2.2.2.1
  simp only [PcOk] at hpc1
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rbp) (.lit 1)) (.lit 0)).eval
    (Env.ofMachine st.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) =
      decide (bl.length % 2 = 0) from by
    rw [test_bit0 (reg st.data .rbp) rfl, hrbp]] at hpc1
  by_cases hev : bl.length % 2 = 0
  · -- Even: done.
    rw [decide_eq_true hev] at hpc1
    simp only [↓reduceIte] at hpc1
    refine .done _ ⟨hpc1.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_16_at), bd1,
      hE.rg.keep fun r hr ↦ K1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h <;> simp [h]),
      by rw [K1 .r15 (by simp)]; exact hE.r15, ?_⟩
    rw [hd1, show nf m0 + bl.length = nf m0 + 2 * (bl.length / 2) by omega]
    exact hE.sizes
  rw [decide_eq_false hev] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  have hj : 2 * (bl.length / 2) = bl.length - 1 := by omega
  set j := bl.length - 1 with hjdef
  have hjl : j < bl.length := by omega
  -- `b16`: the last block's owner.
  have hj16 : 16 * j + 16 ≤ 16 * bl.length := by omega
  have hblkJ : NativeRustcVm.Mapped st1.data.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * j)) 16 ∧
      NativeRustcVm.NoWrap (reg m0 .rcx + BitVec.ofNat 64 (16 * j)) 16 := by
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · rw [NativeRustcVm.addr_add_add]
      exact bd1.fr.kept _ (hBok.1.1 _ (show 16 * j + t < 16 * bl.length by omega))
    · unfold NativeRustcVm.NoWrap
      rw [NativeRustcVm.toNat_add_ofNat (show (reg m0 .rcx).toNat + 16 * j < 2 ^ 64 by omega)]
      omega
  have hwf2 : (Env.ofMachine st1.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * j), 16)]
      (fun _ ↦ 0) 0).WF := Env.wf_of ⟨hblkJ, trivial⟩ (List.pairwise_singleton _ _)
  have hrcx1 : reg st1.data .rcx = BitVec.ofNat 64 j := by
    rw [K1 .rcx (by simp), hE.rcx, hj]
  have hkeyO : keyO.eval (Env.ofMachine st1.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * j), 16)]
      (fun _ ↦ 0) 0) = (Env.ofMachine st1.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * j), 16)]
      (fun _ ↦ 0) 0).base 0 + BitVec.ofInt 64 ((0 : Nat) : Int) := by
    rw [Env.base_ofMachine _ _ _ _ rfl]
    simp only [keyO, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st1.data.regs.get64 .r13 = _ from (K1 .r13 (by simp)).trans hE.rg.r13,
      show st1.data.regs.get64 .rcx = _ from hrcx1, Nat.cast_zero, ofInt_zero64, BitVec.add_zero]
    congr 1
    have hsc : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
    rw [hsc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 4 = 16 from rfl, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
    have : j < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this, Nat.mul_comm]
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf2 nofun
    (hpc1.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b15_next)))
    (match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨hkeyO, trivial⟩)
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmem2, hdx2, hk2⟩ := after_eq run_b16 ▸ ok_b16
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf2 hmem2
  have bd2 := Body.of_eq hst hN bd1 hd2 (hk2.reg' hm2 (by simp))
  have htoN : ∀ {x : Nat}, x < 6 → (x.toUInt64.toBitVec).toNat = x := fun hx ↦ by
    rw [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hwk : bl[j].owner < 6 := hown _ (List.getElem_mem hjl)
  have ho2 : reg st2.data .rdx = bl[j].owner.toUInt64.toBitVec := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hdx2]
    show (Env.ofMachine st1.data _ (fun _ ↦ 0) 0).load 0 0 8 = _
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st1.data.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * j) +
      BitVec.ofNat 64 0)).toBitVec = _
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, owner_word hpre' bd1.same hjl]
  simp only [PcOk] at hpc2
  change st2.pc = if (cJa (.load 0 0 8)).eval
    (Env.ofMachine st1.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * j), 16)] (fun _ ↦ 0) 0) = true
    then _ else _ at hpc2
  rw [eval_cJa (v := .load 0 0 8) (x := bl[j].owner) ((congrArg BitVec.toNat
    ((hm2.regs .rdx _ hdx2).symm.trans ho2)).trans (htoN hwk))] at hpc2
  rw [decide_eq_false (by omega)] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b17`: its height.
  have layR : NativeRustcVm.Mapped st2.data.dmem (reg m0 .r9) 72 ∧
      NativeRustcVm.NoWrap (reg m0 .r9) 72 :=
    ⟨fun t ht ↦ bd2.fr.kept _ (hLok.1.1 _ (by omega)), by unfold NativeRustcVm.NoWrap; omega⟩
  have hwf3 : (Env.ofMachine st2.data [(reg m0 .r9, 72)] (fun _ ↦ reg st2.data .rdx) 0).WF :=
    Env.wf_of ⟨layR, trivial⟩ (List.pairwise_singleton _ _)
  have h12_2 : reg st2.data .r12 = reg m0 .r9 :=
    (hk2.reg' hm2 (by simp)).trans ((K1 .r12 (by simp)).trans hE.rg.r12)
  have hb2 : (reg st2.data .rdx).toNat < 6 := by rw [ho2, htoN hwk]; exact hwk
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf3 nofun
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b16_next)))
    (match_ofMachine (sregions := [72]) ⟨rfl, trivial⟩
      ⟨h12_2.trans (eval_ptr rfl).symm, rfl, trivial⟩ trivial ⟨hb2, trivial⟩ trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmem3, hdx3, h12_3, hk3⟩ := after_eq run_b17 ▸ ok_b17
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf3 hmem3
  have bd3 := Body.of_eq hst hN bd2 hd3 (hk3.reg' hm3 (by simp))
  have hh3 : reg st3.data .rdx = ((S L bl m0).getD (nf m0 + j) 0).toUInt64.toBitVec := by
    rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hdx3]
    show (Env.ofMachine st2.data _ _ 0).load 0 (24 + (BinOp.mul.apply .W64 (reg st2.data .rdx)
      (BitVec.ofNat 64 8)).toNat) 8 = _
    have hvar : (BinOp.mul.apply .W64 (reg st2.data .rdx) (BitVec.ofNat 64 8)).toNat =
        8 * bl[j].owner := by
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul]
      rw [ho2, htoN hwk, toNat_ofNat_lt (by decide)]
      omega
    rw [hvar, NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st2.data.dmem (reg m0 .r9 +
      BitVec.ofNat 64 (24 + 8 * bl[j].owner))).toBitVec = _
    rw [height_word hpre' bd2.same hwk, S_getD_bl hjl]
  simp only [PcOk] at hpc3
  -- `b19`: written.
  set i0 := nf m0 + j with hi0
  have frR : NativeRustcVm.Mapped st3.data.dmem (off (fb m0) (896 + 8 * i0)) 16 ∧
      NativeRustcVm.NoWrap (off (fb m0) (896 + 8 * i0)) 16 := by
    have hoff : (off (fb m0) (896 + 8 * i0)).toNat = (fb m0).toNat + (896 + 8 * i0) :=
      toNat_off (by omega)
    exact ⟨fun t ht ↦ by
      rw [off_add]; exact bd3.fr.kept _ (frame_mapped hst hN (896 + 8 * i0 + t) (by omega)),
      by unfold NativeRustcVm.NoWrap; rw [hoff]; omega⟩
  have hwf4 : (Env.ofMachine st3.data [(off (fb m0) (896 + 8 * i0), 16)] (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨frR, trivial⟩ (List.pairwise_singleton _ _)
  have K3 : ∀ r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r13, .r14, .r15],
      reg st3.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hk3.reg' hm3 (by simp)).trans ((hk2.reg' hm2 (by simp)).trans (K1 _ (by simp)))
  have hkeyP : keyP.eval (Env.ofMachine st3.data [(off (fb m0) (896 + 8 * i0), 16)]
      (fun _ ↦ 0) 0) = (Env.ofMachine st3.data [(off (fb m0) (896 + 8 * i0), 16)]
      (fun _ ↦ 0) 0).base 0 + BitVec.ofInt 64 ((0 : Nat) : Int) := by
    rw [Env.base_ofMachine _ _ _ _ rfl]
    simp only [keyP, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st3.data.regs.get64 .rax = _ from (K3 .rax (by simp)).trans hE.rax,
      show st3.data.regs.get64 .rcx = _ from (K3 .rcx (by simp)).trans (hE.rcx.trans (by rw [hj])),
      BitVec.ofNat_mul_ofNat, off_add, Nat.cast_zero, ofInt_zero64, BitVec.add_zero,
      show 896 + 8 * nf m0 + j * 8 = 896 + 8 * i0 by omega]
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf4 nofun
    (hpc3.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_15_at))
    (match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨hkeyP, trivial⟩)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hw4, hwr4, hk4⟩ := after_eq run_b19 ▸ ok_b19
  have hs4 := sameOutside_sub hwf4 hm4 (r := 0) rfl (le_refl 16) (lo := 0)
    fun w hw ↦ ⟨(hw4 w hw).1, Nat.zero_le _, by have := (hw4 w hw).2; omega⟩
  rw [off_zero, Nat.sub_zero] at hs4
  have bd4 := Body.of_sub hst hN bd3 (a := 896 + 8 * i0) (n := 16) (by omega)
    (fun p hp ↦ by have := slots_lo p hp; omega) slots_le hs4 (hk4.reg' hm4 (by simp))
    (hm4.kept hwf4) (hrv _ _)
  have hW4 : NativeRustcVm.WordAt st4.data.dmem (off (fb m0) (896 + 8 * i0))
      ((S L bl m0).getD i0 0).toUInt64 := by
    have := wordAt_write_eq hm4 (b := off (fb m0) (896 + 8 * i0)) (o := 0) rfl (by decide)
      (.reg .rdx) (hwr4.find (by simp)) hh3
    rwa [off_zero] at this
  simp only [PcOk] at hpc4
  refine .done _ ⟨hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b19_next)),
    bd4, hE.rg.keep fun r hr ↦ ?_, ?_, ?_⟩
  · have hr' : r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h <;> simp [h]
    rcases (show r = .r12 ∨ r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r13, .r14, .r15] by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h <;> simp [h]) with h | h
    · subst h
      have e3 : reg st3.data .r12 = reg m0 .r9 := (hm3.regs .r12 _ h12_3).trans (eval_ptr rfl)
      exact (hk4.reg' hm4 hr').trans (e3.trans
        (((K1 .r12 (by simp)).trans hE.rg.r12).symm.trans (K1 .r12 (by simp))))
    · exact (hk4.reg' hm4 hr').trans (K3 r h)
  · rw [hk4.reg' hm4 (by simp), K3 .r15 (by simp)]; exact hE.r15
  · rw [show nf m0 + bl.length = i0 + 1 by omega]
    exact sizes_snoc (sizes_keep hst (show SizesAt st3.data.dmem L bl m0 i0 by
      rw [hd3, hd2, hd1, hi0, ← hj]; exact hE.sizes) (le_refl _) (by omega) hs4) hW4

end

end NativeRustcVmX64.Bus.BusLayout
