module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Powers
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `verify_stacked_opening`: the target's first term (x86-64)

`first_b25`: from `b25` (`AtB25`), `b25` reads the scales' count (saved at the frame's `88`), `b26`
the first scale, `b27` saves the scales' address (`80`) and multiplies the first scale by the ring
switch's target (`EW::mul`); `b28` keeps the product (RBX, the frame's `72`) and the layout (`32`):
with no column claim to `NativeRustcVmX64.Vm.VerifyStackedOpening.label_30` (`b38`, `Acc` at the end), else `b29` saves
the placements' address (`96`) and enters the target's loop (`Tgt 0`). `accOf j`: the target's
first `j` terms.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- The target's first `j` terms. -/
def accOf (s : TState) (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW) (value : EW)
    (j : Nat) : EW :=
  dotL ((scalesOf s layout cs).toList.take j) ((valsOf layout target cs value).take j)

/-- The frame's words from the target's terms on. -/
def fwA (m0 : MachineData) (layout : LayoutW) (cs : Array ColumnClaimW) : List (Nat × UInt64) :=
  fwL m0 ++ [(32, UInt64.ofBitVec (layA m0)), (80, UInt64.ofBitVec (off (scA m0) 8)),
    (88, (cntOf layout cs).toUInt64)]

/-- **The target's terms** of the claims before `i` added: the sum in RBX and the frame's `72`,
the next scale in R14, the scales' end in R12, the claims in R13. -/
structure Acc [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 : MachineData) (i : Nat) (st : MachineData) :
    Prop where
  ok : Ok m0 st 8
  out : Outs a s layout cs m0 st.dmem
  fw : FW st.dmem m0 (fwA m0 layout cs)
  hi72 : NativeRustcVm.WordAt st.dmem (off (stackBelow m0 512) 72)
    (accOf s layout target cs value (1 + placedOf layout cs i)).c1
  rbx : reg st .rbx = (accOf s layout target cs value (1 + placedOf layout cs i)).c0.toBitVec
  r13 : reg st .r13 = off (clA m0) 8
  r14 : reg st .r14 = off (scA m0) (8 + 16 * (1 + placedOf layout cs i))
  r12 : reg st .r12 = off (scA m0) (8 + 16 * cntOf layout cs)

/-- **The target's loop head** before claim `i` (`b34`): the claim's offset in RBP, the claims'
end in R15, the placements' address at the frame's `96`. -/
structure Tgt [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 : MachineData) (i : Nat) (st : MachineData) :
    Prop where
  acc : Acc a s layout target cs value m0 i st
  w96 : NativeRustcVm.WordAt st.dmem (off (stackBelow m0 512) 96)
    (UInt64.ofBitVec (off (layA m0) 120))
  hi : i < cs.size
  rbp : (reg st .rbp).toNat = 608 * i
  r15 : (reg st .r15).toNat = 608 * cs.size

end

public section

theorem FW.append {m0 : MachineData} {d : Mem 64} {L L' : List (Nat × UInt64)} (h : FW d m0 L)
    (h' : FW d m0 L') : FW d m0 (L ++ L') := fun p hp ↦
  (List.mem_append.mp hp).elim (h p) (h' p)

theorem FW.left {m0 : MachineData} {d : Mem 64} {L L' : List (Nat × UInt64)}
    (h : FW d m0 (L ++ L')) : FW d m0 L := fun p hp ↦ h p (List.mem_append_left _ hp)

theorem FW.right {m0 : MachineData} {d : Mem 64} {L L' : List (Nat × UInt64)}
    (h : FW d m0 (L ++ L')) : FW d m0 L' := fun p hp ↦ h p (List.mem_append_right _ hp)

theorem FW.one {m0 : MachineData} {d : Mem 64} {o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt d (off (stackBelow m0 512) o) v) : FW d m0 [(o, v)] :=
  FW.cons h (FW.nil _ _)

theorem placedOf_zero (layout : LayoutW) (cs : Array ColumnClaimW) : placedOf layout cs 0 = 0 := by
  simp [placedOf]

theorem length_scalesOf (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW) :
    (scalesOf s layout cs).toList.length = cntOf layout cs := by
  rw [Array.length_toList, size_scalesOf]

theorem accOf_one (s : TState) (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW)
    (value : EW) :
    accOf s layout target cs value 1 = (scalesOf s layout cs).toList[0]'(by
      rw [length_scalesOf]; unfold cntOf; omega) * target := by
  unfold accOf
  rw [dotL_take_one (by rw [length_scalesOf]; unfold cntOf; omega) (by simp [valsOf])]
  simp [valsOf]

/-- The product's halves from `ewRet`. -/
theorem ewRet_halves {m : MachineData} {x : EW} (h : ewRet m = x) :
    reg m .rax = x.c0.toBitVec ∧ reg m .rdx = x.c1.toBitVec := by
  subst h
  exact ⟨rfl, rfl⟩

/-- An `E` element's two words, loaded from a region. -/
theorem ew_loads [Labels] {d : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {r n o : Nat} {b : BitVec 64} (hb : rs[r]? = some (b, n)) {x : EW}
    (h : NativeRustcVm.EWAt d.dmem (off b o) x) :
    (Env.ofMachine d rs vs ret).load r o 8 = x.c0.toBitVec ∧
      (Env.ofMachine d rs vs ret).load r (o + 8) 8 = x.c1.toBitVec := by
  obtain ⟨h0, h1⟩ := NativeRustcVm.ewAt_iff.mp h
  exact ⟨load_ofMachine hb h0, load_ofMachine hb (by rw [← off_off]; exact h1)⟩

/-- `x · 608`, without overflow. -/
theorem eval_mul608 [Labels] {env : Env} (X : Sym) (h : (X.eval env).toNat ≤ 160 * 608) :
    ((Sym.bin .mul .W64 X (.lit 608)).eval env).toNat = 608 * (X.eval env).toNat := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem bv_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem fwA_of {m0 : MachineData} {layout : LayoutW} {cs : Array ColumnClaimW} {d : Mem 64}
    (hL : FW d m0 (fwL m0))
    (h32 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 32) (UInt64.ofBitVec (layA m0)))
    (h80 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 80) (UInt64.ofBitVec (off (scA m0) 8)))
    (h88 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 88) (cntOf layout cs).toUInt64) :
    FW d m0 (fwA m0 layout cs) :=
  hL.append (FW.cons h32 (FW.cons h80 (FW.one h88)))

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The target's first term**: `b25` to `b29`. -/
theorem first_b25 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b25Offset))
    (hA : AtB25 a s layout cs m0 st.data) {R : MachineState → Prop}
    (cont1 : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b34Offset) →
      Tgt a s layout target cs value m0 0 st'.data → Eventually (step1 Host.exe) R st')
    (cont2 : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b38Offset) →
      Acc a s layout target cs value m0 cs.size st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hA.ok
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.n_le
  have hscn := h.sc_nw
  have hsc8 := h.sc8_le (layout := layout)
  have hsb : scalesBytes = 2600 := rfl
  have hscap : NativeRustcVm.Apart (scA m0) scalesBytes (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := h.so.1.2.2.2.2.1
  have hcnt : cntOf layout cs < 163 := by unfold cntOf; omega
  -- `b25`: the count
  have hwf1 : ∀ ret, (frameEnv m0 st.data 512 [(scA m0, 8)] (fun _ ↦ 0) ret).WF := fun _ ↦
    hok.wf1 h (fun i hi ↦ h.so.1.1 i (by omega)) (by unfold NativeRustcVm.NoWrap at hscn ⊢; omega)
      (apart_shrink hscap (by omega) le_rfl)
  have hm1 : ∀ ret, Match (frameEnv m0 st.data 512 [(scA m0, 8)] (fun _ ↦ 0) ret) scS st.data :=
    fun _ ↦ match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st.data .r14 = _
          rw [hA.r14, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have hL : ∀ ret, (frameEnv m0 st.data 512 [(scA m0, 8)] (fun _ ↦ 0) ret).load 1 0 8 =
      (cntOf layout cs).toUInt64.toBitVec := fun _ ↦
    load_ofMachine (r := 1) rfl (by rw [off_zero]; exact hA.out.scw)
  have hLn : ∀ ret, ((frameEnv m0 st.data 512 [(scA m0, 8)] (fun _ ↦ 0) ret).load 1 0 8).toNat =
      cntOf layout cs := fun _ ↦ by rw [hL]; exact u64n (by omega)
  refine h.run hp b25_in_code (List.cons_ne_nil _ _) hpc hok (hwf1 _) (hm1 _) run_b25 (o := 8)
    (by decide +kernel) (by decide) fun st1 hok1 hs1 hm1' hpc1 ↦ ?_
  have hLv : ∀ ret, ((Sym.ite (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 163))) (.lit 0)
      (.load 1 0 8)).eval (frameEnv m0 st.data 512 [(scA m0, 8)] (fun _ ↦ 0) ret)) =
        (cntOf layout cs).toUInt64.toBitVec := fun _ ↦ by
    rw [eval_ite_not_ult _ _ _ ((hLn _).trans_lt hcnt) (by decide)]
    exact hL _
  have e1_rcx : reg st1.data .rcx = off (scA m0) 8 := by
    rw [show reg st1.data .rcx = _ from hm1'.regs .rcx _ rfl,
      eval_ite_ult _ _ _ ((hLn _).trans_lt hcnt) (by decide)]
    exact hA.r12
  have e1_r12 : (reg st1.data .r12).toNat = 16 * cntOf layout cs := by
    rw [show reg st1.data .r12 = _ from hm1'.regs .r12 _ rfl, eval_shl_lit' _ (by decide), hLv,
      shl4_toNat' _ (by rw [u64n (by omega)]; omega), u64n (by omega)]
  have hd1 := hok1
  simp only [PcOk] at hpc1
  rw [eval_test0, hLv, u64n (by omega)] at hpc1
  simp only [show ¬ (cntOf layout cs = 0) by unfold cntOf; omega, decide_false,
    Bool.false_eq_true, ↓reduceIte] at hpc1
  have w88 : NativeRustcVm.WordAt st1.data.dmem (off (stackBelow m0 512) 88)
      (cntOf layout cs).toUInt64 := by
    have := fw_write hm1' (o := 88) (by omega) (v := Sym.ite (.not (.cmp .ult .W64 (.load 1 0 8)
      (.lit 163))) (.lit 0) (.load 1 0 8)) (by decide +kernel)
    rw [hLv] at this
    exact this
  have hfw1 : FW st1.data.dmem m0 (fwL m0 ++ [(88, (cntOf layout cs).toUInt64)]) :=
    (FW.block_os (hwf1 _) hm1' rfl hA.fw [24, 40, 48, 56, 64] rfl (by decide +kernel)).append
      (FW.one w88)
  have hout1 := Outs.keep h hA.out (hm1'.kept (hwf1 _)) (h.blk_stack hs1)
  -- `b26`: the first scale
  have hs0 : 0 < (scalesOf s layout cs).toList.length := by
    rw [length_scalesOf]; unfold cntOf; omega
  have hoff8 : (off (scA m0) 8).toNat = (scA m0).toNat + 8 :=
    toNat_off (by unfold NativeRustcVm.NoWrap at hscn; omega)
  have hwf2 : ∀ ret, (frameEnv m0 st1.data 512 [(off (scA m0) 8, 16)] (fun _ ↦ 0) ret).WF :=
    fun _ ↦ hok1.wf1 h (mapped_off h.so.1.1 (by omega)) (noWrap_off' hscn (by omega) (by omega))
      (by
        have hh := hscap
        have hsbe := h.sb
        unfold NativeRustcVm.Apart at hh ⊢
        rw [hsb] at hh
        rw [hoff8]
        omega)
  have hm2 : ∀ ret, Match (frameEnv m0 st1.data 512 [(off (scA m0) 8, 16)] (fun _ ↦ 0) ret) sc0S
      st1.data := fun _ ↦
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok1.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st1.data .rcx = _
          rw [e1_rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have hsc0 := ew_loads (d := st1.data) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b26Offset + b26.length)).toBitVec)
    (rs := [(stackBelow m0 512, 520), (off (scA m0) 8, 16)]) (b := off (scA m0) 8) (n := 16)
    (r := 1) (o := 0) rfl (by
      have h0 := hout1.scs.getElem hs0
      rw [Nat.mul_zero] at h0
      exact h0)
  refine h.run hp b26_in_code (List.cons_ne_nil _ _)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b25_next)) hok1 (hwf2 _) (hm2 _) run_b26 (o := 8)
    (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2' hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hd2 := hm2'.dmem_eq (hwf2 _) rfl
  have e2_rdi : reg st2.data .rdi = ((scalesOf s layout cs).toList[0]).c0.toBitVec :=
    (hm2'.regs .rdi _ rfl).trans (hsc0.1)
  have e2_rsi : reg st2.data .rsi = ((scalesOf s layout cs).toList[0]).c1.toBitVec :=
    (hm2'.regs .rsi _ rfl).trans (hsc0.2)
  have e2_r14 : reg st2.data .r14 = off (scA m0) (8 + 16 * (1 + placedOf layout cs 0)) := by
    rw [show reg st2.data .r14 = _ from hm2'.regs .r14 _ rfl, eval_add64, placedOf_zero]
    show reg st1.data .rcx + BitVec.ofNat 64 16 = _
    rw [e1_rcx, off_add]
  have hout2 : Outs a s layout cs m0 st2.data.dmem := by rw [hd2]; exact hout1
  have hfw2 : FW st2.data.dmem m0 (fwL m0 ++ [(88, (cntOf layout cs).toUInt64)]) := by
    rw [hd2]; exact hfw1
  -- `b27`: the ring switch's target, `EW::mul`
  have hring := (h.ins _ mem_ring).1
  have hrb : NativeRustcVm.Ring.ringWBytes = 1040 := rfl
  simp only [hrb] at hring
  have hwf3 : ∀ ret, (frameEnv m0 st2.data 512 [(reg m0 .rcx, 16)] (fun _ ↦ 0) ret).WF :=
    fun _ ↦ hok2.wf1 h (fun i hi ↦ hring.1.1 i (by omega))
      (by
        have hrn : (reg m0 .rcx).toNat + 1040 ≤ 2 ^ 64 := hring.1.2
        unfold NativeRustcVm.NoWrap; omega)
      (apart_shrink hring.2 (by omega) le_rfl)
  have hm3 : ∀ ret, Match (frameEnv m0 st2.data 512 [(reg m0 .rcx, 16)] (fun _ ↦ 0) ret) ringS
      st2.data := fun _ ↦
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok2.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show (frameEnv m0 st2.data 512 _ (fun _ ↦ 0) _).load 0 64 8 = _
          rw [fw_load hfw2 (o := 64) (v := UInt64.ofBitVec (reg m0 .rcx)) (by simp [fwL]),
            show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have htgt := ew_loads (d := st2.data) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b27Offset + b27.length)).toBitVec) (rs := [(stackBelow m0 512, 520),
    (reg m0 .rcx, 16)]) (b := reg m0 .rcx) (n := 16) (r := 1) (o := 0) rfl (by
      rw [off_zero]
      exact NativeRustcVm.Layout.EWAt.of_same h.ring.1 (hok2.same_in h mem_ring)
        (by show 16 ≤ 1040; decide))
  refine h.run hp b27_in_code (List.cons_ne_nil _ _)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b26_next)) hok2 (hwf3 _) (hm3 _) run_b27 (o := 0)
    (by decide +kernel) (by decide) fun st3 hok3 hs3 hm3' hpc3 ↦ ?_
  have hout3 := Outs.keep h hout2 (hm3'.kept (hwf3 _)) (h.blk_stack hs3)
  have w80 : NativeRustcVm.WordAt st3.data.dmem (off (stackBelow m0 512) 80)
      (UInt64.ofBitVec (off (scA m0) 8)) := by
    have := fw_write hm3' (o := 80) (by omega) (v := .reg .rcx) (by decide +kernel)
    rw [show (Sym.reg .rcx).eval (frameEnv m0 st2.data 512 [(reg m0 .rcx, 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b27Offset + b27.length)).toBitVec) = reg st1.data .rcx from
        regKeep hm2' .rcx rfl, e1_rcx] at this
    exact this
  have hfw3 : FW st3.data.dmem m0 (fwL m0 ++ [(88, (cntOf layout cs).toUInt64)] ++
      [(80, UInt64.ofBitVec (off (scA m0) 8))]) :=
    (FW.block_os (hwf3 _) hm3' rfl hfw2 [24, 40, 48, 56, 64, 88] rfl (by decide +kernel)).append
      (FW.one w80)
  have e3_r12 : reg st3.data .r12 = off (scA m0) (8 + 16 * cntOf layout cs) := by
    rw [show reg st3.data .r12 = _ from hm3'.regs .r12 _ rfl, eval_add64]
    show reg st2.data .rcx + reg st2.data .r12 = _
    rw [regKeep hm2' .rcx rfl, regKeep hm2' .r12 rfl, e1_rcx, bv_of_toNat e1_r12, off_add]
  refine h.mul hmul hok3 hpc3 fun st4 hpc4 hok4 hfs4 hret4 hcs4 hk4 hs4 ↦ ?_
  have hret : ewRet st4.data = (scalesOf s layout cs).toList[0] * target := by
    rw [hret4]
    show EW.mul _ _ = EW.mul _ _
    rw [show reg st3.data .rdi = _ from regKeep hm3' .rdi rfl, e2_rdi,
      show reg st3.data .rsi = _ from regKeep hm3' .rsi rfl, e2_rsi,
      show reg st3.data .rdx = _ from hm3'.regs .rdx _ rfl,
      show reg st3.data .rcx = _ from hm3'.regs .rcx _ rfl]
    show EW.mul _ (ewArg ((frameEnv m0 st2.data 512 _ (fun _ ↦ 0) _).load 1 0 8)
      ((frameEnv m0 st2.data 512 _ (fun _ ↦ 0) _).load 1 8 8)) = _
    rw [htgt.1, htgt.2]
    rfl
  obtain ⟨hax4, hdx4⟩ := ewRet_halves hret
  have hout4 := Outs.keep h hout3 hk4 hs4
  have hfw4 := hfw3.call hfs4 (le_of_map [24, 40, 48, 56, 64, 88, 80] rfl (by decide))
  have e4_r14 : reg st4.data .r14 = off (scA m0) (8 + 16 * (1 + placedOf layout cs 0)) := by
    rw [hcs4 .r14 rfl, regKeep hm3' .r14 rfl, e2_r14]
  have e4_r12 : reg st4.data .r12 = off (scA m0) (8 + 16 * cntOf layout cs) := by
    rw [hcs4 .r12 rfl, e3_r12]
  have k4 : ∀ r : Reg64, r ∈ [Reg64.rbp, .r13, .r15] → reg st4.data r = reg st.data r :=
    fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [hcs4 _ rfl, regKeep hm3' _ rfl, regKeep hm2' _ rfl, regKeep hm1' _ rfl]
  -- `b28`
  refine h.run hp b28_in_code (List.cons_ne_nil _ _) hpc4 hok4 (vars := fun _ ↦ 0) (hok4.wf0 h)
    hok4.m_reg run_b28 (o := 8) (by decide +kernel) (by decide) fun st5 hok5 hs5 hm5 hpc5 ↦ ?_
  have hout5 := Outs.keep h hout4 (hm5.kept (hok4.wf0 h)) (h.blk_stack hs5)
  have hfw5 := FW.block_os (hok4.wf0 h) hm5 rfl hfw4 [24, 40, 48, 56, 64, 88, 80] rfl
    (by decide +kernel)
  have w72 : NativeRustcVm.WordAt st5.data.dmem (off (stackBelow m0 512) 72)
      (accOf s layout target cs value (1 + placedOf layout cs 0)).c1 := by
    have := fw_write hm5 (o := 72) (by omega) (v := .reg .rdx) (by decide +kernel)
    rw [show (Sym.reg .rdx).eval (frameEnv m0 st4.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b28Offset + b28.length)).toBitVec) = reg st4.data .rdx from rfl, hdx4] at this
    rw [placedOf_zero, Nat.add_zero, accOf_one]
    exact this
  have w32 : NativeRustcVm.WordAt st5.data.dmem (off (stackBelow m0 512) 32)
      (UInt64.ofBitVec (layA m0)) := by
    have := fw_write hm5 (o := 32) (by omega) (v := .reg .rbp) (by decide +kernel)
    rw [show (Sym.reg .rbp).eval (frameEnv m0 st4.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b28Offset + b28.length)).toBitVec) = reg st4.data .rbp from rfl,
      k4 .rbp (by simp), hA.rbp] at this
    exact this
  have hfwA5 : FW st5.data.dmem m0 (fwA m0 layout cs) :=
    fwA_of hfw5.left.left w32 (hfw5.right.get (by simp)) (hfw5.left.right.get (by simp))
  have e5_rbx : reg st5.data .rbx =
      (accOf s layout target cs value (1 + placedOf layout cs 0)).c0.toBitVec := by
    rw [show reg st5.data .rbx = reg st4.data .rax from hm5.regs .rbx _ rfl, hax4, placedOf_zero,
      Nat.add_zero, accOf_one]
  have k5 : ∀ r : Reg64, r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15] →
      reg st5.data r = reg st4.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regKeep hm5 _ rfl
  simp only [PcOk] at hpc5
  rw [eval_test0] at hpc5
  have h15 : ((Sym.reg .r15).eval (frameEnv m0 st4.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b28Offset + b28.length)).toBitVec)).toNat = cs.size := by
    show (reg st4.data .r15).toNat = _
    rw [k4 .r15 (by simp)]; exact hA.r15
  rw [h15] at hpc5
  by_cases hz : cs.size = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc5
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_30_at] at hpc5
    have hp0 : placedOf layout cs cs.size = placedOf layout cs 0 := by rw [hz]
    refine cont2 st5 hpc5 ⟨hok5, hout5, hfwA5, by rw [hp0]; exact w72, by rw [hp0]; exact e5_rbx,
      by rw [k5 .r13 (by simp), k4 .r13 (by simp)]; exact hA.r13,
      by rw [hp0, k5 .r14 (by simp)]; exact e4_r14, by rw [k5 .r12 (by simp)]; exact e4_r12⟩
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc5
    -- `b29`
    refine h.run hp b29_in_code (List.cons_ne_nil _ _)
      (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b28_next)) hok5 (vars := fun _ ↦ 0) (hok5.wf0 h)
      hok5.m_reg run_b29 (o := 8) (by decide +kernel) (by decide) fun st6 hok6 hs6 hm6 hpc6 ↦ ?_
    simp only [PcOk] at hpc6
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_26_at] at hpc6
    have hrbp5 : reg st5.data .rbp = layA m0 := by rw [k5 .rbp (by simp), k4 .rbp (by simp)]; exact hA.rbp
    have w96 : NativeRustcVm.WordAt st6.data.dmem (off (stackBelow m0 512) 96)
        (UInt64.ofBitVec (off (layA m0) 120)) := by
      have := fw_write hm6 (o := 96) (by omega) (v := .bin .add .W64 (.reg .rbp) (.lit 120))
        (by decide +kernel)
      rw [eval_add64] at this
      rw [← hrbp5]
      exact this
    have k6 : ∀ r : Reg64, r ∈ [Reg64.rbx, .r12, .r13, .r14] →
        reg st6.data r = reg st5.data r := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact regKeep hm6 _ rfl
    refine cont1 st6 hpc6 ⟨⟨hok6, Outs.keep h hout5 (hm6.kept (hok5.wf0 h)) (h.blk_stack hs6),
      FW.block_os (hok5.wf0 h) hm6 rfl hfwA5 [24, 40, 48, 56, 64, 32, 80, 88] rfl
        (by decide +kernel),
      (FW.block_os (L := [(72, _)]) (hok5.wf0 h) hm6 rfl (FW.one w72) [72] rfl
        (by decide +kernel)).get (by simp),
      by rw [k6 .rbx (by simp)]; exact e5_rbx,
      by rw [k6 .r13 (by simp), k5 .r13 (by simp), k4 .r13 (by simp)]; exact hA.r13,
      by rw [k6 .r14 (by simp), k5 .r14 (by simp)]; exact e4_r14,
      by rw [k6 .r12 (by simp), k5 .r12 (by simp)]; exact e4_r12⟩, w96, by omega, ?_, ?_⟩
    · rw [show reg st6.data .rbp = BitVec.ofNat 64 0 from hm6.regs .rbp _ rfl]; rfl
    · rw [show reg st6.data .r15 = _ from hm6.regs .r15 _ rfl, eval_mul608 _ (by
        show (reg st5.data .r15).toNat ≤ _
        rw [k5 .r15 (by simp), k4 .r15 (by simp), hA.r15]; have := h.n_le; omega)]
      show 608 * (reg st5.data .r15).toNat = _
      rw [k5 .r15 (by simp), k4 .r15 (by simp), hA.r15]

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
