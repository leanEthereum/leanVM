module

public import NativeRustcVmX64.Bus.BusLayout.Sizes
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `bus_layout`'s sizes, from the entry (x86-64)

`sizes_run`: the prologue and `memset` of the sizes (`b0`), the framework's sizes copied (`b1` to
`b4`), the pairs' loop set up (`b5`) and run (`pair_step`), the odd block (`odd_run`): at
`NativeRustcVmX64.Vm.BusLayout.label_16` every size written. A callee writing a range of the frame and its stack keeps
the body (`Body.call_frame`).
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout

public section

/-- **A callee writing a range of the frame below the slots and its stack** keeps the body. -/
theorem Body.call_frame {m0 st st' : MachineData} {N : Nat} (hst : StackOk m0 N)
    (hF : 1808 ≤ N) (hb : Body m0 1808 N slots 0 st) {a n S' : Nat}
    (han : a + n ≤ 1760) (hFS : 1808 + S' ≤ N) (hsv : Saved st st')
    (hrsp : rspOf st' = rspOf st + 8#64)
    (hs : NativeRustcVm.SameOutside st.dmem st'.dmem (fun q ↦
      NativeRustcVm.InRange (off (fb m0) a) n q ∨ NativeRustcVm.InRange (stackBelow st S') S' q)) :
    Body m0 1808 N slots 8 st' := by
  have hrsp0 := hst.1
  have htop := hst.2.1
  have hnw : NativeRustcVm.NoWrap (fb m0) (1808 + 8) := frame_noWrap hst hF
  have hsp := hb.sp0
  have hout : ∀ j, (j < a ∨ a + n ≤ j) → j < 1808 + 8 →
      ¬NativeRustcVm.InRange (off (fb m0) a) n (off (fb m0) j) := by
    intro j h1 h2 h
    rw [inRange_off_iff (by omega) (by unfold NativeRustcVm.NoWrap at hnw; omega)] at h
    omega
  refine ⟨Frame.call_slots hb.fr hsv hrsp hs (fun p hp i hi h ↦ ?_) (fun j hj h ↦ ?_),
    fun q hq ↦ ?_⟩
  · rcases h with h | h
    · exact hout _ (.inr (by have := slots_lo p hp; omega)) (by have := slots_le p hp; omega) h
    · exact not_callee hst hsp hFS (by have := slots_le p hp; omega) h
  · rcases h with h | h
    · exact hout _ (.inr (by omega)) (by omega) h
    · exact not_callee hst hsp hFS (by omega) h
  · refine (hs q fun h ↦ hq ?_).trans (hb.same q hq)
    rcases h with h | h
    · have hnw' : (fb m0).toNat + (1808 + 8) ≤ 2 ^ 64 := hnw
      exact inRange_frame_stack htop hrsp0 hF (inRange_of_off (N := 1808)
        (show (fb m0).toNat + 1808 ≤ 2 ^ 64 by omega) (by omega) h)
    · exact (inRange_callee hsp htop hrsp0 hFS h).1

theorem and_self_eval [Labels] {env : Env} {x : Nat} (hx : (env.regs .r14).toNat = x) :
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .r14) (.reg .r14)) (.lit 0)).eval env =
      decide (x = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  exact beq_of_toNat hx (toNat_ofNat_lt (by decide))

theorem eq_lit_eval [Labels] {env : Env} {x c : Nat} (hc : c < 2 ^ 64)
    (hx : (env.regs .r14).toNat = x) :
    (SBool.cmp .eq .W64 (.reg .r14) (.lit c)).eval env = decide (x = c) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  exact beq_of_toNat hx (toNat_ofNat_lt hc)

theorem and62_eval {x : BitVec 64} (h : x.toNat < 64) :
    BinOp.and.apply .W32 (UnOp.trunc.apply .W32 x) (BitVec.ofNat 64 62) =
      BitVec.ofNat 64 (2 * (x.toNat / 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, UnOp.apply, low, ext, Width.bits, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : x.toNat % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 = x.toNat := by omega
  rw [h1, show (62 : Nat) % 2 ^ 64 % 2 ^ 32 = 62 from rfl, and62 _ h]

variable [Host] {k : Nat}

/-- A framework size copied: `b2` to `b4` from the framework's region, `j` the size's index. -/
theorem fw_copy {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    (hpre : BusLayoutPre L bl m0) {st st' : MachineData} {j : Nat} (hj : j < nf m0)
    (hb : Body m0 1808 busLayoutStack slots 8 st) (hsz : SizesAt st.dmem L bl m0 j)
    {Sy : SState} (hwf : (Env.ofMachine st [(fb m0, 1808 + 8), (reg m0 .rsi, 8 * (j + 1))]
      (fun _ ↦ 0) 0).WF)
    (hm : Match (Env.ofMachine st [(fb m0, 1808 + 8), (reg m0 .rsi, 8 * (j + 1))]
      (fun _ ↦ 0) 0) Sy st')
    (hmid : MidOk 1808 8 slots Sy = true) (hw : ∀ w ∈ Sy.mem, w.r = 0)
    (hwr : Wrote 0 [(896 + 8 * j, .load 1 (8 * j) 8)] Sy)
    (hbd : ∀ w ∈ Sy.mem, 896 + 8 * j ≤ w.off ∧ w.off + w.n ≤ 896 + 8 * j + 8) :
    Body m0 1808 busLayoutStack slots 8 st' ∧ SizesAt st'.dmem L bl m0 (j + 1) := by
  have hst := hpre.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hF := hpre.2.2.2.1
  have hs := sameOutside_sub hwf hm (r := 0) rfl (show 896 + 8 * j + 8 ≤ 1808 + 8 by omega)
    (lo := 896 + 8 * j) fun w hwm ↦ ⟨hw w hwm, (hbd w hwm).1, (hbd w hwm).2⟩
  rw [show 896 + 8 * j + 8 - (896 + 8 * j) = 8 by omega] at hs
  have hb' := Body.of_sub hst hN hb (a := 896 + 8 * j) (n := 8) (by omega)
    (fun p hp ↦ by have := slots_lo p hp; omega) slots_le hs (hm.regs .rsp _ (by
      simp only [MidOk, Bool.and_eq_true, beq_iff_eq] at hmid; exact hmid.2) |>.trans
      (hb.fr.rsp_eval (rest := [(reg m0 .rsi, 8 * (j + 1))]) (vars := fun _ ↦ 0) (ret := 0)).symm)
    (hm.kept hwf) fun r h h' ↦ regs_vac r h h'
  refine ⟨hb', sizes_snoc (sizes_keep hpre.1 hsz (le_refl _) (by omega) hs) ?_⟩
  have hv : (Sym.load 1 (8 * j) 8).eval (Env.ofMachine st [(fb m0, 1808 + 8),
      (reg m0 .rsi, 8 * (j + 1))] (fun _ ↦ 0) 0) = ((S L bl m0).getD j 0).toUInt64.toBitVec := by
    show (Env.ofMachine st _ _ 0).load 1 (8 * j) 8 = _
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st.dmem (reg m0 .rsi + BitVec.ofNat 64 (8 * j))).toBitVec = _
    rw [S_getD_fw hj, toUInt64_toNat, NativeRustcVm.wordOf_congr fun i hi ↦ ?_]
    rw [NativeRustcVm.addr_add_add]
    exact get_keep hst hb.same hF.2 hF.1.2 (show 8 * j + i < 8 * nf m0 by omega)
  have := wordAt_write_eq hm (b := fb m0) (o := 896 + 8 * j) rfl (by omega) _
    (hwr.find (by simp)) hv
  exact this

/-- **From `NativeRustcVmX64.Vm.BusLayout.label_4`**: the pairs' loop set up and run, the odd block. -/
theorem from_b5 (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b5Offset)) (hb : Body m0 1808 busLayoutStack slots 8 st.data)
    (hrg : Rg m0 st.data) (hsz : SizesAt st.data.dmem L bl m0 (nf m0)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b20Offset) ∧
      SzDone L bl m0 st'.data) st := by
  have hst := hpre.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hbl2 := hpre.2.2.2.2.1
  have hmb : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  have hnb : (reg m0 .r8).toNat = bl.length := hpre.2.2.2.2.2.2.1
  have hrsp := hst.1
  have htop := hst.2.1
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hwf := wf0 (d := st.data) hst hN hb.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hax1, hcx1, hdx1, hsi1, h15_1, hk1⟩ := after_eq run_b5 ▸ ok_b5
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem1
  have hfr1 := Frame.of_block hb.fr hwf hm1 hmid1 slots_le
  have bd1 : Body m0 1808 busLayoutStack slots 8 st1.data := ⟨hfr1, by rw [hd1]; exact hb.same⟩
  have rg1 : Rg m0 st1.data := hrg.keep fun r hr ↦ hk1.reg' hm1 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h])
  have e14 : (reg st.data .r14).toNat = nf m0 := by rw [hrg.r14]
  have ebp : (reg st.data .rbp).toNat = bl.length := by rw [hrg.rbp]; exact hnb
  have hI0 : SzInv L bl m0 0 st1.data := by
    refine ⟨bd1, rg1, rfl, hbl2, ?_, hm1.regs .rcx _ hcx1, ?_, ?_, ?_, by rw [hd1]; exact hsz⟩
    · rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax1]
      apply BitVec.eq_of_toNat_eq
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      show (BitVec.ofNat 64 888 + (stackBelow m0 1808 + BitVec.ofInt 64 8 +
        reg st.data .r14 * BitVec.ofNat 64 8)).toNat = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, toNat_off (by omega)]
      have hfb : (stackBelow m0 1808).toNat = (rspOf m0).toNat - 1808 := hbase
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, e14, hfb]
      have h1 : (rspOf m0).toNat - 1808 + 8 % 2 ^ 64 < 2 ^ 64 := by omega
      have h2 : nf m0 * (8 % 2 ^ 64) < 2 ^ 64 := by omega
      have h3 : (rspOf m0).toNat - 1808 + 8 % 2 ^ 64 + nf m0 * (8 % 2 ^ 64) < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
      omega
    · rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx1]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [and62_eval (by rw [ebp]; omega), ebp]
    · rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hsi1]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .r13 = _ from hrg.r13]
    · rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ h15_1]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, BitVec.toNat_add]
      rw [show (st.data.regs.get64 .r14).toNat = nf m0 from e14,
        show (st.data.regs.get64 .rbp).toNat = bl.length from ebp]
      omega
  simp only [PcOk] at hpc1
  have hloop : Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b15Offset) ∧
      SzEnd L bl m0 st'.data) st1 :=
    Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b9Offset) ∧ ∃ i, bl.length - i = n ∧
      SzInv L bl m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ Eventually.mono
        (pair_step hp hpre hpc hI) fun st' h ↦ by
          rcases h with h | ⟨hpc', hI'⟩
          · exact Or.inl h
          · exact Or.inr ⟨bl.length - (i + 2), by have := hI.lt; omega, hpc', i + 2, rfl, hI'⟩)
      ⟨hpc1.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_7_at), 0, rfl, hI0⟩
  exact Eventually.bind hloop fun st' ⟨hpc', hE⟩ ↦ odd_run hp hpre hpc' hE

/-- **The sizes**: from the entry to `NativeRustcVmX64.Vm.BusLayout.label_16`. -/
theorem sizes_run (hp : Placed code k)
    (hms : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    (hpre : BusLayoutPre L bl m0) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b20Offset) ∧
      SzDone L bl m0 st'.data) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b0Offset)⟩ := by
  have hst := hpre.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hF := hpre.2.2.2.1
  have hrsp := hst.1
  have htop := hst.2.1
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  -- `b0`: the prologue, `memset` of the sizes.
  have hwf0 := wf_got hpre (d := m0) (fun _ h ↦ h) (l := "memset") (by simp)
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b0Offset + b0.length)).toBitVec)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_got hpre (fun _ _ ↦ rfl) (by simp) (BitVec.sub_add_cancel _ _).symm)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro1, hw1, hdi1, hdx1, hsi1, hbx1, hbp1, h12_1, h13_1, h14_1, h15_1⟩ :=
    after_eq run_b0 ▸ ok_b0
  have bd1 : Body m0 1808 busLayoutStack slots 0 st1.data :=
    Body.of_prologue hst hN hwf0 hm1 hpro1 hw1 slots_le (by decide)
  have rg1 : Rg m0 st1.data := ⟨hm1.regs .rbx _ hbx1, hm1.regs .r12 _ h12_1,
    hm1.regs .r13 _ h13_1, hm1.regs .r14 _ h14_1, hm1.regs .rbp _ hbp1⟩
  have e15 : reg st1.data .r15 = reg m0 .rsi := hm1.regs .r15 _ h15_1
  have edi : reg st1.data .rdi = off (fb m0) 896 := (hm1.regs .rdi _ hdi1).trans (eval_ptr0 896)
  have edx : (reg st1.data .rdx).toNat = 432 := by rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx1]; rfl
  have hoff : (off (fb m0) 896).toNat = (fb m0).toNat + 896 := toNat_off (by omega)
  have hnfd : nf m0 = (reg m0 .rdx).toNat := rfl
  have hfbd : (stackBelow m0 1808).toNat = (fb m0).toNat := rfl
  have hpreM : MemsetPre st1.data := by
    refine ⟨bd1.stackOk hst (by omega), ?_, ?_, ?_⟩
    · show NativeRustcVm.Mapped _ _ _
      rw [edi, edx]
      intro t ht
      rw [off_add]; exact bd1.fr.kept _ (frame_mapped hst hN (896 + t) (by omega))
    · show NativeRustcVm.NoWrap _ _
      rw [edi, edx]; unfold NativeRustcVm.NoWrap; rw [hoff, hbase]; omega
    · show NativeRustcVm.Apart _ _ _ _
      rw [edi, edx, bd1.sp0]; unfold NativeRustcVm.Apart; rw [hoff]; omega
  refine call_then hpc1 hms hpreM fun st2 hpc2 hrsp2 ⟨_, _, hso2, hsv2⟩ ↦ ?_
  rw [edi, edx] at hso2
  have bd2 := Body.call_frame (S' := 0) hst hN bd1 (a := 896) (n := 432) (by omega) (by omega)
    hsv2 hrsp2 (NativeRustcVm.Transcript.SameOutside.mono hso2 fun _ h ↦ .inl h)
  have rg2 := rg1.keep fun r hr ↦ hsv2.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)
  have e15' : reg st2.data .r15 = reg m0 .rsi := (hsv2.1 .r15 rfl).trans e15
  -- `b1`: no framework size?
  have hwf2 := wf0 (d := st2.data) hst hN bd2.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 nofun
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b0_next)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨bd2.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hk3⟩ := after_eq run_b1 ▸ ok_b1
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have bd3 : Body m0 1808 busLayoutStack slots 8 st3.data :=
    ⟨Frame.of_block bd2.fr hwf2 hm3 hmid3 slots_le, by rw [hd3]; exact bd2.same⟩
  have rg3 := rg2.keep fun r hr ↦ hk3.reg' hm3 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h])
  have e15_3 : reg st3.data .r15 = reg m0 .rsi := (hk3.reg' hm3 (by simp)).trans e15'
  have e14 : ∀ (d : MachineData), Rg m0 d → (reg d .r14).toNat = nf m0 := fun d h ↦ by rw [h.r14]
  simp only [PcOk] at hpc3
  rw [and_self_eval (e14 _ rg2)] at hpc3
  by_cases h0 : nf m0 = 0
  · rw [decide_eq_true h0] at hpc3
    simp only [↓reduceIte] at hpc3
    exact from_b5 hp hpre (hpc3.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_4_at)) bd3 rg3
      (fun j hj ↦ absurd hj (by omega))
  rw [decide_eq_false h0] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  -- The framework's region, for `b2` to `b4`.
  have fwR : ∀ (j : Nat), j < nf m0 → ∀ d : MachineData, Kept m0.dmem d.dmem →
      (frameEnv m0 d 1808 [(reg m0 .rsi, 8 * (j + 1))] (fun _ ↦ 0) 0).WF := fun j hj d hk ↦
    wf1 hst hN hk (a := reg m0 .rsi) (n := 8 * (j + 1))
      ⟨NativeRustcVm.Mapped.mono hF.1.1 (by omega), NativeRustcVm.NoWrap.mono hF.1.2 (by omega)⟩
      (by
        have h' : NativeRustcVm.Apart (reg m0 .rsi) (8 * nf m0) (stackBelow m0 busLayoutStack)
          (busLayoutStack + 8) := hF.2
        unfold NativeRustcVm.Apart at h' ⊢; omega)
  -- `b2`: the first.
  have hwf4 := fwR 0 (by omega) st3.data bd3.fr.kept
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4 nofun
    (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b1_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨bd3.fr.rsp_eval, known_ptr rfl e15_3, trivial⟩
      trivial trivial trivial)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, hwr4, hk4, hk5', hk6', hbd4, hmid5, hw5, hwr5, hbd5, hmid6, hw6, hwr6,
    hbd6⟩ := after_eq run_b2 ▸ ok_b234
  obtain ⟨bd4, hsz4⟩ := fw_copy hpre (j := 0) (by omega) bd3 (fun j hj ↦ absurd hj (by omega))
    hwf4 hm4 hmid4 hw4 hwr4 hbd4
  have rg4 := rg3.keep fun r hr ↦ hk4.reg' hm4 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h])
  have e15_4 : reg st4.data .r15 = reg m0 .rsi := by
    have : reg st4.data .r15 = _ := hm4.regs .r15 (.ptr 1 0) (by decide +kernel)
    exact this.trans (eval_ptr rfl)
  simp only [PcOk] at hpc4
  rw [eq_lit_eval (by decide) (e14 _ rg3)] at hpc4
  by_cases h1 : nf m0 = 1
  · rw [decide_eq_true h1] at hpc4
    simp only [↓reduceIte] at hpc4
    exact from_b5 hp hpre (hpc4.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_4_at)) bd4 rg4 (by rw [h1]; exact hsz4)
  rw [decide_eq_false h1] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b3`: the second.
  have hwf5 := fwR 1 (by omega) st4.data bd4.fr.kept
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf5 nofun
    (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b2_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨bd4.fr.rsp_eval, known_ptr rfl e15_4, trivial⟩
      trivial trivial trivial)
    fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨bd5, hsz5⟩ := fw_copy hpre (j := 1) (by omega) bd4 hsz4 hwf5 hm5 hmid5 hw5 hwr5 hbd5
  have rg5 := rg4.keep fun r hr ↦ hk5'.reg' hm5 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h])
  have e15_5 : reg st5.data .r15 = reg m0 .rsi := by
    have : reg st5.data .r15 = _ := hm5.regs .r15 (.ptr 1 0) (by decide +kernel)
    exact this.trans (eval_ptr rfl)
  simp only [PcOk] at hpc5
  rw [eq_lit_eval (by decide) (e14 _ rg4)] at hpc5
  by_cases h2 : nf m0 = 2
  · rw [decide_eq_true h2] at hpc5
    simp only [↓reduceIte] at hpc5
    exact from_b5 hp hpre (hpc5.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_4_at)) bd5 rg5 (by rw [h2]; exact hsz5)
  rw [decide_eq_false h2] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  -- `b4`: the third.
  have hwf6 := fwR 2 (by omega) st5.data bd5.fr.kept
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf6 nofun
    (hpc5.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b3_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨bd5.fr.rsp_eval, known_ptr rfl e15_5, trivial⟩
      trivial trivial trivial)
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨bd6, hsz6⟩ := fw_copy hpre (j := 2) (by omega) bd5 hsz5 hwf6 hm6 hmid6 hw6 hwr6 hbd6
  have rg6 := rg5.keep fun r hr ↦ hk6'.reg' hm6 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h])
  simp only [PcOk] at hpc6
  exact from_b5 hp hpre (hpc6.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b4_next)))
    bd6 rg6 (by rw [show nf m0 = 3 by omega]; exact hsz6)

end

end NativeRustcVmX64.Bus.BusLayout
