module

public import NativeRustcVmX64.Layout.BuildLayout.Base
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names

/-!
# `build_layout` on x86-64: the entry and the checks (`b0` to `b8`)

`b0` pushes six registers and tests the bytecode's length a power of two (`b19` returns `0`);
`b1` calls `bit_length(n)`; `b2` checks the bit length at least `5` and the memory's log-size in
`1 … 30`, `b3` to `b7` the first five row counts at most `2 ^ 30`, `b8` the last and the
bytecode's log-size at most `30`. A failed check returns `0` (`fail`); else at `b9` (`St9`) the
log-sizes are in RBX and RAX, the row counts in R12, RBP, R15, R8, RDI, RSI (`checks`).
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

section
variable [Labels]

/-- **At `b3`**: the length a power of two, the log-sizes checked. -/
structure St4 (m0 d : MachineData) : Prop where
  b : B m0 8 d
  rbx : reg d .rbx = reg m0 .rsi
  r13 : reg d .r13 = ll m0
  r14 : reg d .r14 = rp m0
  rax : (reg d .rax).toNat = bitLength (nN m0) - 5
  pow2 : Pow2 (nN m0)
  g2 : 5 ≤ bitLength (nN m0) ∧ 1 ≤ lmN m0 ∧ lmN m0 ≤ 30

/-- **At `b8`**: the first five row counts checked, in registers. -/
structure St8 (m0 d : MachineData) : Prop where
  s4 : St4 m0 d
  r12 : reg d .r12 = (rowW m0 0).toBitVec
  rbp : reg d .rbp = (rowW m0 1).toBitVec
  r15 : reg d .r15 = (rowW m0 2).toBitVec
  r8 : reg d .r8 = (rowW m0 3).toBitVec
  rdi : reg d .rdi = (rowW m0 4).toBitVec
  rows : ∀ t < 5, (rowW m0 t).toNat ≤ 2 ^ 30

/-- **At `b9`**: the checks passed, the log-sizes and row counts in registers. -/
structure St9 (m0 d : MachineData) : Prop where
  b : B m0 8 d
  rbx : reg d .rbx = reg m0 .rsi
  r13 : reg d .r13 = ll m0
  r14 : reg d .r14 = rp m0
  rax : (reg d .rax).toNat = bitLength (nN m0) - 5
  r12 : reg d .r12 = (rowW m0 0).toBitVec
  rbp : reg d .rbp = (rowW m0 1).toBitVec
  r15 : reg d .r15 = (rowW m0 2).toBitVec
  r8 : reg d .r8 = (rowW m0 3).toBitVec
  rdi : reg d .rdi = (rowW m0 4).toBitVec
  rsi : reg d .rsi = (rowW m0 5).toBitVec
  pow2 : Pow2 (nN m0)
  chk : Chk m0

end

end

public section

variable {m0 : MachineData} {bc : Array UInt64}

theorem lit_eval [Labels] (env : Env) {n : Nat} (h : n < 2 ^ 64) : ((Sym.lit n).eval env).toNat = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem dec_eval' [Labels] (env : Env) (x : Sym) :
    (dec x).eval env = x.eval env + BitVec.ofNat 64 18446744073709551615 := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem dec_eval [Labels] (env : Env) (x : Sym) :
    ((dec x).eval env).toNat = ((x.eval env).toNat + 18446744073709551615) % 18446744073709551616 := by
  rw [dec_eval', BitVec.toNat_add, BitVec.toNat_ofNat]

theorem rM5_eval' [Labels] (env : Env) :
    rM5.eval env = BitVec.ofNat 64 18446744073709551611 + env.regs .rax := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem rM5_eval [Labels] (env : Env) :
    (rM5.eval env).toNat = (18446744073709551611 + (env.regs .rax).toNat) % 18446744073709551616 := by
  rw [rM5_eval', BitVec.toNat_add, BitVec.toNat_ofNat]

/-- A row count in a body: as at the entry. -/
theorem row_same [Labels] (hF : Facts bc m0) {o : Nat} {d : MachineData} (hb : B m0 o d) {t : Nat}
    (ht : t < 6) : wordOf d.dmem (off (rp m0) (8 * t)) = rowW m0 t := by
  have hrn : (rp m0).toNat + 48 ≤ 2 ^ 64 := hF.rr.2
  refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
  rw [off_add]
  have hq : NativeRustcVm.InRange (rp m0) 48 (off (rp m0) (8 * t + i)) :=
    inRange_off_self (by omega) (by omega)
  refine hb.same _ fun h ↦ h.elim (fun h' ↦ not_inRange_of_apart hF.ap hF.rr.2 hF.lr.2 hq h')
    fun h' ↦ not_inRange_of_apart hF.ro hF.rr.2 (noWrap_stackBelow hF.stack) hq
      (inRange_mono h' (by omega))

variable [Host] {k : Nat}

/-- **A row check** (`b3` to `b7`): row count `t` at most `2 ^ 30`, or a failure. -/
theorem rowBlk (hF : Facts bc m0) {ds : List Directive} {kk t : Nat} {Sy1 : SState}
    (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds rowS = some (Sy1, .cond (cRow (8 * t)) NativeRustcVmX64.Vm.BuildLayout.label_17))
    (hok : MidOk 1360 8 slots Sy1 = true) (hmem : Sy1.mem = []) (ht : t < 6)
    (hL : Labels.label NativeRustcVmX64.Vm.BuildLayout.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset)) {st : MachineState}
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data) (h14 : reg st.data .r14 = rp m0)
    {Q : MachineState → Prop}
    (hfail : ∀ s : MachineState, s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset) → B m0 8 s.data →
      ¬ (rowW m0 t).toNat ≤ 2 ^ 30 → Eventually (step1 Host.exe) Q s)
    (cont : ∀ st' : MachineState,
      Match (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0) Sy1 st'.data →
      st'.pc = Host.addrOf (kk + ds.length) → B m0 8 st'.data → st'.data.dmem = st.data.dmem →
      (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0).load 1 (8 * t) 8 = (rowW m0 t).toBitVec →
      (rowW m0 t).toNat ≤ 2 ^ 30 → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hpr : NativeRustcVm.Mapped m0.dmem (rp m0) 48 ∧ NativeRustcVm.NoWrap (rp m0) 48 := hF.rr
  have hpf : NativeRustcVm.Apart (stackBelow m0 1360) (1360 + 8) (rp m0) 48 :=
    Apart.symm' (apart_frame hF.ro hF.rsp.1 (by decide))
  have hwf := fr_wf1 (vars := fun _ ↦ 0) (ret := 0) hb hF.stack (by decide) hpr.1 hpr.2 hpf
  have hm : Match (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0) rowS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, by
      show reg st.data .r14 = rp m0 + BitVec.ofInt 64 0
      rw [ofInt_zero64, BitVec.add_zero, h14], trivial⟩ trivial trivial trivial
  have hld : (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0).load 1 (8 * t) 8 =
      (rowW m0 t).toBitVec := by
    rw [Arrays.load8_eq]
    show (wordOf st.data.dmem (rp m0 + BitVec.ofNat 64 (8 * t))).toBitVec = _
    exact congrArg UInt64.toBitVec (row_same hF hb ht)
  refine exec_at hk hx hwf nofun hpc hm fun st' hm' hpc' ↦ ?_
  have hb' : B m0 8 st'.data := hb.of_read hwf hm' hok slots_le hmem
  simp only [PcOk] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := 2 ^ 30 < (rowW m0 t).toNat) hpc' (by rw [cRow_eval, hld]; rfl)
  by_cases h : 2 ^ 30 < (rowW m0 t).toNat
  · exact hfail st' ((hy h).trans hL) hb' (by omega)
  · exact cont st' hm' (hno h) hb' (hm'.dmem_eq hwf hmem) hld (by omega)

/-- **After `bit_length(n)`**: the length a power of two, its bit length in RAX. -/
structure St3 (m0 d : MachineData) : Prop where
  b : B m0 8 d
  rbx : reg d .rbx = reg m0 .rsi
  r13 : reg d .r13 = ll m0
  r14 : reg d .r14 = rp m0
  rax : (reg d .rax).toNat = bitLength (nN m0)
  pow2 : Pow2 (nN m0)

/-- **The entry**, `b0` and `b1`: the power-of-two test, `bit_length(n)`. -/
theorem entry1 (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hF : Facts bc m0) :
    Eventually (step1 Host.exe) (fun s ↦ Post bc m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b2Offset) ∧ St3 m0 s.data))
      ⟨m0, Labels.label NativeRustcVmX64.Vm.BuildLayout.entryLabel⟩ := by
  rw [show Labels.label NativeRustcVmX64.Vm.BuildLayout.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b0Offset) from hp.label NativeRustcVmX64.Vm.BuildLayout.entry_at]
  have hwf0 : (frameEnv m0 m0 1360 [] (fun _ ↦ 0) 0).WF :=
    frame_wf ⟨frame_mapped hF.stack (by decide), frame_noWrap hF.stack (by decide)⟩ (by simp)
      (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 1360 [] (fun _ ↦ 0) 0) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  have L17 : Labels.label NativeRustcVmX64.Vm.BuildLayout.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset) := hp.label NativeRustcVmX64.Vm.BuildLayout.label_17_at
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, h14, hK0⟩ := ok_b0
  have hb1 : B m0 8 st1.data := Bd.entry hF.stack (by decide) hwf0 hm1 hpro slots_le slots_cs
    (by simp)
  have hK0' := fun r (hr : r ∈ [Reg64.rdi, .rsi, .rcx]) ↦ kreg hm1 hK0 hr
  simp only [PcOk] at hpc1
  obtain ⟨hy0, hno0⟩ := pc_of (P := ¬Pow2 (nN m0)) hpc1 (c0_eval _)
  by_cases hpow : Pow2 (nN m0)
  swap
  · exact fail hp hF ((hy0 hpow).trans L17) hb1 (model_none hF.size fun h ↦ hpow h.1) |>.mono
      fun s h ↦ Or.inl h
  obtain ⟨hok1, -, h1bx, h1r13, hK1⟩ := ok_b1
  refine run0 (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b1Offset + b1.length)).toBitVec) hF
    (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b1 (fun _ _ ↦ rfl) (hno0 (not_not.mpr hpow))
    hb1 hok1 fun st2 hm2 hpc2 hb2 ↦ ?_
  refine callBL hbl hF hpc2 hb2 fun st3 hpc3 hb3 _ hsv3 hax3 ↦ ?_
  have hrdi : reg st2.data .rdi = reg m0 .rdi :=
    (kreg hm2 hK1 (by simp)).trans (hK0' .rdi (by simp))
  refine .done _ (Or.inr ⟨hpc3.trans rfl, hb3, ?_, ?_, ?_, by rw [hax3, hrdi], hpow⟩)
  · exact (hsv3 .rbx rfl).trans ((hm2.regs .rbx _ h1bx).trans (hK0' .rsi (by simp)))
  · exact (hsv3 .r13 rfl).trans ((hm2.regs .r13 _ h1r13).trans (hK0' .rcx (by simp)))
  · exact (hsv3 .r14 rfl).trans ((kreg hm2 hK1 (by simp)).trans (hm1.regs .r14 _ h14))

/-- **The log-sizes**, `b2`. -/
theorem entry2 (hp : Placed code k) (hF : Facts bc m0) {st3 : MachineState}
    (hpc3 : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b2Offset)) (h3 : St3 m0 st3.data) :
    Eventually (step1 Host.exe) (fun s ↦ Post bc m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b3Offset) ∧ St4 m0 s.data))
      st3 := by
  have L17 : Labels.label NativeRustcVmX64.Vm.BuildLayout.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset) := hp.label NativeRustcVmX64.Vm.BuildLayout.label_17_at
  have hbx3 := h3.rbx
  have hax3' := h3.rax
  have hbl1 : 1 ≤ bitLength (nN m0) := bitLength_pos h3.pow2.1
  have hbl64 : bitLength (nN m0) ≤ 64 := bitLength_le (reg m0 .rdi).isLt
  have hlm : lmN m0 < 2 ^ 64 := (reg m0 .rsi).isLt
  -- `b2`: the log-sizes
  obtain ⟨hok2, hmem2, hax2, hK2⟩ := ok_b2
  refine step0 hF (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b2 nofun hpc3
    h3.b hok2 hmem2 fun st4 hm4 hpc4 hb4 _ ↦ ?_
  have v1 : ((dec (.reg .rbx)).eval (frameEnv m0 st3.data 1360 [] (fun _ ↦ 0) 0)).toNat =
      (lmN m0 + 18446744073709551615) % 18446744073709551616 := by
    rw [dec_eval]
    show ((reg st3.data .rbx).toNat + _) % _ = _
    rw [hbx3]
  have v2 : (rM5.eval (frameEnv m0 st3.data 1360 [] (fun _ ↦ 0) 0)).toNat =
      (18446744073709551611 + bitLength (nN m0)) % 18446744073709551616 := by
    rw [rM5_eval]
    show (_ + (reg st3.data .rax).toNat) % _ = _
    rw [hax3']
  simp only [PcOk] at hpc4
  obtain ⟨hy4, hno4⟩ := pc_of (P := ¬(5 ≤ bitLength (nN m0) ∧ 1 ≤ lmN m0 ∧ lmN m0 ≤ 30)) hpc4 (by
    rw [flag_or, ult_eval, ult_eval, v1, v2]
    rw [lit_eval _ (show 30 < 2 ^ 64 by omega),
      lit_eval _ (show 18446744073709551612 < 2 ^ 64 by omega)]
    by_cases ha : (lmN m0 + 18446744073709551615) % 18446744073709551616 < 30
    · by_cases hb' : (18446744073709551611 + bitLength (nN m0)) % 18446744073709551616 < 18446744073709551612
      · rw [decide_eq_true ha, decide_eq_true hb', decide_eq_false (by omega)]; rfl
      · rw [decide_eq_true ha, decide_eq_false hb', decide_eq_true (by omega)]; rfl
    · have hn : ¬(5 ≤ bitLength (nN m0) ∧ 1 ≤ lmN m0 ∧ lmN m0 ≤ 30) := by omega
      rw [decide_eq_false ha, decide_eq_true hn]; rfl)
  by_cases g2 : 5 ≤ bitLength (nN m0) ∧ 1 ≤ lmN m0 ∧ lmN m0 ≤ 30
  swap
  · exact fail hp hF ((hy4 g2).trans L17) hb4 (model_none hF.size fun h ↦ g2 ⟨h.2.1, h.2.2.1,
      h.2.2.2.1⟩) |>.mono fun s h ↦ Or.inl h
  have hK4 := fun r (hr : r ∈ cs) ↦ kreg hm4 hK2 hr
  refine .done _ (Or.inr ⟨(hno4 (not_not.mpr g2)).trans rfl, hb4, ?_, ?_, ?_, ?_, h3.pow2, g2⟩)
  · rw [hK4 .rbx (by simp [cs])]; exact hbx3
  · rw [hK4 .r13 (by simp [cs])]; exact h3.r13
  · rw [hK4 .r14 (by simp [cs])]; exact h3.r14
  · show (st4.data.regs.get64 .rax).toNat = _
    rw [hm4.regs .rax _ hax2, v2]; omega

/-- **The first five row counts**, `b3` to `b7`. -/
theorem rows (hp : Placed code k) (hF : Facts bc m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b3Offset)) (h4 : St4 m0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Post bc m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b8Offset) ∧ St8 m0 s.data))
      st := by
  have L17 : Labels.label NativeRustcVmX64.Vm.BuildLayout.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset) := hp.label NativeRustcVmX64.Vm.BuildLayout.label_17_at
  have hF' : ∀ {s : MachineState} {t : Nat}, s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset) → B m0 8 s.data →
      t < 6 → ¬ (rowW m0 t).toNat ≤ 2 ^ 30 → Eventually (step1 Host.exe)
        (fun s ↦ Post bc m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b8Offset) ∧ St8 m0 s.data)) s :=
    fun hpc hb ht hr ↦ fail hp hF hpc hb (model_none hF.size fun h ↦ hr (h.2.2.2.2.1 _ ht))
      |>.mono fun s h ↦ Or.inl h
  have r14 : ∀ {d : MachineData} {Sy : SState} {e : Env}, Match e Sy d →
      Sy.reg .r14 = some (.ptr 1 0) → e.base 1 = rp m0 → reg d .r14 = rp m0 :=
    fun hm h hb ↦ (hm.regs .r14 _ h).trans (by
      show _ + BitVec.ofInt 64 0 = _; rw [ofInt_zero64, BitVec.add_zero]; exact hb)
  obtain ⟨ok3, mem3, r143, h12, hK3⟩ := ok_b3
  refine rowBlk (t := 0) hF (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b3 ok3 mem3
    (by decide) L17 hpc h4.b h4.r14
    (fun s hpc hb hr ↦ hF' hpc hb (by decide) hr) fun s5 hm5 hpc5 hb5 _ hlr0 g3 ↦ ?_
  obtain ⟨ok4, mem4, r144, hbp, hK4⟩ := ok_b4
  refine rowBlk (t := 1) hF (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b4 ok4 mem4
    (by decide) L17 hpc5 hb5 (r14 hm5 r143 rfl)
    (fun s hpc hb hr ↦ hF' hpc hb (by decide) hr) fun s6 hm6 hpc6 hb6 _ hlr1 g4 ↦ ?_
  obtain ⟨ok5, mem5, r145, h15, hK5⟩ := ok_b5
  refine rowBlk (t := 2) hF (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b5 ok5 mem5
    (by decide) L17 hpc6 hb6 (r14 hm6 r144 rfl)
    (fun s hpc hb hr ↦ hF' hpc hb (by decide) hr) fun s7 hm7 hpc7 hb7 _ hlr2 g5 ↦ ?_
  obtain ⟨ok6, mem6, r146, h8, hK6⟩ := ok_b6
  refine rowBlk (t := 3) hF (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b6 ok6 mem6
    (by decide) L17 hpc7 hb7 (r14 hm7 r145 rfl)
    (fun s hpc hb hr ↦ hF' hpc hb (by decide) hr) fun s8 hm8 hpc8 hb8 _ hlr3 g6 ↦ ?_
  obtain ⟨ok7, mem7, r147, hdi, hK7⟩ := ok_b7
  refine rowBlk (t := 4) hF (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b7 ok7 mem7
    (by decide) L17 hpc8 hb8 (r14 hm8 r146 rfl)
    (fun s hpc hb hr ↦ hF' hpc hb (by decide) hr) fun s9 hm9 hpc9 hb9 _ hlr4 g7 ↦ ?_
  have k9 : ∀ r ∈ [Reg64.rax, .rbx, .r13], reg s9.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
    · rw [kreg hm9 hK7 (by simp), kreg hm8 hK6 (by simp), kreg hm7 hK5 (by simp),
        kreg hm6 hK4 (by simp), kreg hm5 hK3 (by simp)]
  refine .done _ (Or.inr ⟨hpc9.trans rfl, ⟨hb9, ?_, ?_, r14 hm9 r147 rfl, ?_, h4.pow2, h4.g2⟩,
    ?_, ?_, ?_, ?_, ?_, fun t ht ↦ ?_⟩)
  · rw [k9 .rbx (by simp)]; exact h4.rbx
  · rw [k9 .r13 (by simp)]; exact h4.r13
  · rw [k9 .rax (by simp)]; exact h4.rax
  · rw [kreg hm9 hK7 (by simp), kreg hm8 hK6 (by simp), kreg hm7 hK5 (by simp),
      kreg hm6 hK4 (by simp)]
    exact (hm5.regs .r12 _ h12).trans hlr0
  · rw [kreg hm9 hK7 (by simp), kreg hm8 hK6 (by simp), kreg hm7 hK5 (by simp)]
    exact (hm6.regs .rbp _ hbp).trans hlr1
  · rw [kreg hm9 hK7 (by simp), kreg hm8 hK6 (by simp)]
    exact (hm7.regs .r15 _ h15).trans hlr2
  · rw [kreg hm9 hK7 (by simp)]
    exact (hm8.regs .r8 _ h8).trans hlr3
  · exact (hm9.regs .rdi _ hdi).trans hlr4
  · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [g3, g4, g5, g6, g7]

/-- **The last check**, `b8`: the last row count, the bytecode's log-size. -/
theorem last (hp : Placed code k) (hF : Facts bc m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b8Offset)) (h8 : St8 m0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Post bc m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b9Offset) ∧ St9 m0 s.data))
      st := by
  have L17 : Labels.label NativeRustcVmX64.Vm.BuildLayout.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset) := hp.label NativeRustcVmX64.Vm.BuildLayout.label_17_at
  have hb := h8.s4.b
  have hpr : NativeRustcVm.Mapped m0.dmem (rp m0) 48 ∧ NativeRustcVm.NoWrap (rp m0) 48 := hF.rr
  have hpf : NativeRustcVm.Apart (stackBelow m0 1360) (1360 + 8) (rp m0) 48 :=
    Apart.symm' (apart_frame hF.ro hF.rsp.1 (by decide))
  have hwf := fr_wf1 (vars := fun _ ↦ 0) (ret := 0) hb hF.stack (by decide) hpr.1 hpr.2 hpf
  have hm : Match (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0) rowS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, by
      show reg st.data .r14 = rp m0 + BitVec.ofInt 64 0
      rw [ofInt_zero64, BitVec.add_zero, h8.s4.r14], trivial⟩ trivial trivial trivial
  have hl5 : (Sym.load 1 40 8).eval (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0) =
      (rowW m0 5).toBitVec := by
    show (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0) 0).load 1 40 8 = _
    rw [Arrays.load8_eq]
    show (wordOf st.data.dmem (rp m0 + BitVec.ofNat 64 (8 * 5))).toBitVec = _
    exact congrArg UInt64.toBitVec (row_same hF hb (by decide))
  obtain ⟨ok8, mem8, r148, hsi, hK8⟩ := ok_b8
  refine exec_at (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b8 hwf nofun hpc hm
    fun s10 hm10 hpc10 ↦ ?_
  have hb10 : B m0 8 s10.data := hb.of_read hwf hm10 ok8 slots_le mem8
  have hax := h8.s4.rax
  have hbl64 : bitLength (nN m0) ≤ 64 := bitLength_le (reg m0 .rdi).isLt
  simp only [PcOk] at hpc10
  obtain ⟨hy10, hno10⟩ := pc_of (P := ¬(bitLength (nN m0) - 5 ≤ 30 ∧ (rowW m0 5).toNat ≤ 2 ^ 30))
    hpc10 (by
      rw [flag_or]
      show (!CmpOp.apply .ult .W32 (reg st.data .rax) (BitVec.ofNat 64 31) ||
        !(SBool.cmp .ult .W64 (.load 1 40 8) (.lit 1073741825)).eval _) = _
      rw [ult_eval, hl5]
      simp only [CmpOp.apply, BitVec.ult, toNat_low, Width.bits, hax, BitVec.toNat_ofNat]
      have h31 : (31 : Nat) % 2 ^ 64 % 2 ^ 32 = 31 := by decide
      have hr : ((Sym.lit 1073741825).eval (frameEnv m0 st.data 1360 [(rp m0, 48)] (fun _ ↦ 0)
        0)).toNat = 1073741825 := rfl
      rw [h31, hr, Nat.mod_eq_of_lt (show bitLength (nN m0) - 5 < 2 ^ 32 by omega),
        UInt64.toNat_toBitVec]
      by_cases ha : bitLength (nN m0) - 5 < 31
      · by_cases hb' : (rowW m0 5).toNat < 1073741825
        · rw [decide_eq_true ha, decide_eq_true hb', decide_eq_false (by omega)]; rfl
        · rw [decide_eq_true ha, decide_eq_false hb', decide_eq_true (by omega)]; rfl
      · have hn : ¬(bitLength (nN m0) - 5 ≤ 30 ∧ (rowW m0 5).toNat ≤ 2 ^ 30) := by omega
        rw [decide_eq_false ha, decide_eq_true hn]; rfl)
  by_cases g8 : bitLength (nN m0) - 5 ≤ 30 ∧ (rowW m0 5).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((hy10 g8).trans L17) hb10 (model_none hF.size fun h ↦ g8
      ⟨h.2.2.2.2.2, h.2.2.2.2.1 5 (by decide)⟩) |>.mono fun s h ↦ Or.inl h
  have r10 := fun r (hr : r ∈ [Reg64.rax, .rbx, .rbp, .r12, .r13, .r15, .r8, .rdi]) ↦
    kreg hm10 hK8 hr
  have g2 := h8.s4.g2
  refine .done _ (Or.inr ⟨(hno10 (not_not.mpr g8)).trans rfl, hb10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h8.s4.pow2, ⟨g2.1, g2.2.1, g2.2.2, fun t ht ↦ ?_, g8.1⟩⟩)
  · rw [r10 .rbx (by simp)]; exact h8.s4.rbx
  · rw [r10 .r13 (by simp)]; exact h8.s4.r13
  · exact (hm10.regs .r14 _ r148).trans (by
      show _ + BitVec.ofInt 64 0 = _; rw [ofInt_zero64, BitVec.add_zero]; rfl)
  · rw [r10 .rax (by simp)]; exact hax
  · rw [r10 .r12 (by simp)]; exact h8.r12
  · rw [r10 .rbp (by simp)]; exact h8.rbp
  · rw [r10 .r15 (by simp)]; exact h8.r15
  · rw [r10 .r8 (by simp)]; exact h8.r8
  · rw [r10 .rdi (by simp)]; exact h8.rdi
  · exact (hm10.regs .rsi _ hsi).trans hl5
  · by_cases h5 : t = 5
    · subst h5; exact g8.2
    · exact h8.rows t (by omega)

/-- **The entry and the checks.** -/
theorem checks (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hF : Facts bc m0) :
    Eventually (step1 Host.exe) (fun s ↦ Post bc m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b9Offset) ∧ St9 m0 s.data))
      ⟨m0, Labels.label NativeRustcVmX64.Vm.BuildLayout.entryLabel⟩ :=
  (entry1 hp hbl hF).bind fun _ h ↦ h.elim (fun h ↦ .done _ (Or.inl h)) fun ⟨hpc, h3⟩ ↦
    (entry2 hp hF hpc h3).bind fun _ h ↦ h.elim (fun h ↦ .done _ (Or.inl h)) fun ⟨hpc, h4⟩ ↦
    (rows hp hF hpc h4).bind fun _ h ↦ h.elim (fun h ↦ .done _ (Or.inl h)) fun ⟨hpc, h8⟩ ↦
      last hp hF hpc h8

end

end NativeRustcVmX64.Layout.BuildLayout
