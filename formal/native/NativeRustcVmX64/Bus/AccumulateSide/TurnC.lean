module

public import NativeRustcVmX64.Bus.AccumulateSide.TurnB
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names

/-!
# `accumulate_side`: the table loop's turn, the form added (x86-64)

`b21` reads the owner's padding span from `TABLES` and calls `FormBuf::add_scaled` on the owner's
form of the side with the block's form and its selector; `b22` is its failure exit, never taken
(the forms fit): `turnC`, from `b21` to `b23`, the forms those after turn `j`.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

section
variable [Labels] (env : Env)

theorem five_eval {o : Nat} (h : env.regs .rsi = BitVec.ofNat 64 o) :
    five.eval env = BitVec.ofNat 64 (5 * o) := by
  show BinOp.apply .add .W64 (env.regs .rsi) (BinOp.apply .mul .W64 (env.regs .rsi)
    (BitVec.ofNat 64 4)) = _
  rw [add64, mul64, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem five8_eval {o : Nat} (ho : o < 6) (h : env.regs .rsi = BitVec.ofNat 64 o) :
    (five8.eval env).toNat = 40 * o := by
  show (BinOp.apply .mul .W64 (five.eval env) (BitVec.ofNat 64 8)).toNat = _
  rw [mul64, five_eval env h]
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem r13T_eval {s : Nat} (hs : s ≤ 148) (h : env.load 0 6056 8 = BitVec.ofNat 64 s) :
    r13T.eval env = BitVec.ofNat 64 s := by
  show (if (!(CmpOp.apply .ult .W64 (env.load 0 6056 8) (BitVec.ofNat 64 149))) = true then
    BitVec.ofNat 64 0 else env.load 0 6056 8) = _
  rw [h]
  simp only [CmpOp.apply, low_W64, ult_ofNat (by omega : s < 2 ^ 64) (by decide : 149 < 2 ^ 64)]
  simp [show s < 149 by omega]

theorem rbpT_eval {s : Nat} (hs : s ≤ 148) (h : env.load 0 6056 8 = BitVec.ofNat 64 s) :
    rbpT.eval env = (Sym.ptr 0 6064).eval env := by
  show (if CmpOp.apply .ult .W64 (env.load 0 6056 8) (BitVec.ofNat 64 149) = true then
    (Sym.ptr 0 6064).eval env else BitVec.ofNat 64 8) = _
  rw [h]
  simp only [CmpOp.apply, low_W64, ult_ofNat (by omega : s < 2 ^ 64) (by decide : 149 < 2 ^ 64)]
  simp [show s < 149 by omega]

end

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- `TABLES` as an input region. -/
theorem tables_in (h : Pre L rows bl Fm SL m0) : In m0 (rodataAddr .tables) 240 := by
  obtain ⟨hb, hnw, hA⟩ := h.rodata .tables
  rw [tables_len] at hnw hA
  have hf := h.formsRo .tables
  rw [tables_len] at hf
  have hm := hb.mapped
  rw [tables_len] at hm
  exact ⟨hm, hnw, Apart.symm' hf, hA⟩

/-- **The table loop's turn `j`, from `b21` to `b23`.** -/
theorem turnC (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g)
      (FormBufAddScaledPost f g))
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (outs m0) (VT L rows bl Fm SL m0 j) D20 8 m) (hfb : FB m0 m.dmem (fmA L rows bl m0 j))
    (hG : FormsAt m.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 j).1) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (outs m0) (VT L rows bl Fm SL m0 j) (D21c ++ E21) 8 m2 →
      FB m0 m2.dmem (fmA L rows bl m0 j) →
      FormsAt m2.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b21Offset)⟩ := by
  obtain ⟨-, -, -, -, -, hlo21, hlo22, -⟩ := low_T
  let V := VT L rows bl Fm SL m0 j
  let G := (stA L rows bl Fm SL m0 j).1
  have hbx : bkA L rows bl j = blockW L.tableLogHeights rows bl[j] := BA_getD L rows bl hj
  have ho6 : (bkA L rows bl j).owner < 6 := by
    rw [hbx]; exact (h.bown _ (List.getElem_mem hj)).1
  have hside : (reg m0 .rdx).toNat < 3 := h.side
  obtain ⟨g1, g2⟩ := sta_shape h j
  have hoG : (bkA L rows bl j).owner < G.size := by rw [g1]; exact ho6
  have hsG : (reg m0 .rdx).toNat < G[(bkA L rows bl j).owner].size := by rw [g2 _ hoG]; exact hside
  let o := (bkA L rows bl j).owner
  let sd := (reg m0 .rdx).toNat
  let slot := off (reg m0 .rsi) (formBufBytes * (3 * o + sd))
  have hTIn := tables_in h
  have hsize : (fmA L rows bl m0 j).size ≤ 148 := hfb.len_le
  -- `b21`: the padding span, the call's arguments.
  let env1 := frameEnv m0 m F [(rodataAddr .tables, 240)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b21Offset + b21.length)).toBitVec
  have hwf1 : env1.WF := wf1 h hst.fr.kept hTIn
  have e_si : env1.regs .rsi = BitVec.ofNat 64 o := hst.hd.reg (r := .rsi) (i := 39) (by decide)
  have g6056 : env1.load 0 6056 8 = BitVec.ofNat 64 (fmA L rows bl m0 j).size :=
    load_ofMachine (r := 0) rfl hfb.len
  have g88 : env1.load 0 88 8 = reg m0 .rdx * 5928#64 + reg m0 .rsi := by
    rw [show env1.load 0 88 8 = (Env.ofMachine m [(fb m0, F + 8)]).load 0 88 8 from rfl,
      hst.hd.load (r := 0) (o := 88) (i := 24) (by decide)]
    rfl
  have htw : ∀ i, i < 30 → env1.load 1 (8 * i) 8 = (twA i).toBitVec := fun i hi ↦
    load_ofMachine (r := 1) rfl (St.word h hst outs_id hTIn (j := 8 * i) (by omega)
      (tables_word h.rodata hi))
  have hm1 : Match env1 tS m :=
    St.mt hst ⟨rfl, rfl, trivial⟩ ⟨rfl, trivial⟩
      ⟨by change (five.eval env1).toNat < 26
          rw [five_eval env1 e_si, toNat_ofNat_lt (by omega)]; omega, trivial⟩ trivial
  obtain ⟨hmid1, hw1, htr1, h13, hbp, hsi, hdx, hdi, h12, h24⟩ := ok_b21
  refine St.run h (rest := [(rodataAddr .tables, 240)]) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b21Offset + b21.length)).toBitVec) rfl
    (infix_of b21_in_code (by simp [b21]) hp) exit_b21 (fun _ _ ↦ rfl) hst.fr hst.same
    (hst.hd.reg0 (rs' := (fb m0, F + 8) :: [(rodataAddr .tables, 240)]) (by decide) rfl)
    (by decide) hwf1 hm1 hmid1 hw1 (by decide) htr1 fun st2 hm2 hpc2 hst2 hc2 ↦ ?_
  have hk2 : KeepF m0 m.dmem st2.data.dmem := run_keep hwf1 hm2 hlo21 (writesIn_of_mid hmid1)
  have hG2 := KeepF.forms h hk2 hG
  have hfb2 := KeepF.fbuf hk2 hfb
  have hsp2 : rspOf st2.data = fb m0 := by rw [hst2.fr.sp, off_zero]
  have e13 : st2.data.regs.get64 .r13 = BitVec.ofNat 64 (fmA L rows bl m0 j).size :=
    (hm2.regs .r13 _ h13).trans (r13T_eval env1 hsize g6056)
  have edx : st2.data.regs.get64 .rdx = BitVec.ofNat 64 (fmA L rows bl m0 j).size :=
    (hm2.regs .rdx _ hdx).trans (r13T_eval env1 hsize g6056)
  have ebp : st2.data.regs.get64 .rbp = off (fb m0) 6064 :=
    ((hm2.regs .rbp _ hbp).trans (rbpT_eval env1 hsize g6056)).trans (eval_ptr0 6064)
  have esi : st2.data.regs.get64 .rsi = off (fb m0) 6064 :=
    ((hm2.regs .rsi _ hsi).trans (rbpT_eval env1 hsize g6056)).trans (eval_ptr0 6064)
  have edi : st2.data.regs.get64 .rdi = slot := by
    rw [hm2.regs .rdi _ hdi]
    show BinOp.apply .add .W64 (env1.load 0 88 8)
      (BinOp.apply .mul .W64 (env1.regs .rsi) (BitVec.ofNat 64 17784)) = _
    rw [add64, mul64, g88, e_si]
    exact slot_addr _ _ rfl
  have e12 : st2.data.regs.get64 .r12 = (twA (5 * o + 3)).toBitVec := by
    rw [hm2.regs .r12 _ h12]
    show env1.load 1 (24 + (five8.eval env1).toNat) 8 = _
    rw [five8_eval env1 ho6 e_si, show 24 + 40 * o = 8 * (5 * o + 3) by omega]
    exact htw _ (by omega)
  have e24 : (Sym.loadx 1 32 five8 8).eval env1 = (twA (5 * o + 4)).toBitVec := by
    show env1.load 1 (32 + (five8.eval env1).toNat) 8 = _
    rw [five8_eval env1 ho6 e_si, show 32 + 40 * o = 8 * (5 * o + 4) by omega]
    exact htw _ (by omega)
  have hE : Holds [(fb m0, F + 8)] V E21 st2.data :=
    holds_reg (i := 41) e13 (holds_reg (i := 42) ebp (holds_reg (i := 43) e12
      (holds_content (s := Lw 24) (i := 44) (hc2 _ _ rfl h24) e24 (holds_nil _ _ _))))
  have e_cx : reg st2.data .rcx = (tsel SL (ptA m0) j).c0.toBitVec :=
    hst2.hd.reg (r := .rcx) (i := 37) (by decide)
  have e_r8 : reg st2.data .r8 = (tsel SL (ptA m0) j).c1.toBitVec :=
    hst2.hd.reg (r := .r8) (i := 38) (by decide)
  have hst2c : St m0 (outs m0) V (D21c ++ E21) 0 st2.data :=
    St.sub (St.add hst2 (fun _ _ ↦ rfl) hE) (by decide)
  -- `FormBuf::add_scaled`.
  let f := G[o][sd]
  have hslot := St.slotOk h hst2c le_as ho6 hside
  have hterms : InOk st2.data (off (fb m0) 6064) (termBytes * (fmA L rows bl m0 j).size)
      formBufAddScaledStack :=
    inOk_prefix (frame_inOk h hst2c.fr.kept hsp2 le_as (o := 6064) (n := 5920) (by decide)
      (by decide) (by decide)) (by unfold termBytes; omega)
  have hpre : FormBufAddScaledPre f (fmA L rows bl m0 j) st2.data := by
    refine ⟨St.stackOk h hst2c le_as, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (st2.data.regs.get64 .rdx).toNat = _
      rw [edx, toNat_ofNat_lt (by omega)]
    · show FormBufAt _ (st2.data.regs.get64 .rdi) _
      rw [edi]; exact hG2.forms o hoG sd hsG
    · show TermsAt _ (st2.data.regs.get64 .rsi) _
      rw [esi, ← off_off (fb m0) 6056 8]
      exact hfb2.terms
    · show Readable _ (st2.data.regs.get64 .rdi) _
      rw [edi]; exact hslot.1
    · show OffStack _ (st2.data.regs.get64 .rdi) _ _
      rw [edi]; exact hslot.2
    · show Readable _ (st2.data.regs.get64 .rsi) (termBytes * (st2.data.regs.get64 .rdx).toNat)
      rw [esi, edx, toNat_ofNat_lt (by omega)]; exact hterms.1
    · show OffStack _ (st2.data.regs.get64 .rsi) (termBytes * (st2.data.regs.get64 .rdx).toNat) _
      rw [esi, edx, toNat_ofNat_lt (by omega)]; exact hterms.2
    · show Apart (st2.data.regs.get64 .rdi) _ (st2.data.regs.get64 .rsi)
        (termBytes * (st2.data.regs.get64 .rdx).toNat)
      rw [edi, esi, edx, toNat_ofNat_lt (by omega)]
      exact apart_shrink (Apart.symm' (h.frame_apart (h.slot_stack ho6 hside) (o := 6064)
        (n := 5920) (by decide) (by decide))) (by unfold termBytes; omega)
  have hW : ∀ q, NativeRustcVm.InRange slot formBufBytes q →
      outs m0 q ∧ ¬ NativeRustcVm.InRange (fb m0) (F + 8) q := fun q hq ↦ by
    have : outs m0 q := inRange_of_off h.forms_nw (by
      have hf : formBufBytes = 5928 := rfl
      have hfs : formsBytes = 106704 := rfl
      rw [hf, hfs]; omega) hq
    exact ⟨this, h.outs_frame this⟩
  have hso : ∀ m', FormBufAddScaledPost f (fmA L rows bl m0 j) st2.data m' →
      NativeRustcVm.SameOutside st2.data.dmem m'.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st2.data formBufAddScaledStack)
          formBufAddScaledStack q ∨ NativeRustcVm.InRange (off (fb m0) 0) 0 q ∨
        NativeRustcVm.InRange slot formBufBytes q) := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h1 ↦ .inr (.inr (by rw [← edi]; exact h1))) .inl
  refine St.call h hst2c le_as (lo := 0) (n := 0) (by decide) (by decide) (has _ _) hpc2 hpre
    (W := NativeRustcVm.InRange slot formBufBytes) hW (fun m' hq ↦ ⟨hso m' hq, hq.2.2⟩)
    fun m3 hst3 hq3 ↦ ?_
  have hfb3 := call_fb h hsp2 le_as (by decide) (fun q hq ↦ (hW q hq).2) (hso m3 hq3) hfb2
  have hew : ewArg (reg st2.data .rcx) (reg st2.data .r8) = tsel SL (ptA m0) j := by
    rw [e_cx, e_r8]; rfl
  have hfit : (f.addScaled (fmA L rows bl m0 j) (tsel SL (ptA m0) j)).size ≤ formCap := by
    have := slot_fits h (j := j + 1) (by omega) ho6 hside
    rw [slot_succ h j ho6, slotOf_eq hoG hsG] at this
    exact this
  have hq31 := hq3.1
  simp only [hew, hfit, ↓reduceIte] at hq31
  obtain ⟨hal3, hx3⟩ := hq31
  rw [show reg st2.data .rdi = slot from edi] at hx3
  have hG3 : FormsAt m3.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1 := by
    rw [stA_succ_fst]
    refine FormsAt.modify hG2 hoG hsG _ hx3 h.forms_nw
      (Z := NativeRustcVm.InRange (stackBelow st2.data formBufAddScaledStack)
        formBufAddScaledStack)
      (NativeRustcVm.SameOutside.mono hq3.2.1 fun q hq' ↦ hq'.elim
        (fun h1 ↦ .inl (by change NativeRustcVm.InRange slot formBufBytes q; rw [← edi]; exact h1)) .inr) fun i hi hq ↦
      (forms_out h hi).2 (inRange_callee hsp2 h.sp8 h.spN le_as hq).1
  -- `b22`: `add_scaled`'s failure exit, not taken.
  show Eventually _ _ (⟨m3, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b22Offset)⟩ : MachineState)
  obtain ⟨-, -, -, hmid4, hw4, htr4⟩ := ok_b19
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b22_in_code (by simp [b22]) hp) exit_b22 nofun hst3.fr hst3.same
    (hst3.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst3.fr.kept)
    (St.mt hst3 ⟨rfl, trivial⟩ trivial trivial trivial) hmid4 hw4 (by decide) htr4
    fun st4 hm4 hpc4 hst4 _ ↦ ?_
  have hk4 : KeepF m0 m3.dmem st4.data.dmem :=
    run_keep (wf0 h hst3.fr.kept) hm4 hlo22 (writesIn_of_mid hmid4)
  have hc4 : cAl.eval (frameEnv m0 m3 F [] (fun _ ↦ 0) 0) = false := cAl_false hal3
  simp only [PcOk] at hpc4
  rw [hc4] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset) := hpc4
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4' hst4 hk4
  subst hpc4'
  exact cont d4 hst4 (KeepF.fbuf hk4 hfb3) (KeepF.forms h hk4 hG3)

end

end NativeRustcVmX64.Bus.AccumulateSide
