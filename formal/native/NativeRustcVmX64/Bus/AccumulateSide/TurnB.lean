module

public import NativeRustcVmX64.Bus.AccumulateSide.TPre
public import NativeRustcVmX64.Code.Vm.BlockForm.Names

/-!
# `accumulate_side`: the table loop's turn, the block's form (x86-64)

`b18a` keeps the selector and reads block `j`'s tuple, `b18b` calls `block_form` into the frame's
`FormBuf`; `b19` (its failure exit, never taken: the form fits) and `b20` (the owner past `5`,
never) read the owner: `turnB`, from `eq_above`'s return to `b21`.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- `b19`'s, `b22`'s exit: AL `0`, never when AL is `1`. -/
theorem cAl_false [Labels] {env : Env} (h : (env.regs .rax).toNat % 256 = 1) :
    cAl.eval env = false := by
  show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (env.regs .rax) (env.regs .rax))
    (BitVec.ofNat 64 0) = false
  rw [NativeRustcVmX64.Sumcheck.testAl_eq, h]
  rfl

/-- `b20`'s exit: the owner past `5`, never for an owner below `6`. -/
theorem c20_false {x : BitVec 64} (hx : x.toNat < 6) :
    (!(CmpOp.apply .ult .W64 x (BitVec.ofNat 64 5)) &&
      !(CmpOp.apply .eq .W64 x (BitVec.ofNat 64 5))) = false := by
  rw [eq64]
  simp only [CmpOp.apply, low_W64, BitVec.ult]
  by_cases h5 : x.toNat < 5
  · simp [h5]
  · have : x = BitVec.ofNat 64 5 := BitVec.eq_of_toNat_eq (by simp; omega)
    simp [this]

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- Block `j`, region `1` of `b18a` and `b20`. -/
theorem blk_in (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    In m0 (off (reg m0 .rcx) (16 * j)) 16 :=
  (In.of_inOk h.blocksOk (Apart.symm' h.fB)).sub (by omega) (by decide)

/-- **The table loop's turn `j`, from `eq_above`'s return to `b21`.** -/
theorem turnB (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hbf : Spec (Labels.label NativeRustcVmX64.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (outs m0) (VT L rows bl Fm SL m0 j) D17 8 m) (hret : ewRet m = tsel SL (ptA m0) j)
    (hG : FormsAt m.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 j).1) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (outs m0) (VT L rows bl Fm SL m0 j) D20 8 m2 →
      FB m0 m2.dmem (fmA L rows bl m0 j) →
      FormsAt m2.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 j).1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b21Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b18Offset)⟩ := by
  obtain ⟨-, hlo18a, hlo18b, hlo19, hlo20, -⟩ := low_T
  let V := VT L rows bl Fm SL m0 j
  let blk := off (reg m0 .rcx) (16 * j)
  have hbIn : In m0 blk 16 := blk_in h hj
  have hBl : In m0 (reg m0 .rcx) (16 * bl.length) := In.of_inOk h.blocksOk (Apart.symm' h.fB)
  have hbw := block_words h hj
  have hbx : bkA L rows bl j = blockW L.tableLogHeights rows bl[j] := BA_getD L rows bl hj
  -- `b18a`: the selector kept, the tuple read.
  let env1 := frameEnv m0 m F [(blk, 16)] (fun _ ↦ 0) 0
  have hwf1 : env1.WF := wf1 h hst.fr.kept hbIn
  have g96 : env1.load 0 96 8 = reg m0 .rcx := by
    rw [show env1.load 0 96 8 = (Env.ofMachine m [(fb m0, F + 8)]).load 0 96 8 from rfl,
      hst.hd.load (r := 0) (o := 96) (i := 3) (by decide)]
    rfl
  have hr12 := hst.hd.reg (r := .r12) (i := 32) (by decide)
  have hm1 : Match env1 bS m :=
    St.mt hst ⟨rfl, rfl, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (env1.load 0 96 8) (m.regs.get64 .r12) = blk + BitVec.ofInt 64 0
      rw [add64, g96, hr12, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      rfl, trivial⟩
  have hax : m.regs.get64 .rax = (V 37).toBitVec := by
    show _ = (tsel SL (ptA m0) j).c0.toBitVec; rw [← hret]; rfl
  have hdx : m.regs.get64 .rdx = (V 38).toBitVec := by
    show _ = (tsel SL (ptA m0) j).c1.toBitVec; rw [← hret]; rfl
  obtain ⟨hmid1, hw1, htr1, hdi1⟩ := ok_b18a
  refine St.run h (rest := [(blk, 16)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b18a_in_code (by simp [b18a, b18]) hp)
    exit_b18a nofun hst.fr hst.same
    ((hst.hd.append (holds_reg hax (holds_reg hdx (holds_nil _ _ _)))).reg0
      (rs' := (fb m0, F + 8) :: [(blk, 16)]) (by decide) rfl) (by decide) hwf1 hm1 hmid1 hw1
    (by decide) htr1 fun st2 hm2 hpc2 hst2 _ ↦ ?_
  have hk2 : KeepF m0 m.dmem st2.data.dmem := run_keep hwf1 hm2 hlo18a (writesIn_of_mid hmid1)
  have hG2 := KeepF.forms h hk2 hG
  have htup : env1.load 1 8 8 = BitVec.ofNat 64 bl[j].tuple :=
    St.load h hst outs_id hBl (r := 1) (j := 16 * j) rfl (o' := 8) (by omega) hbw.2
  have e_di : st2.data.regs.get64 .rdi = (V 40).toBitVec := by
    rw [hm2.regs .rdi _ hdi1]
    show env1.load 1 8 8 = ((((bl[j]?).map NativeRustcVm.Data.Block.tuple).getD 0).toUInt64).toBitVec
    rw [htup, List.getElem?_eq_getElem hj]
    rfl
  have hst2' : St m0 (outs m0) V D18 8 st2.data :=
    St.sub (St.add hst2 (fun _ _ ↦ rfl) (holds_reg e_di (holds_nil _ _ _))) (by decide)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b18Offset + b18a.length) := hpc2
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2' hst2' hG2
  subst hpc2'
  -- `b18b`: `block_form`.
  let env3 := frameEnv m0 d2 F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b18Offset + b18a.length + b18b.length)).toBitVec
  obtain ⟨hmid3, hw3, htr3, hr93⟩ := ok_b18b
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b18Offset + b18a.length + b18b.length)).toBitVec) rfl
    (infix_of (F := code) (k := k) (j := NativeRustcVmX64.Vm.AccumulateSide.b18Offset + b18a.length) b18b_in_code (by simp [b18b, b18]) hp) exit_b18b (fun _ _ ↦ rfl) hst2'.fr
    hst2'.same ((hst2'.hd.reg0 (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88)]) (by decide)
      rfl).append (St.holdsDA h hst2' outs_id)) (by decide) (wf1 h hst2'.fr.kept h.argsIn)
    (St.mt hst2' ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid3 hw3 (by decide) htr3
    fun st4 hm4 hpc4 hst4 _ ↦ ?_
  have hk4 : KeepF m0 d2.dmem st4.data.dmem :=
    run_keep (wf1 h hst2'.fr.kept h.argsIn) hm4 hlo18b (writesIn_of_mid hmid3)
  have hG4 := KeepF.forms h hk4 hG2
  have hsp4 : rspOf st4.data = fb m0 := by rw [hst4.fr.sp, off_zero]
  have e_r9 : reg st4.data .r9 = off (fb m0) 6056 := (hm4.regs .r9 _ hr93).trans (eval_ptr0 6056)
  have e_di4 : reg st4.data .rdi = BitVec.ofNat 64 bl[j].tuple := by
    rw [show reg st4.data .rdi = _ from hst4.hd.reg (r := .rdi) (i := 40) (by decide)]
    show ((((bl[j]?).map NativeRustcVm.Data.Block.tuple).getD 0).toUInt64).toBitVec = _
    rw [List.getElem?_eq_getElem hj]
    rfl
  have e_si4 : reg st4.data .rsi = stackArg m0 3 := hst4.hd.reg (r := .rsi) (i := 9) (by decide)
  have e_dx4 : reg st4.data .rdx = stackArg m0 4 := hst4.hd.reg (r := .rdx) (i := 10) (by decide)
  have e_cx4 : reg st4.data .rcx = stackArg m0 5 := hst4.hd.reg (r := .rcx) (i := 11) (by decide)
  have e_r84 : reg st4.data .r8 = stackArg m0 6 := hst4.hd.reg (r := .r8) (i := 12) (by decide)
  have htl := (h.bown _ (List.getElem_mem hj)).2
  have htlen : NativeRustcVm.Data.tuples.length < 2 ^ 64 := by rw [tuples_length]; decide
  have hst4c : St m0 (outs m0) V D18c 0 st4.data := St.sub hst4 (by decide)
  have hpre : BlockFormPre st4.data := by
    refine ⟨St.stackOk h hst4c le_bf, St.rodata h hst4c outs_id le_bf, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_di4, toNat_ofNat_lt (by omega)]; exact htl
    · rw [e_si4, e_dx4]; exact St.sliceOk h hst4c le_bf h.w
    · rw [e_r9]; exact frame_inOk h hst4c.fr.kept hsp4 le_bf (by decide) (by decide) (by decide)
    · rw [e_r9]; exact h.frame_roApart (by decide) (by decide)
    · rw [e_r9, e_si4, e_dx4]; exact h.frame_apart h.w.2 (by decide) (by decide)
  have hso : ∀ m', BlockFormPost st4.data m' → NativeRustcVm.SameOutside st4.data.dmem m'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow st4.data blockFormStack) blockFormStack q ∨
        NativeRustcVm.InRange (off (fb m0) 6056) formBufBytes q ∨ Z q) := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h1 ↦ .inr (.inl (by rw [← e_r9]; exact h1))) .inl
  refine St.call h hst4c le_bf (lo := 6056) (n := formBufBytes) (by decide) (by decide) hbf hpc4
    hpre (W := Z) (fun _ h ↦ h.elim) (fun m' hq ↦ ⟨hso m' hq, hq.2.2⟩) fun m5 hst5 hq5 ↦ ?_
  have hG5 := call_forms h hsp4 le_bf (by decide) (hso m5 hq5) hG4
  have hg : blockForm ⟨0, 0, tupleOf (reg st4.data .rdi).toNat, 0⟩
      (slice st4.data (reg st4.data .rsi) (reg st4.data .rdx))
      (ewArg (reg st4.data .rcx) (reg st4.data .r8)) = fmA L rows bl m0 j := by
    rw [e_di4, toNat_ofNat_lt (by omega), e_si4, e_dx4, e_cx4, e_r84,
      St.slice_eq h hst4c outs_id h.w (Apart.symm' h.fW)]
    show _ = blockForm (bkA L rows bl j) (wA m0) (betaA m0)
    rw [hbx]
    exact blockForm_coords rfl _ _
  have hfit : (fmA L rows bl m0 j).size ≤ formCap := form_fits h hj
  have hq51 := hq5.1
  rw [hg] at hq51
  simp only [hfit, ↓reduceIte] at hq51
  obtain ⟨hal5, hfb5⟩ := hq51
  rw [e_r9] at hfb5
  -- `b19`: `block_form`'s failure exit, not taken.
  show Eventually _ _ (⟨m5, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b19Offset)⟩ : MachineState)
  obtain ⟨hmid6, hw6, htr6, -⟩ := ok_b19
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b19_in_code (by simp [b19]) hp) exit_b19 nofun hst5.fr hst5.same
    (hst5.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst5.fr.kept)
    (St.mt hst5 ⟨rfl, trivial⟩ trivial trivial trivial) hmid6 hw6 (by decide) htr6
    fun st6 hm6 hpc6 hst6 _ ↦ ?_
  have hk6 : KeepF m0 m5.dmem st6.data.dmem :=
    run_keep (wf0 h hst5.fr.kept) hm6 hlo19 (writesIn_of_mid hmid6)
  have hc6 : cAl.eval (frameEnv m0 m5 F [] (fun _ ↦ 0) 0) = false := cAl_false hal5
  simp only [PcOk] at hpc6
  rw [hc6] at hpc6
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc6
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b20Offset) := hpc6
  obtain ⟨d6, pc6⟩ := st6
  simp only at hpc6' hst6 hk6
  subst hpc6'
  have hG6 := KeepF.forms h hk6 hG5
  have hfb6 := KeepF.fbuf hk6 hfb5
  -- `b20`: the owner, never past `5`.
  let env7 := frameEnv m0 d6 F [(blk, 16)] (fun _ ↦ 0) 0
  have hwf7 : env7.WF := wf1 h hst6.fr.kept hbIn
  have g96' : env7.load 0 96 8 = reg m0 .rcx := by
    rw [show env7.load 0 96 8 = (Env.ofMachine d6 [(fb m0, F + 8)]).load 0 96 8 from rfl,
      hst6.hd.load (r := 0) (o := 96) (i := 3) (by decide)]
    rfl
  have hr12' := hst6.hd.reg (r := .r12) (i := 32) (by decide)
  have hm7 : Match env7 bS d6 :=
    St.mt hst6 ⟨rfl, rfl, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (env7.load 0 96 8) (d6.regs.get64 .r12) = blk + BitVec.ofInt 64 0
      rw [add64, g96', hr12', show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      rfl, trivial⟩
  have hown : env7.load 1 0 8 = BitVec.ofNat 64 bl[j].owner :=
    St.load h hst6 outs_id hBl (r := 1) (j := 16 * j) rfl (o' := 0) (by omega)
      (by rw [Nat.add_zero]; exact hbw.1)
  have ho6 := (h.bown _ (List.getElem_mem hj)).1
  have ho6' : bl[j].owner < 6 := ho6
  obtain ⟨hmid7, hw7, htr7, hsi7⟩ := ok_b20
  refine St.run h (rest := [(blk, 16)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b20_in_code (by simp [b20]) hp) exit_b20
    nofun hst6.fr hst6.same (hst6.hd.reg0 (rs' := (fb m0, F + 8) :: [(blk, 16)]) (by decide) rfl)
    (by decide) hwf7 hm7 hmid7 hw7 (by decide) htr7 fun st8 hm8 hpc8 hst8 _ ↦ ?_
  have hk8 : KeepF m0 d6.dmem st8.data.dmem := run_keep hwf7 hm8 hlo20 (writesIn_of_mid hmid7)
  have hc8 : c20.eval (frameEnv m0 d6 F [(blk, 16)] (fun _ ↦ 0) 0) = false := by
    show (!(CmpOp.apply .ult .W64 (env7.load 1 0 8) (BitVec.ofNat 64 5)) &&
      !(CmpOp.apply .eq .W64 (env7.load 1 0 8) (BitVec.ofNat 64 5))) = false
    rw [hown]
    exact c20_false (by rw [toNat_ofNat_lt (by omega)]; exact ho6')
  simp only [PcOk] at hpc8
  rw [hc8] at hpc8
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc8
  have hpc8' : st8.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b21Offset) := hpc8
  have e_si8 : st8.data.regs.get64 .rsi = (V 39).toBitVec := by
    rw [hm8.regs .rsi _ hsi7]
    show env7.load 1 0 8 = ((bkA L rows bl j).owner.toUInt64).toBitVec
    rw [hown, hbx]
    rfl
  obtain ⟨d8, pc8⟩ := st8
  simp only at hpc8' hst8 hk8 e_si8
  subst hpc8'
  exact cont d8 (St.add hst8 (fun _ _ ↦ rfl) (holds_reg e_si8 (holds_nil _ _ _)))
    (KeepF.fbuf hk8 hfb6) (KeepF.forms h hk8 hG6)

end

end NativeRustcVmX64.Bus.AccumulateSide
