module

public import NativeRustcVmX64.Bus.AccumulateSide.TurnC

/-! # `accumulate_side`: the table ones and padding arguments (x86-64) -/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

 theorem okP_false [Labels] (env : Env) {a n : Nat} (hb : a + n < 154)
    (ha : env.regs .r12 = BitVec.ofNat 64 a) (hn : env.load 0 24 8 = BitVec.ofNat 64 n) :
    okP.eval env = false := by
  have hs : sumP.eval env = BitVec.ofNat 64 (a + n) := by
    show BinOp.apply .add .W64 (env.load 0 24 8) (env.regs .r12) = _
    rw [add64, hn, ha, ← BitVec.ofNat_add, Nat.add_comm]
  have hge : CmpOp.apply .ult .W64 (sumP.eval env) (env.regs .r12) = false := by
    rw [hs, ha]
    simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (by omega : a + n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), decide_eq_false_iff_not]
    omega
  have hlt : CmpOp.apply .ult .W64 (sumP.eval env) (BitVec.ofNat 64 154) = true := by
    rw [hs]
    simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : a + n < 2 ^ 64)]
    exact decide_eq_true hb
  simp +instances only [okP, SBool.eval, Sym.eval]
  simp +instances only [hge, hlt, Bool.not_false, ↓reduceIte]
  simp only [CmpOp.apply, BinOp.apply]
  rw [Arrays.low8_replaceLow, Arrays.low8_replaceLow]
  decide

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

 theorem turnD (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (outs m0) (VT L rows bl Fm SL m0 j) (D21c ++ E21) 8 m)
    (hfb : FB m0 m.dmem (fmA L rows bl m0 j))
    (hG : FormsAt m.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1)
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (outs m0) (VT L rows bl Fm SL m0 j) (D23 ++ E23) 8 m2 →
      FB m0 m2.dmem (fmA L rows bl m0 j) →
      FormsAt m2.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1 →
      reg m2 .rsi = BitVec.ofNat 64 (bkA L rows bl j).logRows →
      reg m2 .rdx = BitVec.ofNat 64 (bkA L rows bl j).rows →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset)⟩ := by
  let V := VT L rows bl Fm SL m0 j
  let o := (bkA L rows bl j).owner
  have hbx : bkA L rows bl j = blockW L.tableLogHeights rows bl[j] := BA_getD L rows bl hj
  have ho : o < 6 := by
    dsimp [o]; rw [hbx]; exact (h.bown _ (List.getElem_mem hj)).1
  have hIn := (In.of_inOk h.layOk (Apart.symm' h.fL)).sub (o := 0) (k := 120)
    (by decide) (by decide)
  rw [off_zero] at hIn
  let env := frameEnv m0 m F [(reg m0 .r9, 120)] (fun _ ↦ 0) 0
  have hwf : env.WF := wf1 h hst.fr.kept hIn
  have g48 : env.load 0 48 8 = BitVec.ofNat 64 o :=
    hst.hd.load (r := 0) (o := 48) (i := 39) (by decide)
  have g104 : env.load 0 104 8 = reg m0 .r9 :=
    hst.hd.load (r := 0) (o := 104) (i := 5) (by decide)
  have hm : Match env hS m := St.mt hst ⟨rfl, rfl, trivial⟩ trivial
    ⟨by change (env.load 0 48 8).toNat < 6
        rw [g48, toNat_ofNat_lt (by omega)]; exact ho, trivial⟩
    ⟨by change env.load 0 104 8 = reg m0 .r9 + 0#64
        rw [BitVec.add_zero]; exact g104, trivial⟩
  have g12 : env.regs .r12 = (twA (5 * o + 3)).toBitVec :=
    hst.hd.reg (r := .r12) (i := 43) (by decide)
  have g24 : env.load 0 24 8 = (twA (5 * o + 4)).toBitVec :=
    hst.hd.load (r := 0) (o := 24) (i := 44) (by decide)
  have hP := okP_false env (padding_read ho).1
    (g12.trans (by simp)) (g24.trans (by simp))
  have hidx : (BinOp.apply .mul .W64 (env.load 0 48 8) (BitVec.ofNat 64 8)).toNat = 8 * o := by
    rw [mul64, g48]
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have hheight : env.load 1 (24 + 8 * o) 8 = BitVec.ofNat 64 (bkA L rows bl j).logRows := by
    have hw := NativeRustcVm.WordsAt.getElem h.lay.heights (i := o) (by
      simp only [List.length_map, Array.length_toList, h.lay.heights_size]; exact ho)
    simp only [List.getElem_map, Array.getElem_toList, off_off] at hw
    have hl : L.tableLogHeights.getD o 0 = L.tableLogHeights[o]'(by
        rw [h.lay.heights_size]; exact ho) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h.lay.heights_size]; exact ho)]
      rfl
    have hb : (bkA L rows bl j).logRows = L.tableLogHeights.getD o 0 := by
      change (bkA L rows bl j).logRows = L.tableLogHeights.getD (bkA L rows bl j).owner 0
      rw [hbx]; rfl
    rw [hb, hl]
    exact load_ofMachine (r := 1) rfl (St.word h hst outs_id hIn (by omega) hw)
  have hrows : env.load 1 (72 + 8 * o) 8 = BitVec.ofNat 64 (bkA L rows bl j).rows := by
    have hw := NativeRustcVm.WordsAt.getElem h.rowsW (i := o) (by
      simp only [List.length_map, Array.length_toList, h.rows_size]; exact ho)
    simp only [List.getElem_map, Array.getElem_toList, off_off] at hw
    have hl : rows.getD o 0 = rows[o]'(by rw [h.rows_size]; exact ho) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [h.rows_size]; exact ho)]
      rfl
    have hb : (bkA L rows bl j).rows = rows.getD o 0 := by
      change (bkA L rows bl j).rows = rows.getD (bkA L rows bl j).owner 0
      rw [hbx]; rfl
    rw [hb, hl]
    exact load_ofMachine (r := 1) rfl (St.word h hst outs_id hIn (by omega) hw)
  obtain ⟨hmid, hw, htr, h14, h15, h12, h24, hsi, hdx⟩ := ok_b23a
  refine St.run h (rest := [(reg m0 .r9, 120)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b23a_in_code (by simp [b23a, b23]) hp) exit_b23a nofun hst.fr hst.same
    (hst.hd.reg0 (by decide) rfl) (by decide) hwf hm hmid hw (by decide) htr
    fun st hm' hpc hst' hc ↦ ?_
  have hk := run_keep hwf hm' low_T.2.2.2.2.2.2.2.1 (writesIn_of_mid hmid)
  have e14 : st.data.regs.get64 .r14 = (V 45).toBitVec := by
    rw [hm'.regs .r14 _ h14]
    show BinOp.apply .xor .W64 (m.regs.get64 .r14) (m.regs.get64 .rbx) = _
    rw [xor64, hst.hd.reg (r := .r14) (i := 35) (by decide),
      hst.hd.reg (r := .rbx) (i := 37) (by decide)]
    change (onesT SL (ptA m0) j).c0.toBitVec ^^^ (tsel SL (ptA m0) j).c0.toBitVec = _
    change _ = (onesT SL (ptA m0) (j + 1)).c0.toBitVec
    rw [onesT_succ, add_c0, UInt64.toBitVec_xor]
  have e15 : st.data.regs.get64 .r15 = (V 46).toBitVec := by
    rw [hm'.regs .r15 _ h15]
    show BinOp.apply .xor .W64 (m.regs.get64 .r15) ((Env.ofMachine m [(fb m0, F + 8)]).load 0 16 8) = _
    rw [xor64, hst.hd.reg (r := .r15) (i := 36) (by decide),
      hst.hd.load (r := 0) (o := 16) (i := 38) (by decide)]
    change (onesT SL (ptA m0) j).c1.toBitVec ^^^ (tsel SL (ptA m0) j).c1.toBitVec = _
    change _ = (onesT SL (ptA m0) (j + 1)).c1.toBitVec
    rw [onesT_succ, add_c1, UInt64.toBitVec_xor]
  have e12 : st.data.regs.get64 .r12 = (V 47).toBitVec := by
    rw [hm'.regs .r12 _ h12]
    change (if okP.eval env = true then _ else _) = _
    rw [hP]; simp only [Bool.false_eq_true, ↓reduceIte]
    show BinOp.apply .add .W64 (rodataAddr .padding)
      (BinOp.apply .shl .W64 (env.regs .r12) (BitVec.ofNat 64 4)) = _
    rw [add64, shl4, g12]; rfl
  have e24 : lenP.eval env = (V 44).toBitVec := by
    change (if okP.eval env = true then _ else _) = _
    rw [hP]; exact g24
  have hst2 := St.add hst' (fun _ _ ↦ rfl)
    (holds_reg (i := 45) e14 (holds_reg (i := 46) e15 (holds_reg (i := 47) e12
      (holds_content (s := Lw 24) (i := 44) (hc _ _ rfl h24) e24 (holds_nil _ _ _)))))
  have esi : reg st.data .rsi = BitVec.ofNat 64 (bkA L rows bl j).logRows := by
    change st.data.regs.get64 .rsi = _
    rw [hm'.regs .rsi _ hsi]
    change env.load 1 (24 + (BinOp.apply .mul .W64 (env.load 0 48 8) (BitVec.ofNat 64 8)).toNat) 8 = _
    rw [hidx]; exact hheight
  have edx : reg st.data .rdx = BitVec.ofNat 64 (bkA L rows bl j).rows := by
    change st.data.regs.get64 .rdx = _
    rw [hm'.regs .rdx _ hdx]
    change env.load 1 (72 + (BinOp.apply .mul .W64 (env.load 0 48 8) (BitVec.ofNat 64 8)).toNat) 8 = _
    rw [hidx]; exact hrows
  have hpc' : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length) := hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc' hst2 hk esi edx
  subst hpc'
  exact cont d hst2 (KeepF.fbuf hk hfb) (KeepF.forms h hk hG) esi edx

end

end NativeRustcVmX64.Bus.AccumulateSide
