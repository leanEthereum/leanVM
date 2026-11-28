module

public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.ProdE.Names
public import NativeRustcVmArm.Bus.GkrStep.Children

/-!
# `gkr_step`'s check

`b13` to `b15` take each child's product (`prod_e`), stored at `1216`, `1232`, `1248`; `b16`
evaluates them at the combiner (`poly_eval`); `b17`, `b18` compare with the sumcheck's claim:
`AtTail`, at `b19`.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- An element of the frame from its two words. -/
theorem ew_of_words {d : DataMem} {m0 : MachineData} {o : Nat} {x : EW}
    (h0 : NativeRustcVm.WordAt d (loc m0 o) x.c0)
    (h1 : NativeRustcVm.WordAt d (loc m0 (o + 8)) x.c1) :
    NativeRustcVm.EWsAt d (loc m0 o) [x] := by
  refine NativeRustcVm.ewsAt_singleton.mpr (NativeRustcVm.ewAt_iff.mpr ⟨h0, ?_⟩)
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
  exact h1

/-- Three elements of the frame, one after the other. -/
theorem ew3 {d : DataMem} {m0 : MachineData} {o : Nat} {x y z : EW}
    (hx : NativeRustcVm.EWsAt d (loc m0 o) [x]) (hy : NativeRustcVm.EWsAt d (loc m0 (o + 16)) [y])
    (hz : NativeRustcVm.EWsAt d (loc m0 (o + 32)) [z]) :
    NativeRustcVm.EWsAt d (loc m0 o) [x, y, z] := by
  rw [show [x, y, z] = [x] ++ ([y] ++ [z]) from rfl, NativeRustcVm.ewsAt_append,
    NativeRustcVm.ewsAt_append]
  refine ⟨hx, ?_, ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hy
  · rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]; exact hz

/-- The derived `==` of elements: their limbs equal. -/
theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  rfl

theorem cmp_w64 (x y : UInt64) : CmpOp.eq.apply .W64 x.toBitVec y.toBitVec = (x == y) := by
  simp only [CmpOp.apply, low_W64]
  by_cases h : x = y
  · simp [h]
  · simp [h, UInt64.toBitVec_inj]

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

omit [Host] in
/-- The frame's `2^step` elements at `o` as a slice. -/
theorem slice_loc {m : MachineData} {o : Nat} {xs : Array EW}
    (hx : NativeRustcVm.EWsAt m.dmem (loc m0 o) xs.toList) {p n : UInt64}
    (hp : p.toBitVec = loc m0 o) (hn : n.toNat = xs.size) : slice m p n = xs := by
  unfold slice
  rw [hp, hn, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hx, Array.toArray_toList]

/-- `n ≤ 64` bytes of the frame at `o` as a callee's slice. -/
theorem sliceOk_loc (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) {N' : Nat}
    (hle : 1392 + N' ≤ gkrStepStack) {o : Nat} {p n : UInt64} (hp : p.toBitVec = loc m0 o)
    (hon : o + 16 * n.toNat ≤ 1392) : SliceOk m p n N' := by
  have cx := ctx h
  have hat := Fr.at_ cx hfr (outs_not_rc h)
  have := cx.outOk hat hle (o := o) (n := 16 * n.toNat) hon
  unfold SliceOk Readable OffStack
  rw [hp]
  exact ⟨⟨this.1, this.2.1⟩, this.2.2.2.2.1⟩

/-- **A block of the frame** writing the products' area (`1216` to `1264`) only: the frame, the
bytes below `1216`, the `TState` kept. -/
theorem block_w (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) {ds : List Directive} {j : Nat}
    {S' : SState} {x : Exit} {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds frS = some (S', x))
    (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ 1216 ≤ w.off ∧ w.off + w.n ≤ 1264) (hsp : S'.sp = .ptr 0 0)
    (cont : ∀ st, Fr m0 1392 gkrStepStack slots keep (outs m0) st.data →
      Match (Env.ofMachine m [(base m0 1392, 1392)]) S' st.data →
      (∀ o (xs : List EW), o + 16 * xs.length ≤ 1216 →
        NativeRustcVm.EWsAt m.dmem (loc m0 o) xs → NativeRustcVm.EWsAt st.data.dmem (loc m0 o) xs) →
      (∀ s, TStateAt m.dmem m0.regs.X0.toBitVec a s →
        TStateAt st.data.dmem m0.regs.X0.toBitVec a s) →
      PcOk (Env.ofMachine m [(base m0 1392, 1392)]) x (Host.addrOf (j + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf j⟩ := by
  have hS := pre_stack h
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  have hsl : ∀ p ∈ slots, 1296 ≤ p.1 := fun p hp ↦ (slots_ge p hp).1
  refine cont st (Bus.Fr.block hfr hS.2.1 N_ge hm' hwf hsp (fun w hw' ↦ ?_)
    (fun _ hr ↦ absurd hr List.not_mem_nil) slots_le)
    hm' (fun o xs ho hxs ↦ ews_block hm' hwf (L := 16 * xs.length) (by omega)
      (fun w hw' ↦ ⟨(hw w hw').1, .inr (by have := (hw w hw').2.1; omega)⟩) (Nat.le_refl _) hxs)
    (fun s hs ↦ ts_block h hm' hwf (fun w hw' ↦ ⟨(hw w hw').1, by have := (hw w hw').2.2; omega⟩) hs)
    hpc
  obtain ⟨h0, h1, h2⟩ := hw w hw'
  exact ⟨h0, by omega, fun p hp ↦ .inl (by have := hsl p hp; omega)⟩

/-- **The check** (`b13` to `b18`). -/
theorem prods_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hpr : Spec (Labels.label NativeRustcVmArm.Vm.ProdE.entryLabel) ProdEPre ProdEPost)
    (hpe : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    {c cl : EW} {xs h0 h1 h2 : Array EW} {s3 : TState}
    (htail : ∀ m, AtTail a s0 g0 m0 xs h0 h1 h2 s3 m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b19Offset)⟩)
    {m : MachineData} (hi : AtProds a s0 g0 m0 c cl xs h0 h1 h2 s3 m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b13Offset)⟩ := by
  have hS := pre_stack h
  have hN : gkrStepStack ≤ m0.regs.SP.toNat := hS.2.1
  have hn := two_pow_le h
  have hxl := xs_le hi.size
  have l0 : h0.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hi.s0']
  have l1 : h1.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hi.s1']
  have l2 : h2.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hi.s2']
  have hst : 2 ≤ 2 ^ m0.regs.X1.toNat ∧ 2 ^ m0.regs.X1.toNat ≤ 4 := by
    rcases pre_step h with e | e <;> rw [e] <;> decide
  -- `b13`
  refine Fr.runBlock hS N_ge rfl hi.fr (b13_in_code.trans hp.1 (by simp [b13])) run_b13 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have R := hi.regs.block hm (by decide +kernel)
  have e0 : st.data.regs.X0.toBitVec = loc m0 1024 := by
    show (st.data.regs.getXReg .X0).toBitVec = _
    rw [hm.regs .X0 _ rfl]; rfl
  have e1 : st.data.regs.X1.toNat = 2 ^ m0.regs.X1.toNat := by
    show (st.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [reg_of hm (r := .X1) (r' := .X26) rfl, hi.regs.x26,
      NativeRustcVm.toNat_ofNat_of_lt (by omega)]
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b13_length, NativeRustcVmArm.Vm.GkrStep.b13Length, show k + NativeRustcVmArm.Vm.GkrStep.b13Offset + 3 = k + NativeRustcVmArm.Vm.GkrStep.b14Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b13_length, NativeRustcVmArm.Vm.GkrStep.b13Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b13_next] at hpc
  refine leaf_call h le_prod hpr (fun _ _ hq ↦ hq.2) hfr hpc
    ⟨hfr.stackOk hS rfl le_prod, by omega, by omega, sliceOk_loc h hfr le_prod e0 (by omega)⟩
    fun m2 hfr2 hq2 hcs2 hc2 hk2 ↦ ?_
  have hp0 : ewRet m2 = prodE h0 := by
    rw [hq2.1, slice_loc (by rw [hd]; exact hi.c0) e0 (by rw [e1, hi.s0'])]
  have R2 := R.call hcs2
  have K2 : Bus.KeepRegs [.X28, .X29] m st.data :=
    (Bus.KeepRegs.of_block hm (by decide +kernel))
  have K2' : Bus.KeepRegs [.X28, .X29] m m2 := K2.trans (Bus.KeepRegs.of_call hcs2 (by decide))
  have c1 := ews_leaf hS hfr.sp le_prod hc2 (o := 1088) (xs := h1.toList) (by omega) (by rw [hd]; exact hi.c1)
  have c2 := ews_leaf hS hfr.sp le_prod hc2 (o := 1152) (xs := h2.toList) (by omega) (by rw [hd]; exact hi.c2)
  have c0 := ews_leaf hS hfr.sp le_prod hc2 (o := 1024) (xs := h0.toList) (by omega)
    (by rw [hd]; exact hi.c0)
  have cx := ews_leaf hS hfr.sp le_prod hc2 (o := 16) (xs := xs.toList) (by omega) (by rw [hd]; exact hi.hxs)
  have t2 := ts_leaf h hfr le_prod hc2 hk2 (by rw [hd]; exact hi.ts)
  -- `b14`
  refine block_w h hfr2 (b14_in_code.trans hp.1 (by simp [b14])) run_b14 (by decide +kernel) rfl
    fun st3 hfr3 hm3 hk3 ht3 hpc3 ↦ ?_
  have w0 := Bus.wordAt_write hm3 (r := 0) (o := 1216) rfl (by omega) (v := .reg .X0)
    (by decide +kernel)
  have w1 := Bus.wordAt_write hm3 (r := 0) (o := 1224) rfl (by omega) (v := .reg .X1)
    (by decide +kernel)
  have hP0 : NativeRustcVm.EWsAt st3.data.dmem (loc m0 1216) [prodE h0] :=
    ew_of_words (by rw [← hp0]; exact w0) (by rw [← hp0]; exact w1)
  have R3 := R2.block hm3 (by decide +kernel)
  have K3 := K2'.trans (Bus.KeepRegs.of_block hm3 (by decide +kernel))
  have f0 : st3.data.regs.X0.toBitVec = loc m0 1088 := by
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ rfl]
    show BinOp.apply .add .W64 (m2.regs.getXReg .X27).toBitVec (BitVec.ofNat 64 64) = _
    rw [R2.x27, add_loc]
  have f1 : st3.data.regs.X1.toNat = 2 ^ m0.regs.X1.toNat := by
    show (st3.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [reg_of hm3 (r := .X1) (r' := .X26) rfl, R2.x26,
      NativeRustcVm.toNat_ofNat_of_lt (by omega)]
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b14_length, NativeRustcVmArm.Vm.GkrStep.b14Length, show k + NativeRustcVmArm.Vm.GkrStep.b14Offset + 5 = k + NativeRustcVmArm.Vm.GkrStep.b15Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b14_length, NativeRustcVmArm.Vm.GkrStep.b14Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b14_next] at hpc3
  refine leaf_call h le_prod hpr (fun _ _ hq ↦ hq.2) hfr3 hpc3
    ⟨hfr3.stackOk hS rfl le_prod, by omega, by omega, sliceOk_loc h hfr3 le_prod f0 (by omega)⟩
    fun m4 hfr4 hq4 hcs4 hc4 hk4 ↦ ?_
  have hp1 : ewRet m4 = prodE h1 := by
    rw [hq4.1, slice_loc (hk3 1088 h1.toList (by omega) c1) f0 (by rw [f1, hi.s1'])]
  have R4 := R3.call hcs4
  have K4 := K3.trans (Bus.KeepRegs.of_call hcs4 (by decide))
  have c2' := ews_leaf hS hfr3.sp le_prod hc4 (o := 1152) (xs := h2.toList) (by omega)
    (hk3 1152 _ (by omega) c2)
  have c0' := ews_leaf hS hfr3.sp le_prod hc4 (o := 1024) (xs := h0.toList) (by omega)
    (hk3 1024 _ (by omega) c0)
  have c1' := ews_leaf hS hfr3.sp le_prod hc4 (o := 1088) (xs := h1.toList) (by omega)
    (hk3 1088 _ (by omega) c1)
  have cx' := ews_leaf hS hfr3.sp le_prod hc4 (o := 16) (xs := xs.toList) (by omega)
    (hk3 16 _ (by omega) cx)
  have hP0' := ews_leaf hS hfr3.sp le_prod hc4 (o := 1216) (by simp) hP0
  have t4 := ts_leaf h hfr3 le_prod hc4 hk4 (ht3 _ t2)
  -- `b15`
  refine block_w h hfr4 (b15_in_code.trans hp.1 (by simp [b15])) run_b15 (by decide +kernel) rfl
    fun st5 hfr5 hm5 hk5 ht5 hpc5 ↦ ?_
  have w2 := Bus.wordAt_write hm5 (r := 0) (o := 1232) rfl (by omega) (v := .reg .X0)
    (by decide +kernel)
  have w3 := Bus.wordAt_write hm5 (r := 0) (o := 1240) rfl (by omega) (v := .reg .X1)
    (by decide +kernel)
  have hP1 : NativeRustcVm.EWsAt st5.data.dmem (loc m0 1232) [prodE h1] :=
    ew_of_words (by rw [← hp1]; exact w2) (by rw [← hp1]; exact w3)
  have hP0'' := keep_block hm5 (Bus.wf_frame hS N_ge hfr4.kept) (sizes := [1392]) rfl (r := 0) rfl
    (o := 1216) (L := 16) (by omega) (by decide +kernel)
    (by rw [NativeRustcVm.length_ewsBytes, List.length_singleton]) hP0'
  have R5 := R4.block hm5 (by decide +kernel)
  have K5 := K4.trans (Bus.KeepRegs.of_block hm5 (by decide +kernel))
  have g0' : st5.data.regs.X0.toBitVec = loc m0 1152 := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ rfl]
    show BinOp.apply .add .W64 (m4.regs.getXReg .X27).toBitVec (BitVec.ofNat 64 128) = _
    rw [R4.x27, add_loc]
  have g1 : st5.data.regs.X1.toNat = 2 ^ m0.regs.X1.toNat := by
    show (st5.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [reg_of hm5 (r := .X1) (r' := .X26) rfl, R4.x26,
      NativeRustcVm.toNat_ofNat_of_lt (by omega)]
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b15_length, NativeRustcVmArm.Vm.GkrStep.b15Length, show k + NativeRustcVmArm.Vm.GkrStep.b15Offset + 5 = k + NativeRustcVmArm.Vm.GkrStep.b16Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b15_length, NativeRustcVmArm.Vm.GkrStep.b15Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b15_next] at hpc5
  refine leaf_call h le_prod hpr (fun _ _ hq ↦ hq.2) hfr5 hpc5
    ⟨hfr5.stackOk hS rfl le_prod, by omega, by omega, sliceOk_loc h hfr5 le_prod g0' (by omega)⟩
    fun m6 hfr6 hq6 hcs6 hc6 hk6 ↦ ?_
  have hp2 : ewRet m6 = prodE h2 := by
    rw [hq6.1, slice_loc (hk5 1152 h2.toList (by omega) c2') g0' (by rw [g1, hi.s2'])]
  have R6 := R5.call hcs6
  have K6 := K5.trans (Bus.KeepRegs.of_call hcs6 (by decide))
  have cx6 := ews_leaf hS hfr5.sp le_prod hc6 (o := 16) (xs := xs.toList) (by omega)
    (hk5 16 _ (by omega) cx')
  have c06 := ews_leaf hS hfr5.sp le_prod hc6 (o := 1024) (xs := h0.toList) (by omega)
    (hk5 1024 _ (by omega) c0')
  have c16 := ews_leaf hS hfr5.sp le_prod hc6 (o := 1088) (xs := h1.toList) (by omega)
    (hk5 1088 _ (by omega) c1')
  have c26 := ews_leaf hS hfr5.sp le_prod hc6 (o := 1152) (xs := h2.toList) (by omega)
    (hk5 1152 _ (by omega) c2')
  have hQ0 := ews_leaf hS hfr5.sp le_prod hc6 (o := 1216) (by simp) hP0''
  have hQ1 := ews_leaf hS hfr5.sp le_prod hc6 (o := 1232) (by simp) hP1
  have t6 := ts_leaf h hfr5 le_prod hc6 hk6 (ht5 _ t4)
  -- `b16`
  refine block_w h hfr6 (b16_in_code.trans hp.1 (by simp [b16])) run_b16 (by decide +kernel) rfl
    fun st7 hfr7 hm7 hk7 ht7 hpc7 ↦ ?_
  have hwf7 := Bus.wf_frame hS N_ge hfr6.kept
  have w4 := Bus.wordAt_write hm7 (r := 0) (o := 1248) rfl (by omega) (v := .reg .X0)
    (by decide +kernel)
  have w5 := Bus.wordAt_write hm7 (r := 0) (o := 1256) rfl (by omega) (v := .reg .X1)
    (by decide +kernel)
  have hP2 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 1248) [prodE h2] :=
    ew_of_words (by rw [← hp2]; exact w4) (by rw [← hp2]; exact w5)
  have hQ0' := keep_block hm7 hwf7 (sizes := [1392]) rfl (r := 0) rfl
    (o := 1216) (L := 16) (by omega) (by decide +kernel)
    (by rw [NativeRustcVm.length_ewsBytes, List.length_singleton]) hQ0
  have hQ1' := keep_block hm7 hwf7 (sizes := [1392]) rfl (r := 0) rfl
    (o := 1232) (L := 16) (by omega) (by decide +kernel)
    (by rw [NativeRustcVm.length_ewsBytes, List.length_singleton]) hQ1
  have hPs : NativeRustcVm.EWsAt st7.data.dmem (loc m0 1216)
      #[prodE h0, prodE h1, prodE h2].toList := ew3 hQ0' hQ1' hP2
  have R7 := R6.block hm7 (by decide +kernel)
  have K7 := K6.trans (Bus.KeepRegs.of_block hm7 (by decide +kernel))
  have q0 : st7.data.regs.X0.toBitVec = loc m0 1216 := by
    show (st7.data.regs.getXReg .X0).toBitVec = _
    rw [hm7.regs .X0 _ rfl]; rfl
  have q1 : st7.data.regs.X1.toNat = 3 := by
    show (st7.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [reg_lit hm7 (r := .X1) (n := 3) rfl]; rfl
  have q23 : ewArg st7.data.regs.X2 st7.data.regs.X3 = c := by
    rw [show st7.data.regs.X2 = c.c0 from (reg_of hm7 (r := .X2) (r' := .X24) rfl).trans R6.x24,
      show st7.data.regs.X3 = c.c1 from (reg_of hm7 (r := .X3) (r' := .X25) rfl).trans R6.x25]
    rfl
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b16_length, NativeRustcVmArm.Vm.GkrStep.b16Length, show k + NativeRustcVmArm.Vm.GkrStep.b16Offset + 7 = k + NativeRustcVmArm.Vm.GkrStep.b17Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b16_length, NativeRustcVmArm.Vm.GkrStep.b16Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b16_next] at hpc7
  refine leaf_call h le_pe hpe (fun _ _ hq ↦ hq.2) hfr7 hpc7
    ⟨hfr7.stackOk hS rfl le_pe, by omega, sliceOk_loc h hfr7 le_pe q0 (by omega)⟩
    fun m8 hfr8 hq8 hcs8 hc8 hk8 ↦ ?_
  have hP : ewRet m8 = polyEval #[prodE h0, prodE h1, prodE h2] c := by
    rw [hq8.1, slice_loc hPs q0 (by rw [q1]; rfl), q23]
  have R8 := R7.call hcs8
  have K8 := K7.trans (Bus.KeepRegs.of_call hcs8 (by decide))
  have m29 : m8.regs.getXReg .X29 = cl.c0 := (K8 .X29 (by simp)).trans hi.x29
  have m28 : m8.regs.getXReg .X28 = cl.c1 := (K8 .X28 (by simp)).trans hi.x28
  have x8 := ews_leaf hS hfr7.sp le_pe hc8 (o := 16) (xs := xs.toList) (by omega)
    (hk7 16 _ (by omega) cx6)
  have d08 := ews_leaf hS hfr7.sp le_pe hc8 (o := 1024) (xs := h0.toList) (by omega)
    (hk7 1024 _ (by omega) c06)
  have d18 := ews_leaf hS hfr7.sp le_pe hc8 (o := 1088) (xs := h1.toList) (by omega)
    (hk7 1088 _ (by omega) c16)
  have d28 := ews_leaf hS hfr7.sp le_pe hc8 (o := 1152) (xs := h2.toList) (by omega)
    (hk7 1152 _ (by omega) c26)
  have t8 := ts_leaf h hfr7 le_pe hc8 hk8 (ht7 _ t6)
  have hrun : run0 s0 g0 m0 = if cl == polyEval #[prodE h0, prodE h1, prodE h2] c then
      ((sampleChallenges m0.regs.X1.toNat).run s3).bind fun y ↦
        some (⟨#[multilinearEval h0 y.1, multilinearEval h1 y.1, multilinearEval h2 y.1],
          y.1 ++ xs⟩, y.2)
      else none := by rw [hi.run]; rfl
  -- `b17`
  refine Fr.runBlock hS N_ge rfl hfr8 (b17_in_code.trans hp.1 (by simp [b17])) run_b17 rfl rfl
    (by decide) (by decide) fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_
  have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 1392, 1392)])
      (.not (.cmp .eq .W64 (.reg .X29) (.reg .X0))) =
      !(cl.c0 == (polyEval #[prodE h0, prodE h1, prodE h2] c).c0) := by
    show (!CmpOp.eq.apply .W64 (m8.regs.getXReg .X29).toBitVec (m8.regs.getXReg .X0).toBitVec) = _
    rw [cmp_w64, m29, show m8.regs.getXReg .X0 = (ewRet m8).c0 from rfl, hP]
  simp only [PcOk, hc9, NativeRustcVmArm.Vm.GkrStep.b17_length, NativeRustcVmArm.Vm.GkrStep.b17Length, show k + NativeRustcVmArm.Vm.GkrStep.b17Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b18Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b17_length, NativeRustcVmArm.Vm.GkrStep.b17Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b17_next] at hpc9
  by_cases e0 : cl.c0 = (polyEval #[prodE h0, prodE h1, prodE h2] c).c0
  · simp only [e0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
    -- `b18`
    refine at_pc hpc9 (Fr.runBlock hS N_ge rfl hfr9 (b18_in_code.trans hp.1 (by simp [b18]))
      run_b18 rfl rfl (by decide) (by decide) fun st10 hfr10 hd10 hm10 hpc10 ↦ ?_)
    have hc10 : SBool.eval (Env.ofMachine st9.data [(base m0 1392, 1392)])
        (.not (.cmp .eq .W64 (.reg .X28) (.reg .X1))) =
        !(cl.c1 == (polyEval #[prodE h0, prodE h1, prodE h2] c).c1) := by
      show (!CmpOp.eq.apply .W64 (st9.data.regs.getXReg .X28).toBitVec
        (st9.data.regs.getXReg .X1).toBitVec) = _
      rw [cmp_w64, reg_of hm9 (r := .X28) (r' := .X28) rfl, m28,
        reg_of hm9 (r := .X1) (r' := .X1) rfl, show m8.regs.getXReg .X1 = (ewRet m8).c1 from rfl,
        hP]
    simp only [PcOk, hc10, NativeRustcVmArm.Vm.GkrStep.b18_length, NativeRustcVmArm.Vm.GkrStep.b18Length, show k + NativeRustcVmArm.Vm.GkrStep.b18Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b19Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b18_length, NativeRustcVmArm.Vm.GkrStep.b18Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b18_next]
      at hpc10
    by_cases e1 : cl.c1 = (polyEval #[prodE h0, prodE h1, prodE h2] c).c1
    · simp only [e1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc10
      have hb : (cl == polyEval #[prodE h0, prodE h1, prodE h2] c) = true := by
        rw [ew_beq, e0, e1]; simp
      have R10 := (R8.block hm9 (by decide +kernel)).block hm10 (by decide +kernel)
      have hd' : st10.data.dmem = m8.dmem := hd10.trans hd9
      exact at_pc hpc10 (htail st10.data
        { fr := hfr10
          x19 := R10.x19
          x20 := R10.x20
          x21 := R10.x21
          x22 := R10.x22
          x23 := R10.x23
          x26 := R10.x26
          x27 := R10.x27
          size := hi.size
          hxs := by rw [hd']; exact x8
          c0 := by rw [hd']; exact d08
          c1 := by rw [hd']; exact d18
          c2 := by rw [hd']; exact d28
          s0' := hi.s0'
          s1' := hi.s1'
          s2' := hi.s2'
          ts := by rw [hd']; exact t8
          run := by rw [hrun, hb]; rfl })
    · have e1' : (cl.c1 == (polyEval #[prodE h0, prodE h1, prodE h2] c).c1) = false := by
        simp [e1]
      simp only [e1', Bool.not_false, ↓reduceIte] at hpc10
      exact at_pc (hpc10.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b32Offset) NativeRustcVmArm.Vm.GkrStep.label_14_at)) (fail_spec hp h hfr10
        (by rw [hrun, ew_beq, e1']; simp))
  · have e0' : (cl.c0 == (polyEval #[prodE h0, prodE h1, prodE h2] c).c0) = false := by
      simp [e0]
    simp only [e0', Bool.not_false, ↓reduceIte] at hpc9
    exact at_pc (hpc9.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b32Offset) NativeRustcVmArm.Vm.GkrStep.label_14_at)) (fail_spec hp h hfr9
      (by rw [hrun, ew_beq, e0']; simp))

end

end NativeRustcVmArm.Bus.GkrStep
