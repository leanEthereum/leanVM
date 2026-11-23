module

public import NativeRustcVmArm.Wire.InsD.Basic

/-!
# `ins_d`'s shift and store

From the shift's set-up (`b6`, `SixInv`): the elements from `i` moved up one by one (`b7`,
`TInv`, `shift_step`), then `x` stored at `i` (`b8`, `EInv`, `store_spec`): `six_spec`.
-/

namespace NativeRustcVmArm.Wire.InsD

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmArm.Vm.InsD

public section

variable [Host] {k : Nat} {m : MachineData} {L : List UInt64}

theorem lbl (hp : Placed code k) {j : Nat} {l : Label} (h : Vm.InsD.code[j]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + j) :=
  hp.label h

section
variable (hp : Placed code k)
  (hok : NativeRustcVm.Mapped m.dmem (arr m) 2048 ∧ NativeRustcVm.NoWrap (arr m) 2048)
  (hL : L.length = m.regs.X1.toNat) (hn : L.length < 256) (hW : WordsAt m.dmem (arr m) L)
include hp hok hL hn hW

omit hp in
/-- **The end of an insertion** (`b3`, `b8`): `x` stored at `i`, the count plus one, returned. -/
theorem finish {i : Nat} {g : UInt64} {s : MachineData} {st' : MachineState} {S₀ S' : SState}
    (hk : Kp m s) (hle : i ≤ L.length) (hb : Below m L i) (ha : Above m L i)
    (hw : WordsAt s.dmem (arr m) (L.take i ++ g :: L.drop i)) (hwf : (env1 m s i).WF)
    (hm : Match (env1 m s i) S₀ s) (hm' : Match (env1 m s i) S' st'.data)
    (hS : S'.mem = [⟨0, 0, 8, .reg .X2⟩]) (h0 : S'.reg .X0 = some (.bin .add .W64 (.reg .X1) (.lit 1)))
    (h30 : S₀.reg .X30 = some (.reg .X30) ∧ S'.reg .X30 = some (.reg .X30))
    (hkeep : keeps S₀ S' = true) (hpc' : st'.pc = retOf st'.data) : Post m st' := by
  have hi : i < 256 := by omega
  have h30' : st'.data.regs.getXReg .X30 = m.regs.getXReg .X30 :=
    (Match.reg_eq hm hm' h30.1 h30.2).trans hk.x30
  have hs : NativeRustcVm.SameOutside s.dmem st'.data.dmem (NativeRustcVm.InRange (pos m i) 8) := by
    have := Match.sameOutside_in hm' hwf (r0 := 0) (b := pos m i) (sz := 8) (o := 0) (n := 8) rfl
      (by omega) (by rw [hS]; decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hx : WordAt st'.data.dmem (pos m i) m.regs.X2 :=
    store_x2 hk hm' fun j hj ↦ by rw [hS]; exact findWrite_head hj
  have hlen : (L.take i ++ g :: L.drop i).length = L.length + 1 := by
    simp; omega
  have hws := hw.set hx hs (i := i) (by rw [hlen]; omega)
    (hok.2.mono (by rw [hlen]; omega))
  have ht : (L.take i).length = i := by simp; exact hle
  have hsm := set_mid (L.take i) (L.drop i) g m.regs.X2
  rw [ht] at hsm
  rw [hsm] at hws
  obtain ⟨hins, hmap⟩ := insD_words hle hb ha
  refine ⟨by rw [hpc', retOf, retOf, show st'.data.regs.X30 = m.regs.X30 from h30'], ?_⟩
  refine post_of hL hW (hk.sv.trans (Match.saved hm hm' hwf rfl hkeep))
    (fun p hp ↦ (pos_sub hok hi hs p hp).trans (hk.so p hp)) ?_ (by rw [hins, hmap]; exact hws)
  rw [hins]
  have hx0 := hm'.regs .X0 _ h0
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, hk.x1] at hx0
  show (st'.data.regs.getXReg .X0).toBitVec.toNat = _
  rw [hx0, toNat_add_one (by show (m.regs.getXReg .X1).toNat < 256; rw [← hL.symm] at hn; exact hn)]
  simp only [List.length_append, List.length_take, List.length_cons, List.length_drop, lst,
    List.length_map]
  show m.regs.X1.toNat + 1 = _
  omega

/-- **The store** (`b8`): `x` at `i`, the count plus one. -/
theorem store_spec {i : Nat} {g : UInt64} {st : MachineState} (hI : EInv m L k i g st) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hi : i < 256 := by have := hI.le; omega
  have hwf := env1_wf hok hI.kp hi
  have hm : Match (env1 m st.data i) scanS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by rw [elem_reg]; exact elem_alias hI.kp hi rfl hI.x8, trivial⟩
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf hI.pc hm fun st' hm' hpc' ↦ ?_
  exact .done _ (finish hok hL hn hW hI.kp hI.le hI.below hI.above hI.w hwf hm hm' rfl rfl ⟨rfl, rfl⟩
    (by decide) hpc')

omit hW in
/-- **A step of the shift** (`b7`): element `j` copied to `j + 1`; back at the head or at the
store. -/
theorem shift_step {i j : Nat} {g : UInt64} {st : MachineState} (hjL : j < L.length)
    (hI : TInv m L k i (j + 1) g st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ EInv m L k i L[j] st' ∨ TInv m L k i j L[j] st') st := by
  have hj : j + 1 < 256 := by have := hI.le; omega
  have hwf := env2_wf hok hI.kp hj
  have hm : Match (env2 m st.data j) shiftS st.data := by
    refine match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨?_, ?_, trivial⟩
    · rw [elem_sub]
      refine elem_alias hI.kp (by omega) rfl ?_
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [toNat_sub_one (by show (st.data.regs.getXReg .X9).toNat > 0; rw [hI.x9]; omega)]
      show (st.data.regs.getXReg .X9).toNat - 1 = j
      rw [hI.x9]; rfl
    · rw [elem_reg]; exact elem_alias hI.kp hj rfl hI.x9
  have hld : (env2 m st.data j).load 0 0 8 = L[j].toBitVec := by
    refine load_pos rfl ?_
    have := hI.w.getElem (i := j) (by simp; omega)
    rwa [List.getElem_append_left (by simp; omega), List.getElem_take] at this
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hI.pc hm fun st' hm' hpc' ↦ ?_
  have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (pos m (j + 1)) 8) := by
    have := Match.sameOutside_in hm' hwf (r0 := 1) (b := pos m (j + 1)) (sz := 8) (o := 0) (n := 8)
      rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hx : WordAt st'.data.dmem (pos m (j + 1)) L[j] := by
    have h := hm'.bytesAt_write (r := 1) (o := 0) (n := 8) (b := pos m (j + 1)) (sz := 8) rfl
      (by omega) (v := .load 0 0 8) fun t ht ↦ findWrite_head ht
    rw [byteOf_range, NativeRustcVm.addr_add_zero] at h
    simp only [Sym.eval, hld] at h
    exact h
  have hlen : (L.take (j + 1) ++ g :: L.drop (j + 1)).length = L.length + 1 := by
    simp; omega
  have hws := hI.w.set hx hs (i := j + 1) (by rw [hlen]; omega)
    (hok.2.mono (by rw [hlen]; omega))
  rw [shift_words L g hjL] at hws
  have hkp : Kp m st'.data := hI.kp.block hm hm' hwf rfl (by decide) (by decide)
    (pos_sub hok hj hs)
  have h8 : (st'.data.regs.getXReg .X8).toNat = i := by
    rw [Match.reg_eq hm hm' (v := .reg .X8) rfl rfl]; exact hI.x8
  have h9 : (st'.data.regs.getXReg .X9).toNat = j := by
    have := hm'.regs .X9 (.bin .sub .W64 (.reg .X9) (.lit 1)) rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at this
    show (st'.data.regs.getXReg .X9).toBitVec.toNat = j
    rw [this, toNat_sub_one (by show (st.data.regs.getXReg .X9).toNat > 0; rw [hI.x9]; omega)]
    show (st.data.regs.getXReg .X9).toNat - 1 = j
    rw [hI.x9]; rfl
  have hc : (SBool.and (SBool.cmp .ult .W64 (.bin .sub .W64 (.reg .X9) (.lit 1)) (.reg .X8)).not
      (SBool.cmp .eq .W64 (.bin .sub .W64 (.reg .X9) (.lit 1)) (.reg .X8)).not).eval
        (env2 m st.data j) = decide (i < j) := by
    simp only [SBool.eval, ult_apply, eq_apply]
    have e9 : ((Sym.bin .sub .W64 (.reg .X9) (.lit 1)).eval (env2 m st.data j)).toNat = j := by
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [toNat_sub_one (by show (st.data.regs.getXReg .X9).toNat > 0; rw [hI.x9]; omega)]
      show (st.data.regs.getXReg .X9).toNat - 1 = j
      rw [hI.x9]; rfl
    have e8 : ((Sym.reg .X8).eval (env2 m st.data j)).toNat = i := hI.x8
    rw [e9, e8]
    by_cases h : i < j
    · simp [h, show ¬j < i by omega, show j ≠ i by omega]
    · simp [h]; omega
  simp only [PcOk, hc] at hpc'
  by_cases hij : i < j
  · simp only [decide_eq_true hij, ↓reduceIte, lbl hp (j := 25) rfl] at hpc'
    exact .done _ (.inr ⟨hpc', hkp, h8, h9, hij, by omega, hI.below, hI.above, hws⟩)
  · simp only [decide_eq_false hij, Bool.false_eq_true, ↓reduceIte] at hpc'
    obtain rfl : j = i := by have := hI.lt; omega
    exact .done _ (.inl ⟨hpc'.trans (congrArg Host.addrOf (by rfl)), hkp, h8, by omega,
      hI.below, hI.above, hws⟩)

/-- **From the shift's set-up**: the shift, then the store. -/
theorem six_spec {g : UInt64} (hW' : WordsAt m.dmem (arr m) (L ++ [g])) {i : Nat}
    {st : MachineState} (hI : SixInv m L k i st) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hwf := Env.wf_nil st.data
  have hm := match_nil st.data
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hI.pc hm fun st' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have hkp : Kp m st'.data := hI.kp.block hm hm' hwf rfl (by decide) (by decide)
    (by rw [hd]; exact NativeRustcVm.SameOutside.refl _ _)
  have h8 : (st'.data.regs.getXReg .X8).toNat = i := by
    rw [Match.reg_eq hm hm' (v := .reg .X8) rfl rfl]; exact hI.x8
  have hx1 : (st.data.regs.getXReg .X1).toNat = L.length := by rw [hI.kp.x1]; exact hL.symm
  have hmin : ((Sym.ite (SBool.cmp .ult .W64 (.reg .X1) (.lit 255)) (.reg .X1) (.lit 255)).eval
      (Env.ofMachine st.data [])).toNat = L.length := by
    simp only [Sym.eval, SBool.eval, ult_apply, Env.ofMachine_regs]
    show (if decide ((st.data.regs.getXReg .X1).toNat < (BitVec.ofNat 64 255).toNat) = true then
      (st.data.regs.getXReg .X1).toBitVec else BitVec.ofNat 64 255).toNat = _
    rw [hx1]
    by_cases h : L.length < 255
    · simp [h]; exact hx1
    · simp [h]; omega
  have h9 : (st'.data.regs.getXReg .X9).toNat = L.length := by
    show (st'.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [hm'.regs .X9 _ rfl]; exact hmin
  have hc : (SBool.or
      (SBool.cmp .ult .W64 (Sym.ite (SBool.cmp .ult .W64 (.reg .X1) (.lit 255)) (.reg .X1) (.lit 255))
        (.reg .X8))
      (SBool.cmp .eq .W64 (Sym.ite (SBool.cmp .ult .W64 (.reg .X1) (.lit 255)) (.reg .X1) (.lit 255))
        (.reg .X8))).eval (Env.ofMachine st.data []) = decide (i = L.length) := by
    simp only [SBool.eval, ult_apply, eq_apply]
    have e8 : ((Sym.reg .X8).eval (Env.ofMachine st.data [])).toNat = i := hI.x8
    rw [hmin, e8]
    have := hI.le
    by_cases h : i = L.length
    · simp [h]
    · simp [h]; omega
  simp only [PcOk, hc] at hpc'
  have hw : WordsAt st'.data.dmem (arr m) (L.take L.length ++ g :: L.drop L.length) := by
    rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp), hd, hI.d]; exact hW'
  by_cases hi : i = L.length
  · simp only [decide_eq_true hi, ↓reduceIte, lbl hp (j := 34) rfl] at hpc'
    subst hi
    exact store_spec hp hok hL hn hW ⟨hpc', hkp, h8, le_refl _, hI.below, hI.above, hw⟩
  simp only [decide_eq_false hi, Bool.false_eq_true, ↓reduceIte] at hpc'
  have hT : TInv m L k i L.length g st' :=
    ⟨hpc'.trans (congrArg Host.addrOf (by rfl)), hkp, h8, h9, by have := hI.le; omega, le_refl _,
      hI.below, hI.above, hw⟩
  refine Sym.loop (fun j st ↦ ∃ g, TInv m L k i j g st) (fun j st ⟨g, hT⟩ ↦ ?_) ⟨g, hT⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hT.lt; omega⟩
  refine Eventually.bind (shift_step hp hok hL hn (by have := hT.le; omega) hT) fun st' h ↦ ?_
  rcases h with hE | hT'
  · exact Eventually.mono (store_spec hp hok hL hn hW hE) fun _ h ↦ .inl h
  · exact .done _ (.inr ⟨j, by omega, _, hT'⟩)

end

end

end NativeRustcVmArm.Wire.InsD
