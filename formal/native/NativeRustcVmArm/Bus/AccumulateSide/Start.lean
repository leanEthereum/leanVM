module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Bus.AccumulateSide.StartOnes

/-!
# `accumulate_side` up to the table loop

After the ones (`QZ` at `b22`), `b22`, `b23` zero the frame's 5920 bytes from `6080`, 160 a turn
(`zturn`, `zloop`); `b24` saves the ones in the frame and copies those bytes to the frame's
`FormBuf`'s terms at `160` (`memcpy`); `b25` takes the table blocks' count (`bl.length`, at most
`51`); `b26` sets the table loop's registers and frame words.

**`start_spec`**: from the entry to the table loop's head before turn `0` (`b27`, `k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset`):
`St m0 (TT … 0) DL` and the forms at X1 still `Fm`.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- The zeroing loop's 160 bytes in turn `t`. -/
@[expose] def zA (m0 : MachineData) (t : Nat) : BitVec 64 :=
  base m0 F + BitVec.ofNat 64 (6080 + 160 * t)

/-- X8 in turn `t` of the zeroing loop. -/
@[expose] def x8v (t : Nat) : UInt64 :=
  UInt64.ofBitVec (BitVec.ofInt 64 (-5920) + BitVec.ofNat 64 (160 * t))

section
variable [Labels]

theorem ev_add (env : Env) (a b : Sym) :
    (Sym.bin .add .W64 a b).eval env = a.eval env + b.eval env := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem ev_mul (env : Env) (a b : Sym) :
    (Sym.bin .mul .W64 a b).eval env = a.eval env * b.eval env := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem ev_sub (env : Env) (a b : Sym) :
    (Sym.bin .sub .W64 a b).eval env = a.eval env - b.eval env := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

end

theorem x8v_step (t : Nat) :
    (x8v t).toBitVec + BitVec.ofNat 64 160 = (x8v (t + 1)).toBitVec := by
  show BitVec.ofInt 64 (-5920) + BitVec.ofNat 64 (160 * t) + BitVec.ofNat 64 160 =
    BitVec.ofInt 64 (-5920) + BitVec.ofNat 64 (160 * (t + 1))
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]

theorem x8v_ne : ∀ t : Fin 36, (x8v (t.val + 1)).toNat ≠ 0 := by decide

theorem x8v_37 : (x8v 37).toNat = 0 := by decide

theorem x8v_0 : BitVec.ofNat 64 18446744073709545696 = (x8v 0).toBitVec := by decide

/-- X9 + X8 in turn `t`: the zeroing loop's bytes less `5920`. -/
theorem x8v_alias (b : BitVec 64) (t : Nat) :
    b + BitVec.ofNat 64 6080 + (x8v t).toBitVec =
      b + BitVec.ofNat 64 (6080 + 160 * t) + BitVec.ofInt 64 (-5920) := by
  show _ + (BitVec.ofInt 64 (-5920) + BitVec.ofNat 64 (160 * t)) = _
  rw [← BitVec.ofNat_add_ofNat]
  ac_rfl

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

theorem zA_toNat (h : Pre L rows bl Fm SL m0) {t : Nat} (ht : t < 37) :
    (zA m0 t).toNat = (base m0 F).toNat + 6080 + 160 * t := by
  have hb := base_toNat (m0 := m0) (F := F) (F_le h)
  have := m0.regs.SP.toNat_lt
  have hF0 : F = 12096 := rfl
  have hS := h.stack.2.1
  rw [N_eq] at hS
  unfold zA
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- The zeroing loop's bytes in turn `t` are among the frame's 5920 from `6080`. -/
theorem zA_in (h : Pre L rows bl Fm SL m0) {t : Nat} (ht : t < 37) {q : BitVec 64}
    (hq : InRange (zA m0 t) 160 q) : InRange (base m0 F + BitVec.ofNat 64 6080) 5920 q := by
  have hb := base_toNat (m0 := m0) (F := F) (F_le h)
  have := m0.regs.SP.toNat_lt
  have hF0 : F = 12096 := rfl
  have hS := h.stack.2.1
  rw [N_eq] at hS
  have hz := zA_toNat h ht
  have h1 : (base m0 F + BitVec.ofNat 64 6080).toNat = (base m0 F).toNat + 6080 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [hz]; omega), hz] at hq
  rw [Sym.inRange_iff (by rw [h1]; omega), h1]
  omega

/-- **The frame through a write of its 5920 bytes from `6080`**: the frame, the description, the
forms kept. -/
theorem St.zeroes (h : Pre L rows bl Fm SL m0) {V : Nat → UInt64} {D : List (Sym × Nat)}
    {m m' : MachineData} (hst : St m0 V D m) (hD : D.all (fun p ↦ callOk 6080 5920 p.1) = true)
    (hsp : m'.regs.SP = m.regs.SP) (hk : Kept m.dmem m'.dmem)
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r)
    (hs : SameOutside m.dmem m'.dmem (InRange (base m0 F + BitVec.ofNat 64 6080) 5920))
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) :
    St m0 V D m' ∧ FormsAt m'.dmem m0.regs.X1.toBitVec Fm := by
  have hN := h.stack.2.1
  have hFl := F_le h
  have hfr : Fr m0 F N slots keep (outs m0) m' :=
    hst.fr.step hsp (fun r hr ↦ nomatch hr) hk hs
      (fun q hq ↦ .inl (Bus.inRange_local hN (by decide) (by decide) hq))
      fun p hp i hi ↦ Bus.slot_not_local hFl (by have := slots_ge p hp; omega)
        (by have := slots_le p hp; omega)
  refine ⟨⟨hfr, ?_⟩, forms_frame h hst.fr.sp (N' := 0) (lo := 6080) (n := 5920) (by decide)
    (by decide) (NativeRustcVm.SameOutside.mono hs fun _ h ↦ .inl h) hF⟩
  refine Holds.keep hst.hd (List.all_eq_true.mpr fun p hp ↦ ?_) (fun p hp r hr ↦ ?_)
    fun p hp o ho j hj ↦ ?_
  · exact loc0_of_callOk _ (List.all_eq_true.mp hD p hp)
  · have hc : callOk 6080 5920 p.1 = true := List.all_eq_true.mp hD p hp
    rw [hr] at hc
    exact hcs r hc
  · have hc : callOk 6080 5920 p.1 = true := List.all_eq_true.mp hD p hp
    rw [ho] at hc
    simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    show m'.dmem.get? (base m0 F + BitVec.ofNat 64 (o + j)) =
      m.dmem.get? (base m0 F + BitVec.ofNat 64 (o + j))
    exact hs _ (Gkr.not_loc (m0 := m0) hFl (by decide) (by omega) (by omega))

end

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-! ## The zeroing loop -/

/-- **A turn of the zeroing loop** (`b23`), turn `t`. -/
theorem zturn (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {t : Nat} (ht : t < 37)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QZ m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm)
    (h9 : (m.regs.getXReg .X9).toBitVec = base m0 F + BitVec.ofNat 64 6080)
    (h8 : m.regs.getXReg .X8 = x8v t) {R : MachineState → Prop}
    (cnext : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      (m2.regs.getXReg .X9).toBitVec = base m0 F + BitVec.ofNat 64 6080 →
      m2.regs.getXReg .X8 = x8v (t + 1) → t + 1 < 37 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b23Offset)⟩)
    (cexit : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b24Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b23Offset)⟩ := by
  have hN := h.stack.2.1
  have hFl := F_le h
  have hb := base_toNat (m0 := m0) (F := F) hFl
  have hlt := m0.regs.SP.toNat_lt
  have hz := zA_toNat h ht
  have hF0 : F = 12096 := rfl
  have hNe := N_eq
  have hS := h.stack.2.1
  rw [N_eq] at hS
  let env := Env.ofMachine m [(zA m0 t, 160)] (fun _ ↦ m.regs.SP.toBitVec)
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ hst.fr.kept _ ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
    · show (m0.dmem.get? (zA m0 t + BitVec.ofNat 64 i)).isSome
      rw [zA, NativeRustcVm.addr_add_add]
      exact (Bus.frame_mapped h.stack (show F ≤ N by decide)).1 _ (by omega)
    · show (zA m0 t).toNat + 160 ≤ 2 ^ 64
      rw [hz]
      omega
  have hm : Match env zS m := by
    refine match_ofMachine (sregions := [(160, true)]) (regions := [(zA m0 t, 160)])
      ⟨rfl, fun _ ↦ ?_, trivial⟩ rfl trivial trivial trivial ⟨?_, trivial⟩
    · rw [hz]
      have := Bus.base_aligned h.stack (show F ≤ N by decide) rfl
      omega
    · show (Sym.bin .add .W64 (.reg .X9) (.reg .X8)).eval env =
        env.base 0 + BitVec.ofInt 64 (-5920)
      rw [ev_add, Env.base_ofMachine m _ _ (r := 0) rfl]
      show (m.regs.getXReg .X9).toBitVec + (m.regs.getXReg .X8).toBitVec = _
      rw [h9, h8, x8v_alias]
      rfl
  refine exec_then (b23_in_code.trans hp.1 (by simp [b23])) run_b23 hwf hm fun st hm' hpc ↦ ?_
  have hW : SameOutside m.dmem st.data.dmem
      (InRange (base m0 F + BitVec.ofNat 64 6080) 5920) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun q hq ↦ zA_in h ht
      (Bus.Written.inRange (r := 0) rfl (by rw [hz]; omega) (by decide) hq)
  have hsp : st.data.regs.SP = m.regs.SP := UInt64.toBitVec_inj.mp hm'.sp
  obtain ⟨hst2, hF2⟩ := St.zeroes h hst (by decide) hsp (hm'.kept hwf) (fun r hr ↦ by
    cases r <;> first
      | exact absurd hr (by decide)
      | exact UInt64.toBitVec_inj.mp (hm'.regs _ (.reg _) rfl)) hW hF
  have h9' : (st.data.regs.getXReg .X9).toBitVec = base m0 F + BitVec.ofNat 64 6080 :=
    (hm'.regs .X9 _ rfl).trans h9
  have h8e : (Sym.bin .add .W64 (.reg .X8) (.lit 160)).eval env = (x8v (t + 1)).toBitVec := by
    rw [ev_add]
    show (m.regs.getXReg .X8).toBitVec + BitVec.ofNat 64 160 = _
    rw [h8, x8v_step t]
  have h8' : st.data.regs.getXReg .X8 = x8v (t + 1) :=
    UInt64.toBitVec_inj.mp ((hm'.regs .X8 _ rfl).trans h8e)
  have he := cmp_eq_lit env h8e (by decide : 0 < 2 ^ 64)
  have hc : SBool.eval env (.not (.cmp .eq .W64 (.bin .add .W64 (.reg .X8) (.lit 160)) (.lit 0))) =
      decide (t + 1 < 37) := by
    show (!SBool.eval _ _) = _
    rw [he]
    by_cases h1 : t + 1 < 37
    · have := x8v_ne ⟨t, by omega⟩
      simp only [h1, decide_true, this, decide_false, Bool.not_false]
    · rw [show t + 1 = 37 by omega, x8v_37]
      rfl
  simp only [PcOk, hc] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b23Offset) NativeRustcVmArm.Vm.AccumulateSide.label_14_at,
    show k + NativeRustcVmArm.Vm.AccumulateSide.b23Offset + b23.length = k + NativeRustcVmArm.Vm.AccumulateSide.b24Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b23_next]] at hpc
  by_cases h1 : t + 1 < 37
  · exact Gkr.at_pc (by simpa [h1] using hpc) (cnext _ hst2 hF2 h9' h8' h1)
  · exact Gkr.at_pc (by simpa [h1] using hpc) (cexit _ hst2 hF2)

/-- **The zeroing loop** from turn `t`. -/
theorem zloop (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {R : MachineState → Prop}
    (cexit : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b24Offset)⟩) :
    ∀ n t, t + n = 36 → ∀ m, St m0 (TT SL m0 L rows bl Fm 0) QZ m →
      FormsAt m.dmem m0.regs.X1.toBitVec Fm →
      (m.regs.getXReg .X9).toBitVec = base m0 F + BitVec.ofNat 64 6080 →
      m.regs.getXReg .X8 = x8v t → Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b23Offset)⟩
  | 0, t, ht, m, hst, hF, h9, h8 =>
    zturn hp h (by omega) hst hF h9 h8 (fun _ _ _ _ _ h1 ↦ absurd h1 (by omega)) cexit
  | n + 1, t, ht, m, hst, hF, h9, h8 =>
    zturn hp h (by omega) hst hF h9 h8
      (fun m2 hst2 hF2 h92 h82 _ ↦ zloop hp h cexit n (t + 1) (by omega) m2 hst2 hF2 h92 h82)
      cexit

/-- **`b22`** and the zeroing loop. -/
theorem zero (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QZ m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b24Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩ := by
  have hH0 := St.lift (D := QZ) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b22_in_code.trans hp.1 (by simp [b22])) run_b22 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := QZ) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  simp only [PcOk] at hpc
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset + b22.length = k + NativeRustcVmArm.Vm.AccumulateSide.b23Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b22_next]] at hpc
  refine Gkr.at_pc hpc (zloop hp h cont 36 0 rfl st.data ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF) ?_ ?_)
  · rw [hm'.regs .X9 _ rfl, ptr0_eval (oi := 6080) (o := 6080) _ _ _ _ rfl]
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.regs .X8 _ rfl]
    exact x8v_0

/-! ## The frame's `FormBuf`, the table loop's setup -/

/-- **`b24`**: the ones in the frame; `memcpy` of the zeroed bytes to the `FormBuf`'s terms. -/
theorem s24 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QZ m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q25 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b25Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b24Offset)⟩ := by
  have hH0 : Holds [(base m0 F, F + 0)] (TT SL m0 L rows bl Fm 0)
      ((.reg .X25, 90) :: (.reg .X20, 91) :: QZ) m :=
    Holds.dup (s := .reg .X25) (Holds.dup (s := .reg .X20) (St.lift hst (by decide) 0 [])
      (i := 79) (j := 91) (by decide) rfl) (i := 78) (j := 90) (by decide) rfl
  have hwf := wf0 h hst.fr.kept
  have hb := base_toNat (m0 := m0) (F := F) (F_le h)
  have hlt := m0.regs.SP.toNat_lt
  have hF0 : F = 12096 := rfl
  have hS := sp_ge h
  refine St.runCall h (A := 0) (rs := []) (sz := [12096]) rfl
    (b24_in_code.trans hp.1 (by simp [b24])) run_b24 hst.fr hH0 hwf (matchF h hst.fr.sp) rfl
    (by decide) (D' := Q24r) (E := [(.load 0 80 8, 23)]) (by decide) (by decide)
    (fun st hm' ↦ holds_one ?_) (N' := 0) (lo := 160) (n := 5920) (by decide) (by decide)
    (by decide) hmc (fun st hm' hst' ↦ ?_) (fun st m' hm' hq ↦ ?_)
    fun st m2 hm' hst' hst2 hq _ ↦ ?_
  · rw [tval_write hm' rfl rfl (by decide) (v := .ptr 0 160) (by decide),
      ptr0_eval (oi := 160) (o := 160) _ _ _ _ rfl]
    rfl
  all_goals
    have ex0 : st.regs.X0.toBitVec = base m0 F + BitVec.ofNat 64 160 :=
      (hm'.regs .X0 _ rfl).trans (ptr0_eval (oi := 160) (o := 160) _ _ _ _ rfl)
    have ex1 : st.regs.X1.toBitVec = base m0 F + BitVec.ofNat 64 6080 :=
      (hm'.regs .X1 _ rfl).trans (ptr0_eval (oi := 6080) (o := 6080) _ _ _ _ rfl)
    have ex2 : st.regs.X2.toNat = 5920 := by
      show (st.regs.getXReg .X2).toBitVec.toNat = 5920
      rw [hm'.regs .X2 _ rfl]
      rfl
  · obtain ⟨hd1, hd2⟩ := Bus.local_ok h.stack (N' := 0) (o := 160) (n := 5920) (by decide)
      (by decide) hst'.fr.kept hst'.fr.sp
    obtain ⟨hs1, hs2⟩ := Bus.local_ok h.stack (N' := 0) (o := 6080) (n := 5920) (by decide)
      (by decide) hst'.fr.kept hst'.fr.sp
    unfold MemcpyPre
    rw [ex0, ex1, ex2]
    refine ⟨hd1.1, hs1.1, hd1.2, hs1.2, ?_⟩
    unfold Apart
    rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq' ↦ ?_, hsv⟩
    rw [ex0, ex2] at hq'
    exact .inr (.inl hq')
  · rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b24Offset + b24.length = k + NativeRustcVmArm.Vm.AccumulateSide.b25Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b24_next]]
    refine cont m2 ⟨hst2.fr, Holds.sub hst2.hd (by decide)⟩ ?_
    obtain ⟨-, -, hs, -⟩ := hq
    refine forms_frame h hst'.fr.sp (N' := 0) (lo := 160) (n := 5920) (by decide) (by decide)
      (NativeRustcVm.SameOutside.mono hs fun q hq' ↦ ?_)
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF)
    rw [ex0, ex2] at hq'
    exact .inl hq'

/-- **`b25`**: the table blocks' count, between `1` and `51`. -/
theorem s25 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q25 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q26 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b26Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b25Offset)⟩ := by
  have hfr := hst.fr
  have h51 := bl_size h
  have h1 := h.blen
  have hok := rok_sl h (n := 888) (by decide) (by decide)
  have hH0 : Holds ((base m0 F, F + 0) :: [(m0.regs.X6.toBitVec, 888)])
      (TT SL m0 L rows bl Fm 0) ((.ptr 1 0, 6) :: Q25) m := by
    refine Holds.cons (St.lift hst (by decide) 0 _) ?_
    unfold tval
    rw [ptr_eval (oi := 0) (o := 0) rfl rfl, add_zero', TT_sv (by decide)]
    rfl
  have hwf := wf1 h hfr.kept hok
  have h19 : (m.regs.getXReg .X19).toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 0 := by
    rw [Holds.regv hst.hd (r := .X19) (i := 6) (by decide), TT_sv (by decide), add_zero']
    rfl
  have hlen : bl.length < 2 ^ 64 := by omega
  have e64 : (Sym.load 1 64 8).eval (Env.ofMachine m [(base m0 F, F + 0),
      (m0.regs.X6.toBitVec, 888)]) = (bl.length.toUInt64).toBitVec := by
    rw [load_rk rfl, sl_word h hfr (o := 64) (by decide), tb_word h]
  have e27 : (Sym.reg .X27).eval (Env.ofMachine m [(base m0 F, F + 0),
      (m0.regs.X6.toBitVec, 888)]) = (bl.length.toUInt64).toBitVec := by
    rw [Holds.evc hH0 (s := .reg .X27) (i := 4) (by decide), TT_sv (by decide)]
    show m0.regs.X4.toBitVec = _
    congr 1
    apply UInt64.toNat_inj.mp
    rw [h.x4, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hlen]
  refine St.run h.stack (A := 0) (rs := [(m0.regs.X6.toBitVec, 888)]) (sz := [12096, 888]) rfl
    (b25_in_code.trans hp.1 (by simp [b25])) run_b25 hfr hH0 hwf (matchR h hfr.sp h19) rfl
    (by decide) (D' := Q25) (E := [(.reg .X29, 100)]) (by decide) (by decide)
    (fun st hm' ↦ holds_one ?_) fun st hm' hpc hst' ↦ ?_
  · rw [tval_reg_of hm' rfl, ev_ite, e27, e64, ite_self, UInt64.ofBitVec_toBitVec]
    show bl.length.toUInt64 = ((BA L rows bl).size - 0).toUInt64
    rw [BA_size]
    rfl
  · have ev : (Sym.bin .sub .W64 (.load 1 64 8) (.lit 1)).eval (Env.ofMachine m
        [(base m0 F, F + 0), (m0.regs.X6.toBitVec, 888)]) =
        (UInt64.ofBitVec (BitVec.ofNat 64 (bl.length - 1))).toBitVec := by
      rw [ev_sub, e64]
      show BitVec.ofNat 64 bl.length - BitVec.ofNat 64 1 = BitVec.ofNat 64 (bl.length - 1)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    have hx : (UInt64.ofBitVec (BitVec.ofNat 64 (bl.length - 1))).toNat = bl.length - 1 := by
      show (BitVec.ofNat 64 (bl.length - 1)).toNat = _
      rw [BitVec.toNat_ofNat]
      omega
    have c1 := cmp_ult_lit _ ev (c := 50) (by decide)
    have c2 := cmp_eq_lit _ ev (c := 50) (by decide)
    rw [hx] at c1 c2
    have hc : SBool.eval (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X6.toBitVec, 888)])
        (.and (.not (.cmp .ult .W64 (.bin .sub .W64 (.load 1 64 8) (.lit 1)) (.lit 50)))
          (.not (.cmp .eq .W64 (.bin .sub .W64 (.load 1 64 8) (.lit 1)) (.lit 50)))) =
        false := by
      show (!SBool.eval _ _ && !SBool.eval _ _) = false
      rw [c1, c2]
      by_cases h50 : bl.length - 1 < 50
      · simp [h50]
      · simp [show bl.length - 1 = 50 by omega]
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b25Offset + b25.length = k + NativeRustcVmArm.Vm.AccumulateSide.b26Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b25_next]] at hpc
    exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- **`b26`**: the table loop's registers and frame words, before turn `0`. -/
theorem s26 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q26 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) DL m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b26Offset)⟩ := by
  have hH0 := St.lift (D := Q26) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b26_in_code.trans hp.1 (by simp [b26])) run_b26 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q26r) (E := Q26e) (by decide) (by decide)
    (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [Q26e, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tval_reg_of hm' rfl]
      rfl
    · rw [tval_reg_of hm' rfl]
      rfl
    · rw [tval_reg_of hm' rfl]
      rfl
    · rw [tval_reg_of hm' rfl, ev_add, Holds.evc hH0 (s := .reg .X19) (i := 6) (by decide),
        TT_sv (by decide)]
      rfl
    · rw [tval_reg_of hm' rfl, ev_add, Holds.evc hH0 (s := .load 0 128 8) (i := 3) (by decide),
        TT_sv (by decide)]
      rfl
    · rw [tval_write hm' rfl rfl (by decide) (v := .bin .add .W64 (.load 0 120 8) (.lit 72))
        (by decide), ev_add, Holds.evc hH0 (s := .load 0 120 8) (i := 5) (by decide),
        TT_sv (by decide)]
      rfl
    · rw [tval_write hm' rfl rfl (by decide) (v := .bin .add .W64 (.load 0 120 8) (.lit 24))
        (by decide), ev_add, Holds.evc hH0 (s := .load 0 120 8) (i := 5) (by decide),
        TT_sv (by decide)]
      rfl
    · rw [tval_write hm' rfl rfl (by decide) (v := .bin .add .W64
        (.bin .mul .W64 (.load 0 56 8) (.lit 5928)) (.load 0 48 8)) (by decide), ev_add,
        ev_mul, Holds.evc hH0 (s := .load 0 56 8) (i := 2) (by decide),
        Holds.evc hH0 (s := .load 0 48 8) (i := 1) (by decide), TT_sv (by decide),
        TT_sv (by decide)]
      rfl
  · simp only [PcOk] at hpc
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b26Offset + b26.length = k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b26_next]] at hpc
    exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-! ## From the entry to the table loop -/

/-- **`accumulate_side` from its entry to the table loop's head** (`b27`, `k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset`) before turn
`0`: the description `DL` of turn `0`'s table, the forms at X1 still `Fm`. -/
theorem start_spec (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {R : MachineState → Prop}
    (cont : ∀ m, St m0 (TT SL m0 L rows bl Fm 0) DL m →
      FormsAt m.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b0Offset)⟩ := by
  have tail : ∀ m, St m0 (TT SL m0 L rows bl Fm 0) QZ m →
      FormsAt m.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩ := fun m hs hF ↦
    zero hp h hs hF fun m2 hs2 hF2 ↦ s24 hp h hmc hs2 hF2 fun m3 hs3 hF3 ↦
      s25 hp h hs3 hF3 fun m4 hs4 hF4 ↦ s26 hp h hs4 hF4 cont
  exact start0 hp h
    (fun m hs hF hc ↦ known hp h hee hmul hc hs hF fun m2 hs2 hF2 ↦
      k15 hp h hs2 hF2 fun m3 hs3 hF3 ↦ ones hp h hee hs3 hF3 tail)
    fun m hs hF hc ↦ k5 hp h hc hs hF fun m2 hs2 hF2 ↦ ones hp h hee hs2 hF2 tail

end

end NativeRustcVmArm.Bus.AccumulateSide
