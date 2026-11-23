module

public import NativeRustcVmArm.Whir.NextLevel.Mid

/-!
# `next_level`: what a callee gets

From a state of the frame, a callee using `N'` bytes below it gets the read-only data
(`rodataAt'`), the transcript's context (`whirT'`), the inputs (`whirIn'`) and outputs
(`whirOut'`). Symbolic values: `ev_add`, `ev_add2`, `ite_ult`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

public section

theorem ev_add [Labels] (m : MachineData) (rs : List (BitVec 64 × Nat)) (r : XReg) (n : Nat) :
    (Sym.bin .add .W64 (.reg r) (.lit n)).eval (Env.ofMachine m rs) =
      (m.regs.getXReg r).toBitVec + BitVec.ofNat 64 n := by
  sym_simp; rfl

theorem ev_add2 [Labels] (m : MachineData) (rs : List (BitVec 64 × Nat)) (r r' : XReg) :
    (Sym.bin .add .W64 (.reg r) (.reg r')).eval (Env.ofMachine m rs) =
      (m.regs.getXReg r).toBitVec + (m.regs.getXReg r').toBitVec := by
  sym_simp; rfl

theorem bv_ult_toNat' (a b : BitVec 64) : a.ult b = decide (a.toNat < b.toNat) := rfl

theorem apart_sub {a b : BitVec 64} {n m o k : Nat} (h : Apart a n b m) (hnw : NoWrap a n)
    (hk : o + k ≤ n) : Apart (a + BitVec.ofNat 64 o) k b m := by
  have := NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by unfold NoWrap at hnw; omega)
  unfold NoWrap at hnw
  unfold Apart at h ⊢
  omega

theorem whirOut_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : WhirOut m t a x n N) (hk : o + k ≤ n) :
    WhirOut m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨⟨NativeRustcVm.Mapped.sub h.1.1 hk, NativeRustcVm.NoWrap.sub h.1.2.1 hk,
    apart_sub h.1.2.2.1 h.1.2.1 hk, apart_sub h.1.2.2.2.1 h.1.2.1 hk,
    apart_sub h.1.2.2.2.2.1 h.1.2.1 hk, apart_sub h.1.2.2.2.2.2 h.1.2.1 hk⟩,
    fun t' ↦ apart_sub (h.2 t') h.1.2.1 hk⟩

theorem whirIn_sub {m : MachineData} {x : BitVec 64} {n N o k : Nat} (h : WhirIn m x n N)
    (hk : o + k ≤ n) : WhirIn m (x + BitVec.ofNat 64 o) k N :=
  ⟨⟨NativeRustcVm.Mapped.sub h.1.1 hk, NativeRustcVm.NoWrap.sub h.1.2 hk⟩,
    apart_sub h.2 h.1.2 hk⟩

theorem ite_ult [Labels] {env : Env} {x y z : Sym} {n : Nat} (hx : (x.eval env).toNat < n)
    (hn : n < 2 ^ 64) : (Sym.ite (.cmp .ult .W64 x (.lit n)) y z).eval env = y.eval env := by
  sym_simp
  have hc : (x.eval env).ult (BitVec.ofNat 64 n) = true := by
    rw [bv_ult_toNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    exact decide_eq_true hx
  simp only [hc, ↓reduceIte]

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec]; exact toNat_toUInt64 h

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {st : MachineData} {N' : Nat}

/-- The read-only data for a callee. -/
theorem rodataAt' (h : NextLevelPre a s level w rounds m0) (hf : NFr m0 st)
    (hle : 8192 + N' ≤ nextLevelStack) : RodataAt st N' := by
  have g := geo h
  have hN : nextLevelStack ≤ m0.regs.SP.toNat := h.1.1.2.1
  have hro := h.1.2.2.1
  have hqo := whirOut_sub (whirOut h) (o := queriesOff) (k := queryBufBytes) (by decide)
  refine rodataAt_callee hro hf.same (fun q hq t ↦ ?_) hf.sp hN (by rw [stack_eq]; decide)
    (by omega)
  rcases hq with hq | hq | hq
  · exact rodata_not_stack hro hN t hq
  · exact rodata_not_out h.1.2.2.2.2 h.2.1.footprint.1.2 t hq (hro t).2.1
  · exact rodata_not_out hqo.2 hqo.1.2.1 t hq (hro t).2.1

/-- **The transcript's context** for a callee. -/
theorem whirT' (h : NextLevelPre a s level w rounds m0) (hf : NFr m0 st)
    (hle : 8192 + N' ≤ nextLevelStack) : WhirT st (tA m0) a N' :=
  ⟨(ctx h).stackOk hf hle, (ctx h).rcAt hf hle, rodataAt' h hf hle, (ctx h).tstateOk hf hle,
    h.1.2.2.2.2⟩

/-- An output for a callee. -/
theorem whirOut' (h : NextLevelPre a s level w rounds m0) (hf : NFr m0 st)
    (hle : 8192 + N' ≤ nextLevelStack) {o : BitVec 64} {n : Nat}
    (ho : WhirOut m0 (tA m0) a o n nextLevelStack) : WhirOut st (tA m0) a o n N' :=
  ⟨(ctx h).outOk hf hle ho.1, ho.2⟩

/-- An input for a callee. -/
theorem whirIn' (h : NextLevelPre a s level w rounds m0) (hf : NFr m0 st)
    (hle : 8192 + N' ≤ nextLevelStack) {x : BitVec 64} {n : Nat}
    (hx : WhirIn m0 x n nextLevelStack) : WhirIn st x n N' :=
  ⟨⟨fun i hi ↦ hf.kept _ (hx.1.1 i hi), hx.1.2⟩, hf.apart (ctx h).hN hx.2 hle⟩

/-- The `WhirW` as an input. -/
theorem pIn (h : NextLevelPre a s level w rounds m0) :
    WhirIn m0 (pA m0) whirBytes nextLevelStack :=
  ⟨⟨(whirOut h).1.1, (whirOut h).1.2.1⟩, (whirOut h).1.2.2.2.2.1⟩

/-- The decoded area as an input. -/
theorem decIn (h : NextLevelPre a s level w rounds m0) :
    WhirIn m0 a.words (8 * a.len) nextLevelStack :=
  ⟨h.2.1.footprint.2.1, h.1.2.2.2.1.2.1⟩

/-- A frame range as an input for a callee. -/
theorem locIn (h : NextLevelPre a s level w rounds m0) (hf : NFr m0 st)
    (hle : 8192 + N' ≤ nextLevelStack) {o n : Nat} (hon : o + n ≤ 8192) :
    WhirIn st (loc m0 o) n N' :=
  ⟨⟨((ctx h).localOk hf hle hon).1, ((ctx h).localOk hf hle hon).2.1⟩,
    ((ctx h).localOk hf hle hon).2.2.2.2.1⟩

end

end

end NativeRustcVmArm.Whir.NextLevel
