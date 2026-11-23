module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Bus.GkrStep.Exec
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVmArm.Bus.GkrModel

/-!
# `gkr_step`'s frame, its exits

The 1392-byte frame below the entry's SP (`loc m0 o`, its byte `o`): the sumcheck's challenges
from `16` (up to `63` elements), its `Option<EW>` result at `1024`, then the three children at
`1024`, `1088`, `1152` (up to `4` elements each), the products at `1216`, the coordinates at
`1264`; the saved registers from `1296`. The outputs: the `TState` (X0) and the `GkrStateW` (X3).

- `exit_spec`: the epilogue (`.LGkrStep_15`), X0 the result's tag.
- `fail_spec`: `.LGkrStep_14`, the step failed.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(1296, .X29), (1304, .X30), (1312, .X28), (1320, .X27), (1328, .X26), (1336, .X25),
    (1344, .X24), (1352, .X23), (1360, .X22), (1368, .X21), (1376, .X20), (1384, .X19)]

/-- The callee-saved registers it does not save: none. -/
abbrev keep : List XReg := []

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1392 := by decide

theorem slots_ge : ∀ p ∈ slots, 1296 ≤ p.1 ∧ p.1 + 8 ≤ 1392 := by decide

/-- Bytes of the frame below the slots. -/
theorem slots_lo {o n : Nat} (h : o + n ≤ 1296) : ∀ p ∈ slots, o + n ≤ p.1 ∧ p.1 + 8 ≤ 1392 :=
  fun p hp ↦ ⟨by have := (slots_ge p hp).1; omega, (slots_ge p hp).2⟩

/-- The outputs: the `TState` (X0) and the `GkrStateW` (X3). -/
@[expose] def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X3.toBitVec gkrStateBytes q

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 1392 + BitVec.ofNat 64 o

theorem N_eq : gkrStepStack = 3216 := by decide

theorem N_ge : 1392 ≤ gkrStepStack := by decide

theorem le_bl : 1392 + bitLengthStack ≤ gkrStepStack := by decide
theorem le_grind : 1392 + grindStack ≤ gkrStepStack := by decide
theorem le_sq : 1392 + squeezeStack ≤ gkrStepStack := by decide
theorem le_pe : 1392 + polyEvalStack ≤ gkrStepStack := by decide
theorem le_sc : 1392 + sumcheckGkrStack ≤ gkrStepStack := by decide
theorem le_rs : 1392 + readScalarsStack ≤ gkrStepStack := by decide
theorem le_prod : 1392 + prodEStack ≤ gkrStepStack := by decide
theorem le_samp : 1392 + sampleChallengesStack ≤ gkrStepStack := by decide
theorem le_mle : 1392 + mleStack ≤ gkrStepStack := by decide

/-- `gkrStep`'s run from the entry's arguments. -/
abbrev run0 (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) : Option (GkrStateW × TState) :=
  (gkrStep m0.regs.X1.toNat (decide (m0.regs.X2.toNat = 1)) g0).run s0

/-- A word of value at most `1` is unchanged by truncation to its low half. -/
theorem trunc_small (x : UInt64) (h : x.toNat ≤ 1) :
    UnOp.apply .trunc .W32 x.toBitVec = x.toBitVec := by
  have hx : x = 0 ∨ x = 1 := by
    rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with h | h
    · exact .inl (UInt64.toNat_inj.mp h)
    · exact .inr (UInt64.toNat_inj.mp h)
  rcases hx with rfl | rfl <;> rfl

/-- `1 << step`, `step` `1` or `2`. -/
theorem lsl_one (x : UInt64) (h : x.toNat = 1 ∨ x.toNat = 2) :
    BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) x.toBitVec = BitVec.ofNat 64 (2 ^ x.toNat) := by
  have hx : x = 1 ∨ x = 2 := by
    rcases h with h | h
    · exact .inl (UInt64.toNat_inj.mp h)
    · exact .inr (UInt64.toNat_inj.mp h)
  rcases hx with rfl | rfl <;> rfl

/-- `(1 << step) | 1`, `step` `1` or `2`. -/
theorem orr_one (x : UInt64) (h : x.toNat = 1 ∨ x.toNat = 2) :
    BinOp.apply .orr .W64 (BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) x.toBitVec)
      (BitVec.ofNat 64 1) = BitVec.ofNat 64 (2 ^ x.toNat + 1) := by
  have hx : x = 1 ∨ x = 2 := by
    rcases h with h | h
    · exact .inl (UInt64.toNat_inj.mp h)
    · exact .inr (UInt64.toNat_inj.mp h)
  rcases hx with rfl | rfl <;> rfl

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

theorem pre_stack (h : GkrStepPre a s0 g0 m0) : StackOk m0 gkrStepStack := h.1
theorem pre_ts (h : GkrStepPre a s0 g0 m0) : TStateAt m0.dmem m0.regs.X0.toBitVec a s0 := h.2.2.1
theorem pre_step (h : GkrStepPre a s0 g0 m0) : m0.regs.X1.toNat = 1 ∨ m0.regs.X1.toNat = 2 :=
  h.2.2.2.2.1
theorem pre_last (h : GkrStepPre a s0 g0 m0) : m0.regs.X2.toNat ≤ 1 := h.2.2.2.2.2.1
theorem pre_size (h : GkrStepPre a s0 g0 m0) : g0.point.size + m0.regs.X1.toNat ≤ busPointCap :=
  h.2.2.2.2.2.2.1
theorem pre_gk (h : GkrStepPre a s0 g0 m0) :
    GkrOk m0 m0.regs.X0.toBitVec a m0.regs.X3.toBitVec gkrStepStack := h.2.2.2.2.2.2.2.1
theorem pre_gs (h : GkrStepPre a s0 g0 m0) : GkrStateWAt m0.dmem m0.regs.X3.toBitVec g0 :=
  h.2.2.2.2.2.2.2.2

/-- The entry's context. -/
theorem ctx (h : GkrStepPre a s0 g0 m0) : Ctx m0 m0.regs.X0.toBitVec a gkrStepStack 1392 :=
  ctx_of h.1 h.2.1 h.2.2.1 h.2.2.2.1 N_ge rfl

theorem outs_not_rc (h : GkrStepPre a s0 g0 m0) : ∀ q, outs m0 q → ¬InRange rcAddr 192 q :=
  fun _ hq ↦ hq.elim (fun hq ↦ (ctx h).not_rc_tstate hq) fun hq ↦ out_not_rc (ctx h) (pre_gk h) hq

theorem outs_not_frame (h : GkrStepPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬InRange (base m0 1392) 1392 q := fun _ hq ↦
  hq.elim (fun hq ↦ tstate_not_frame (ctx h) hq) fun hq ↦ out_not_frame (ctx h) (pre_gk h) hq

/-- A byte of the `GkrStateW` is neither the `TState`'s nor its decoded area's. -/
theorem p_apart (h : GkrStepPre a s0 g0 m0) {q : BitVec 64}
    (hq : InRange m0.regs.X3.toBitVec gkrStateBytes q) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hgo := pre_gk h
  have fp := (pre_ts h).footprint
  exact ⟨NativeRustcVm.Apart.not_inRange hgo.2.2.1 hgo.2.1 fp.1.2 hq,
    NativeRustcVm.Apart.not_inRange hgo.2.2.2.1 hgo.2.1 fp.2.1.2 hq⟩

/-- A byte of the frame is not the `GkrStateW`'s. -/
theorem frame_not_p (h : GkrStepPre a s0 g0 m0) {q : BitVec 64}
    (hq : InRange (base m0 1392) 1392 q) : ¬InRange m0.regs.X3.toBitVec gkrStateBytes q :=
  frame_not_out (ctx h) (pre_gk h) hq

omit [Labels] in
/-- A byte of the frame at `o < 1392`. -/
theorem loc_in (o : Nat) (ho : o < 1392) : InRange (base m0 1392) 1392 (loc m0 o) :=
  NativeRustcVm.inRange_add ho (by decide)

/-- **A callee's stack** below a state of the frame: apart from the `TState`, its area, the
`GkrStateW` and the frame. -/
theorem callee_apart (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) {N' : Nat}
    (hle : 1392 + N' ≤ gkrStepStack) {q : BitVec 64} (hq : InRange (stackBelow m N') N' q) :
    (¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q) ∧
      ¬InRange m0.regs.X3.toBitVec gkrStateBytes q ∧ ¬InRange (base m0 1392) 1392 q := by
  have c := ctx h
  have hat := Fr.at_ c hfr (outs_not_rc h)
  have htok := c.tstateOk hat hle
  have fp := (pre_ts h).footprint
  have hgk := c.outOk_sub hat hle (pre_gk h)
  have hspN := c.spN
  have hs := c.spN' hat
  have hl := m0.regs.SP.toNat_lt
  have e : (stackBelow m N').toNat = m.regs.SP.toNat - N' :=
    Sumcheck.toNat_stackBelow (by omega)
  have hnw : NativeRustcVm.NoWrap (stackBelow m N') N' := by
    unfold NativeRustcVm.NoWrap; rw [e]; omega
  refine ⟨⟨NativeRustcVm.Apart.not_inRange htok.1.symm hnw fp.1.2 hq,
    NativeRustcVm.Apart.not_inRange htok.2.1.symm hnw fp.2.1.2 hq⟩,
    NativeRustcVm.Apart.not_inRange hgk.2.2.2.2.1.symm hnw hgk.2.1 hq, fun hin ↦ ?_⟩
  have ef : (base m0 1392).toNat = m0.regs.SP.toNat - 1392 := base_toNat (by omega)
  rw [Sym.inRange_iff (by rw [e]; omega), e] at hq
  rw [Sym.inRange_iff (by rw [ef]; omega), ef] at hin
  omega

omit [Labels] in
/-- The frame's byte `o` as a number. -/
theorem loc_toNat {o : Nat} (hS : StackOk m0 gkrStepStack) (ho : o ≤ 1392) :
    (loc m0 o).toNat = m0.regs.SP.toNat - 1392 + o := by
  have hN := hS.2.1
  have := N_ge
  have hl := m0.regs.SP.toNat_lt
  have hb := base_toNat (m0 := m0) (F := 1392) (by omega)
  rw [NativeRustcVm.toNat_add_ofNat (by omega), hb]

omit [Labels] in
/-- `size < 64`, unsigned: below `64`. -/
theorem ult_lit : ∀ n < 64, CmpOp.ult.apply .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 64) = true := by
  decide +kernel

omit [Labels] in
/-- A byte of the frame at `o` outside `n` bytes of it at `o'`. -/
theorem loc_not_loc {o o' n : Nat} (hS : StackOk m0 gkrStepStack) (ho : o < 1392)
    (hon : o' + n ≤ 1392) (hd : o < o' ∨ o' + n ≤ o) : ¬InRange (loc m0 o') n (loc m0 o) :=
  not_loc (by have := hS.2.1; have := N_ge; omega) hon ho hd

omit [Labels] in
/-- `n` bytes of the frame at `o'` within `n'` bytes at `o`. -/
theorem loc_mono {o o' n n' : Nat} (hS : StackOk m0 gkrStepStack) (h1 : o ≤ o')
    (h2 : o' + n' ≤ o + n) (h3 : o + n ≤ 1392) {q : BitVec 64} (hq : InRange (loc m0 o') n' q) :
    InRange (loc m0 o) n q := by
  have hN := hS.2.1
  have := N_ge
  have hbF := base_toNat (m0 := m0) (F := 1392) (by omega)
  have hl := m0.regs.SP.toNat_lt
  have e1 : (loc m0 o).toNat = (base m0 1392).toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  have e2 : (loc m0 o').toNat = (base m0 1392).toNat + o' :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [e2]; omega), e2] at hq
  rw [Sym.inRange_iff (by rw [e1]; omega), e1]
  omega

/-- The `TState` kept by a leaf call from the frame (memory changed in its stack only). -/
theorem ts_leaf (h : GkrStepPre a s0 g0 m0) {m m' : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) {N' : Nat}
    (hle : 1392 + N' ≤ gkrStepStack) (hc : Changes m m' N' 0 0) (hk : Kept m.dmem m'.dmem)
    {s : TState} (ht : TStateAt m.dmem m0.regs.X0.toBitVec a s) :
    TStateAt m'.dmem m0.regs.X0.toBitVec a s :=
  ht.frame hk (fun _ hq ↦ hq.elim (fun h' ↦ (callee_apart h hfr hle h').1) False.elim)
    (Bus.changes_zero (outs := fun _ ↦ False) hc)

/-- The `TState` kept by a block writing the frame (region 0) only. -/
theorem ts_block (h : GkrStepPre a s0 g0 m0) {m m' : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m [(base m0 1392, 1392)]) S m')
    (hwf : (Env.ofMachine m [(base m0 1392, 1392)]).WF)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 1392) {s : TState}
    (ht : TStateAt m.dmem m0.regs.X0.toBitVec a s) : TStateAt m'.dmem m0.regs.X0.toBitVec a s :=
  ht.frame (fun q hq ↦ hm.kept hwf q hq) (fun _ hq ↦ frame_not_tstate (ctx h) hq)
    (NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun _ hq ↦
      Written.inRange (r := 0) rfl (Bus.frame_mapped (pre_stack h) N_ge).2 hS hq)

omit [Labels] in
/-- Elements of the frame kept by a call writing below the frame and `X`. -/
theorem ews_call {m d : MachineData} (hS : StackOk m0 gkrStepStack)
    (hsp : m.regs.SP.toBitVec = base m0 1392) {N' : Nat} (hle : 1392 + N' ≤ gkrStepStack)
    {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    {o : Nat} {xs : List EW} (ho : o + 16 * xs.length ≤ 1392)
    (hX : ∀ i < 16 * xs.length, ¬X (loc m0 (o + i)))
    (h : NativeRustcVm.EWsAt m.dmem (loc m0 o) xs) : NativeRustcVm.EWsAt d.dmem (loc m0 o) xs :=
  keep_frame hsp (by have := hS.2.1; omega) hs (by rw [NativeRustcVm.length_ewsBytes]; exact ho)
    (fun i hi ↦ by rw [NativeRustcVm.length_ewsBytes] at hi; exact hX i hi) h

omit [Labels] in
/-- Elements of the frame kept by a leaf call. -/
theorem ews_leaf {m d : MachineData} (hS : StackOk m0 gkrStepStack)
    (hsp : m.regs.SP.toBitVec = base m0 1392) {N' : Nat} (hle : 1392 + N' ≤ gkrStepStack)
    (hc : Changes m d N' 0 0) {o : Nat} {xs : List EW} (ho : o + 16 * xs.length ≤ 1392)
    (h : NativeRustcVm.EWsAt m.dmem (loc m0 o) xs) : NativeRustcVm.EWsAt d.dmem (loc m0 o) xs :=
  ews_call hS hsp hle (X := fun _ ↦ False) (Bus.changes_zero hc) ho (fun _ _ h ↦ h) h

/-- Elements of the frame kept by a block whose writes in the frame are apart from them. -/
theorem ews_block {m m' : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m [(base m0 1392, 1392)]) S m')
    (hwf : (Env.ofMachine m [(base m0 1392, 1392)]).WF) {o L : Nat} (hL : o + L ≤ 1392)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ o ∨ o + L ≤ w.off)) {xs : List EW}
    (hxs : 16 * xs.length ≤ L) (h : NativeRustcVm.EWsAt m.dmem (loc m0 o) xs) :
    NativeRustcVm.EWsAt m'.dmem (loc m0 o) xs :=
  keep_block hm hwf (sizes := [1392]) rfl (r := 0) rfl hL (fun w hw' ↦ .inl (hw w hw'))
    (by rw [NativeRustcVm.length_ewsBytes]; exact hxs) h

omit [Labels] in
/-- `n` bytes of the frame at `o` miss the frame's byte `o' + i` beyond them. -/
theorem not_loc' {o o' n i : Nat} (hS : StackOk m0 gkrStepStack) (hon : o + n ≤ 1392)
    (hi : o' + i < 1392) (hd : o' + i < o ∨ o + n ≤ o' + i) :
    ¬InRange (loc m0 o) n (loc m0 (o' + i)) :=
  loc_not_loc hS hi hon hd

/-- The frame's byte `o < 1392` is not the `TState`'s. -/
theorem loc_not_ts (h : GkrStepPre a s0 g0 m0) {o : Nat} (ho : o < 1392) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes (loc m0 o) :=
  (frame_not_tstate (ctx h) (loc_in o ho)).1

end

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- What `gkr_step` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ GkrStepPost a s0 g0 m0 st.data

/-- **The epilogue** (`.LGkrStep_15`, `b33`): X0 the result's tag, the outputs its state. -/
theorem exit_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m)
    (hx0 : m.regs.X0 = okWord (run0 s0 g0 m0).isSome)
    (hok : ∀ g' s', run0 s0 g0 m0 = some (g', s') →
      TStateAt m.dmem m0.regs.X0.toBitVec a s' ∧ GkrStateWAt m.dmem m0.regs.X3.toBitVec g') :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b33Offset)⟩ := by
  have hS := pre_stack h
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then (b33_in_code.trans hp.1 (by simp [b33])) run_b33 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm' hwf (by decide)
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have e0 : st.data.regs.X0 = m.regs.X0 := reg_of hm' (r := .X0) (r' := .X0) rfl
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], by rw [e0]; exact hx0,
    fun g' s' he ↦ by rw [hd]; exact hok g' s' he, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact .inr (.inr hq)
    · exact .inl hq
    · exact .inr (.inl hq)

/-- **A failed step** (`.LGkrStep_14`, `b32`): X0 = `0`. -/
theorem fail_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) (hr : run0 s0 g0 m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b32Offset)⟩ := by
  refine Fr.runBlock (pre_stack h) N_ge rfl hfr (b32_in_code.trans hp.1 (by simp [b32])) run_b32
    rfl rfl (by decide) (by decide) fun st hfr' _ hm hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc (exit_spec hp h hfr' ?_ fun g' s' he ↦ by rw [hr] at he; cases he)
  rw [hr]
  exact UInt64.toBitVec_inj.mp (reg_lit hm (r := .X0) (n := 0) rfl)

end

public section

/-- **`SpongeW::squeeze` on the `TState`'s sponge** from the frame: the challenge in X0, X1, the
`TState` then `sampleChallenge`'s. -/
theorem squeeze_call [Host] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
    {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop}
    (c : Ctx m0 t a N F)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hf : Fr m0 F N slots keep outs st.data) (hrc : ∀ q, outs q → ¬InRange rcAddr 192 q)
    (hle : F + squeezeStack ≤ N) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hto : ∀ q, InRange t tstateBytes q → outs q)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0.toBitVec = t) {s : TState} (hts : TStateAt st.data.dmem t a s)
    (cont : ∀ m2 : MachineData, Fr m0 F N slots keep outs m2 →
      TStateAt m2.dmem t a { s with sponge := s.sponge.squeeze.2 } →
      m2.regs.X0 = s.sponge.squeeze.1.c0 → m2.regs.X1 = s.sponge.squeeze.1.c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange t spongeBytes q ∨
        InRange (stackBelow st.data squeezeStack) squeezeStack q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have sponge_le : spongeBytes ≤ tstateBytes := by decide
  have hat := Bus.Gkr.Fr.at_ c hf hrc
  have hfp := hts.footprint
  have htok := c.tstateOk hat hle
  have hspN := c.spN
  have hs := c.spN' hat
  have hl := m0.regs.SP.toNat_lt
  have e : (stackBelow st.data squeezeStack).toNat = st.data.regs.SP.toNat - squeezeStack :=
    Sumcheck.toNat_stackBelow (by have := c.le; omega)
  have hnws : NoWrap (stackBelow st.data squeezeStack) squeezeStack := by
    unfold NoWrap; rw [e]; omega
  have hnwt : NoWrap t spongeBytes := NativeRustcVm.NoWrap.mono hfp.1.2 sponge_le
  have hpre : SqueezePre s.sponge st.data := by
    unfold SqueezePre
    rw [hx0]
    exact ⟨c.stackOk hat hle, c.rcAt hat hle, c.spongeOk hat hle, hts.sponge⟩
  refine Bus.Gkr.Fr.callSpec hf c.spN hle hkeep hsl hfr (hsq s.sponge) hpc hpre
    (fun m' hq ↦ ?_) fun m2 hf2 hq hcs ↦ ?_
  · obtain ⟨-, -, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · right
      rw [hx0] at hq
      exact hto q (NativeRustcVm.InRange.mono hq hnwt hfp.1.2 (Nat.le_refl _)
        (by have := sponge_le; omega))
    · exact Or.inl hq
  · obtain ⟨h0, h1, hsp, hs, hsv⟩ := hq
    rw [hx0] at hsp hs
    refine cont m2 hf2 ?_ h0 h1 hcs hs
    refine hts.with_sponge (R := fun q ↦ InRange (stackBelow st.data squeezeStack) squeezeStack q)
      hsv.2.2 (fun q hq ↦ ⟨NativeRustcVm.Apart.not_inRange htok.1.symm hnws hfp.1.2 hq,
        NativeRustcVm.Apart.not_inRange htok.2.1.symm hnws hfp.2.1.2 hq⟩)
      (NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_) hsp
    rcases hq with hq | hq
    · left
      obtain ⟨i, hi, rfl⟩ := NativeRustcVm.InRange.exists hq
      exact ⟨i, by have := sponge_le; omega, hi, rfl⟩
    · exact Or.inr hq

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

/-- **At `b7`** (`k + NativeRustcVmArm.Vm.GkrStep.b7Offset`): the sumcheck's challenges `xs` at `16`, its claim `cl` at `1032`. -/
structure AtChildren (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (c cl : EW)
    (xs : Array EW) (s2 : TState) (m : MachineData) : Prop where
  fr : Fr m0 1392 gkrStepStack slots keep (outs m0) m
  x19 : m.regs.getXReg .X19 = m0.regs.X3
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  x22 : m.regs.getXReg .X22 = m0.regs.X2
  x23 : (m.regs.getXReg .X23).toNat = xs.size
  x24 : m.regs.getXReg .X24 = c.c0
  x25 : m.regs.getXReg .X25 = c.c1
  x26 : (m.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 (2 ^ m0.regs.X1.toNat)
  x27 : (m.regs.getXReg .X27).toBitVec = loc m0 1024
  size : xs.size + m0.regs.X1.toNat ≤ busPointCap
  cl0 : NativeRustcVm.WordAt m.dmem (loc m0 1032) cl.c0
  cl1 : NativeRustcVm.WordAt m.dmem (loc m0 1040) cl.c1
  hxs : NativeRustcVm.EWsAt m.dmem (loc m0 16) xs.toList
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s2
  run : run0 s0 g0 m0 = gkrChildren m0.regs.X1.toNat c cl xs s2

/-- **At `b19`** (`k + NativeRustcVmArm.Vm.GkrStep.b19Offset`): the check passed; the children at `1024`, `1088`, `1152`. -/
structure AtTail (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs h0 h1 h2 : Array EW) (s3 : TState) (m : MachineData) : Prop where
  fr : Fr m0 1392 gkrStepStack slots keep (outs m0) m
  x19 : m.regs.getXReg .X19 = m0.regs.X3
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  x22 : m.regs.getXReg .X22 = m0.regs.X2
  x23 : (m.regs.getXReg .X23).toNat = xs.size
  x26 : (m.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 (2 ^ m0.regs.X1.toNat)
  x27 : (m.regs.getXReg .X27).toBitVec = loc m0 1024
  size : xs.size + m0.regs.X1.toNat ≤ busPointCap
  hxs : NativeRustcVm.EWsAt m.dmem (loc m0 16) xs.toList
  c0 : NativeRustcVm.EWsAt m.dmem (loc m0 1024) h0.toList
  c1 : NativeRustcVm.EWsAt m.dmem (loc m0 1088) h1.toList
  c2 : NativeRustcVm.EWsAt m.dmem (loc m0 1152) h2.toList
  s0' : h0.size = 2 ^ m0.regs.X1.toNat
  s1' : h1.size = 2 ^ m0.regs.X1.toNat
  s2' : h2.size = 2 ^ m0.regs.X1.toNat
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s3
  run : run0 s0 g0 m0 = ((sampleChallenges m0.regs.X1.toNat).run s3).bind fun y ↦
    some (⟨#[multilinearEval h0 y.1, multilinearEval h1 y.1, multilinearEval h2 y.1],
      y.1 ++ xs⟩, y.2)

/-- **At `.LGkrStep_11`** (`k + NativeRustcVmArm.Vm.GkrStep.b29Offset`): the values, the length and the coordinates `y` written;
the challenges `xs` to copy. -/
structure AtCopy (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs y vs : Array EW) (s' : TState) (m : MachineData) : Prop where
  fr : Fr m0 1392 gkrStepStack slots keep (outs m0) m
  x19 : m.regs.getXReg .X19 = m0.regs.X3
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x23 : (m.regs.getXReg .X23).toNat = xs.size
  size : xs.size + m0.regs.X1.toNat ≤ busPointCap
  ysize : y.size = m0.regs.X1.toNat
  vsize : vs.size = 3
  hxs : NativeRustcVm.EWsAt m.dmem (loc m0 16) xs.toList
  vals : NativeRustcVm.EWsAt m.dmem m0.regs.X3.toBitVec vs.toList
  len : NativeRustcVm.WordAt m.dmem (off m0.regs.X3.toBitVec 48) (y.size + xs.size).toUInt64
  ys : NativeRustcVm.EWsAt m.dmem (off m0.regs.X3.toBitVec 56) y.toList
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s'
  run : run0 s0 g0 m0 = some (⟨vs, y ++ xs⟩, s')

end

end NativeRustcVmArm.Bus.GkrStep
