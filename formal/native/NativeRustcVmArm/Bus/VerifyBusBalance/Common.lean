module

public import NativeRustcVmArm.Bus.VerifyBusBalance.Exec
public import NativeRustcVmArm.Bus.VerifyBusBalance.Model
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVm.Tables.Same
public import NativeRustcVmArm.Bus.Frame

/-!
# `verify_bus_balance`'s frame, its exits

The 5488-byte frame below the entry's SP (`loc m0 o`, its byte `o`): the stack arguments at `0`,
scalars at `80` to `136`, the framework sizes at `136`, the three sides' layouts at `160`, `1048`,
`1936`, the weights at `2824`, the `GkrStateW` at `3080`, the memory's two scalars at `4144`, the
callees' outputs from `4176`, the bytecode point at `4176`, the share at `5248`, the closure's
environment at `5264`, the fingerprints at `5344`; the saved registers from `5392`. The outputs:
the `TState` (X0), the bus (X4), the claims (X5).

- `exit_spec`: the epilogue (`.LVerifyBusBalance_23`), X0 the result's tag.
- `fail_spec`: `.LVerifyBusBalance_22`, the phase failed.
- `same_call`, `same_block`: bytes of the frame kept.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(5392, .X29), (5400, .X30), (5408, .X28), (5416, .X27), (5424, .X26), (5432, .X25),
    (5440, .X24), (5448, .X23), (5456, .X22), (5464, .X21), (5472, .X20), (5480, .X19)]

/-- The callee-saved registers it does not save: none. -/
abbrev keep : List XReg := []

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 5488 := by decide

theorem slots_ge : ∀ p ∈ slots, 5392 ≤ p.1 ∧ p.1 + 8 ≤ 5488 := by decide

/-- Bytes of the frame below the slots. -/
theorem slots_lo {o n : Nat} (h : o + n ≤ 5392) : ∀ p ∈ slots, o + n ≤ p.1 ∧ p.1 + 8 ≤ 5488 :=
  fun p hp ↦ ⟨by have := (slots_ge p hp).1; omega, (slots_ge p hp).2⟩

/-- The outputs: the `TState` (X0), the bus (X4), the claims (X5). -/
@[expose] def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X4.toBitVec busBytes q ∨
    InRange m0.regs.X5.toBitVec claimsBytes q

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 5488 + BitVec.ofNat 64 o

theorem N_eq : verifyBusBalanceStack = 18288 := by decide

theorem N_ge : 5488 ≤ verifyBusBalanceStack := by decide

theorem le_bl : 5488 + busLayoutStack ≤ verifyBusBalanceStack := by decide
theorem le_len : 5488 + bitLengthStack ≤ verifyBusBalanceStack := by decide
theorem le_grind : 5488 + grindStack ≤ verifyBusBalanceStack := by decide
theorem le_samp : 5488 + sampleChallengesStack ≤ verifyBusBalanceStack := by decide
theorem le_sq : 5488 + squeezeStack ≤ verifyBusBalanceStack := by decide
theorem le_gkr : 5488 + verifyGkrStack ≤ verifyBusBalanceStack := by decide
theorem le_rss : 5488 + readScalarsStack ≤ verifyBusBalanceStack := by decide
theorem le_rs : 5488 + readScalarStack ≤ verifyBusBalanceStack := by decide
theorem le_pc : 5488 + pushClaimStack ≤ verifyBusBalanceStack := by decide
theorem le_share : 5488 + bytecodeShareStack ≤ verifyBusBalanceStack := by decide
theorem le_cbv : 5488 + computedBytecodeValueStack ≤ verifyBusBalanceStack := by decide
theorem le_kpow : 5488 + kpowStack ≤ verifyBusBalanceStack := by decide
theorem le_fp : 5488 + fpClosureStack ≤ verifyBusBalanceStack := by decide
theorem le_acc : 5488 + accumulateSideStack ≤ verifyBusBalanceStack := by decide
theorem le_ext : 5488 + bufExtendStack ≤ verifyBusBalanceStack := by decide
theorem le_mem : 5488 + 0 ≤ verifyBusBalanceStack := by decide

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-! ## The precondition's parts -/

section
variable (h : VerifyBusBalancePre a s0 L m0)
include h

theorem pre_stack : StackOk m0 verifyBusBalanceStack := h.1
theorem pre_rc : RcAt m0 verifyBusBalanceStack := h.2.1
theorem pre_ro : RodataAt m0 verifyBusBalanceStack := h.2.2.1
theorem pre_ts : TStateAt m0.dmem m0.regs.X0.toBitVec a s0 := h.2.2.2.1
theorem pre_tok : TStateOk m0 m0.regs.X0.toBitVec a verifyBusBalanceStack := h.2.2.2.2.1
theorem pre_lay : LayoutWAt m0.dmem m0.regs.X1.toBitVec L := h.2.2.2.2.2.1
theorem pre_layOk : InOk m0 m0.regs.X1.toBitVec layoutBytes verifyBusBalanceStack :=
  h.2.2.2.2.2.2.1
theorem pre_layT : Apart m0.regs.X1.toBitVec layoutBytes m0.regs.X0.toBitVec tstateBytes :=
  h.2.2.2.2.2.2.2.1
theorem pre_n : L.bytecode.size = m0.regs.X3.toNat := h.2.2.2.2.2.2.2.2.1
theorem pre_bc : NativeRustcVm.WordsAt m0.dmem m0.regs.X2.toBitVec L.bytecode.toList :=
  h.2.2.2.2.2.2.2.2.2.1
theorem pre_bcR : Readable m0 m0.regs.X2.toBitVec (8 * m0.regs.X3.toNat) :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem pre_bcS : 0 < m0.regs.X3.toNat →
    OffStack m0 m0.regs.X2.toBitVec (8 * m0.regs.X3.toNat) verifyBusBalanceStack :=
  h.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_bus :
    OutOk m0 m0.regs.X0.toBitVec a m0.regs.X4.toBitVec busBytes verifyBusBalanceStack :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busR : RodataApart m0.regs.X4.toBitVec busBytes := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busL : Apart m0.regs.X4.toBitVec busBytes m0.regs.X1.toBitVec layoutBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busB : 0 < m0.regs.X3.toNat →
    Apart m0.regs.X4.toBitVec busBytes m0.regs.X2.toBitVec (8 * m0.regs.X3.toNat) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_cl : OutOk m0 m0.regs.X0.toBitVec a m0.regs.X5.toBitVec claimsBytes
    verifyBusBalanceStack := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_clR : RodataApart m0.regs.X5.toBitVec claimsBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_clL : Apart m0.regs.X5.toBitVec claimsBytes m0.regs.X1.toBitVec layoutBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_clB : 0 < m0.regs.X3.toNat →
    Apart m0.regs.X5.toBitVec claimsBytes m0.regs.X2.toBitVec (8 * m0.regs.X3.toNat) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busCl : Apart m0.regs.X4.toBitVec busBytes m0.regs.X5.toBitVec claimsBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_tR : RodataApart m0.regs.X0.toBitVec tstateBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_bcT : 0 < m0.regs.X3.toNat →
    Apart m0.regs.X2.toBitVec (8 * m0.regs.X3.toNat) m0.regs.X0.toBitVec tstateBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The entry's context. -/
theorem ctx : Ctx m0 m0.regs.X0.toBitVec a verifyBusBalanceStack 5488 :=
  ctx_of (pre_stack h) (pre_rc h) (pre_ts h) (pre_tok h) N_ge rfl

theorem outs_not_rc : ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun _ hq ↦ by
  rcases hq with hq | hq | hq
  · exact (ctx h).not_rc_tstate hq
  · exact out_not_rc (ctx h) (pre_bus h) hq
  · exact out_not_rc (ctx h) (pre_cl h) hq

theorem outs_not_frame : ∀ q, outs m0 q → ¬InRange (base m0 5488) 5488 q := fun _ hq ↦ by
  rcases hq with hq | hq | hq
  · exact tstate_not_frame (ctx h) hq
  · exact out_not_frame (ctx h) (pre_bus h) hq
  · exact out_not_frame (ctx h) (pre_cl h) hq

end

omit [Labels] in
/-- A byte of the frame at `o < 5488`. -/
theorem loc_in (o : Nat) (ho : o < 5488) : InRange (base m0 5488) 5488 (loc m0 o) :=
  NativeRustcVm.inRange_add ho (by decide)

omit [Labels] in
/-- The frame's byte `o` as a number. -/
theorem loc_toNat {o : Nat} (hS : StackOk m0 verifyBusBalanceStack) (ho : o ≤ 5488) :
    (loc m0 o).toNat = m0.regs.SP.toNat - 5488 + o := by
  have hN := hS.2.1
  have := N_ge
  have hl := m0.regs.SP.toNat_lt
  have hb := base_toNat (m0 := m0) (F := 5488) (by omega)
  rw [NativeRustcVm.toNat_add_ofNat (by omega), hb]

omit [Labels] in
/-- A byte of the frame at `o` outside `n` bytes of it at `o'`. -/
theorem loc_not_loc {o o' n : Nat} (hS : StackOk m0 verifyBusBalanceStack) (ho : o < 5488)
    (hon : o' + n ≤ 5488) (hd : o < o' ∨ o' + n ≤ o) : ¬InRange (loc m0 o') n (loc m0 o) :=
  not_loc (by have := hS.2.1; have := N_ge; omega) hon ho hd

omit [Labels] in
/-- `n` bytes of the frame at `o'` within `n'` bytes at `o`. -/
theorem loc_mono {o o' n n' : Nat} (hS : StackOk m0 verifyBusBalanceStack) (h1 : o ≤ o')
    (h2 : o' + n' ≤ o + n) (h3 : o + n ≤ 5488) {q : BitVec 64} (hq : InRange (loc m0 o') n' q) :
    InRange (loc m0 o) n q := by
  have hN := hS.2.1
  have := N_ge
  have hbF := base_toNat (m0 := m0) (F := 5488) (by omega)
  have hl := m0.regs.SP.toNat_lt
  have e1 : (loc m0 o).toNat = (base m0 5488).toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  have e2 : (loc m0 o').toNat = (base m0 5488).toNat + o' :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [e2]; omega), e2] at hq
  rw [Sym.inRange_iff (by rw [e1]; omega), e1]
  omega

/-- The frame's byte `o < 5488` is no output's. -/
theorem loc_not_outs (h : VerifyBusBalancePre a s0 L m0) {o : Nat} (ho : o < 5488) :
    ¬outs m0 (loc m0 o) := fun hq ↦ outs_not_frame h _ hq (loc_in o ho)

/-- The frame's byte `o < 5488` is not the `TState`'s. -/
theorem loc_not_ts (h : VerifyBusBalancePre a s0 L m0) {o : Nat} (ho : o < 5488) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes (loc m0 o) :=
  (frame_not_tstate (ctx h) (loc_in o ho)).1

/-- **A callee's stack** below a state of the frame: apart from the `TState`, its area, the
outputs and the frame. -/
theorem callee_apart (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) {q : BitVec 64}
    (hq : InRange (stackBelow m N') N' q) :
    ¬InRange a.words (8 * a.len) q ∧ ¬outs m0 q ∧ ¬InRange (base m0 5488) 5488 q := by
  have c := ctx h
  have hat := Fr.at_ c hfr (outs_not_rc h)
  have htok := c.tstateOk hat hle
  have fp := (pre_ts h).footprint
  have hb := c.outOk_sub hat hle (pre_bus h)
  have hc := c.outOk_sub hat hle (pre_cl h)
  have hspN := c.spN
  have hs := c.spN' hat
  have hl := m0.regs.SP.toNat_lt
  have e : (stackBelow m N').toNat = m.regs.SP.toNat - N' :=
    Sumcheck.toNat_stackBelow (by omega)
  have hnw : NativeRustcVm.NoWrap (stackBelow m N') N' := by
    unfold NativeRustcVm.NoWrap; rw [e]; omega
  refine ⟨NativeRustcVm.Apart.not_inRange htok.2.1.symm hnw fp.2.1.2 hq, ?_, fun hin ↦ ?_⟩
  · rintro (h' | h' | h')
    · exact NativeRustcVm.Apart.not_inRange htok.1.symm hnw fp.1.2 hq h'
    · exact NativeRustcVm.Apart.not_inRange hb.2.2.2.2.1.symm hnw hb.2.1 hq h'
    · exact NativeRustcVm.Apart.not_inRange hc.2.2.2.2.1.symm hnw hc.2.1 hq h'
  · have ef : (base m0 5488).toNat = m0.regs.SP.toNat - 5488 := base_toNat (by omega)
    rw [Sym.inRange_iff (by rw [e]; omega), e] at hq
    rw [Sym.inRange_iff (by rw [ef]; omega), ef] at hin
    omega

end

/-! ## Where a block wrote -/

public section

/-- Where a block's writes are: between offsets `lo` and `hi` of region `r`. -/
theorem written_in [Labels] {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) {lo hi : Nat}
    (hS : (S.mem.all fun w ↦ w.r == r && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) = true)
    {q : BitVec 64} (h : Written env S q) : b.toNat + lo ≤ q.toNat ∧ q.toNat < b.toNat + hi := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  have := List.all_eq_true.mp hS w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨⟨hr, hlo⟩, hhi⟩ := this
  rw [hr, hb] at hb'
  cases hb'
  omega

end

/-! ## Disjointness -/

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

omit [Labels] in
/-- A range of the frame is in the frame. -/
theorem loc_frame (hS : StackOk m0 verifyBusBalanceStack) {o n : Nat} (hon : o + n ≤ 5488)
    {q : BitVec 64} (hq : InRange (loc m0 o) n q) : InRange (base m0 5488) 5488 q := by
  have h0 : loc m0 0 = base m0 5488 := (Bus.add_zero' _)
  rw [← h0]
  exact loc_mono hS (Nat.zero_le _) (by omega) (by omega) hq

/-- A range of the frame is neither the `TState`'s nor its area's. -/
theorem loc_not_tsw (h : VerifyBusBalancePre a s0 L m0) {o n : Nat} (hon : o + n ≤ 5488)
    {q : BitVec 64} (hq : InRange (loc m0 o) n q) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q :=
  frame_not_tstate (ctx h) (loc_frame (pre_stack h) hon hq)

/-- A byte of the bus is neither the `TState`'s nor its area's. -/
theorem bus_not_tsw (h : VerifyBusBalancePre a s0 L m0) {q : BitVec 64}
    (hq : InRange m0.regs.X4.toBitVec busBytes q) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hb := pre_bus h
  have fp := (pre_ts h).footprint
  exact ⟨NativeRustcVm.Apart.not_inRange hb.2.2.1 hb.2.1 fp.1.2 hq,
    NativeRustcVm.Apart.not_inRange hb.2.2.2.1 hb.2.1 fp.2.1.2 hq⟩

/-- A byte of the claims is neither the `TState`'s nor its area's. -/
theorem cl_not_tsw (h : VerifyBusBalancePre a s0 L m0) {q : BitVec 64}
    (hq : InRange m0.regs.X5.toBitVec claimsBytes q) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hb := pre_cl h
  have fp := (pre_ts h).footprint
  exact ⟨NativeRustcVm.Apart.not_inRange hb.2.2.1 hb.2.1 fp.1.2 hq,
    NativeRustcVm.Apart.not_inRange hb.2.2.2.1 hb.2.1 fp.2.1.2 hq⟩

/-- A byte of the bus is not the claims'. -/
theorem bus_not_cl (h : VerifyBusBalancePre a s0 L m0) {q : BitVec 64}
    (hq : InRange m0.regs.X4.toBitVec busBytes q) : ¬InRange m0.regs.X5.toBitVec claimsBytes q :=
  NativeRustcVm.Apart.not_inRange (pre_busCl h) (pre_bus h).2.1 (pre_cl h).2.1 hq

/-- A byte of the bus is not the frame's. -/
theorem bus_not_loc (h : VerifyBusBalancePre a s0 L m0) {q : BitVec 64}
    (hq : InRange m0.regs.X4.toBitVec busBytes q) {o n : Nat} (hon : o + n ≤ 5488) :
    ¬InRange (loc m0 o) n q := fun h' ↦
  outs_not_frame h q (.inr (.inl hq)) (loc_frame (pre_stack h) hon h')

/-- A byte of the claims is not the frame's. -/
theorem cl_not_loc (h : VerifyBusBalancePre a s0 L m0) {q : BitVec 64}
    (hq : InRange m0.regs.X5.toBitVec claimsBytes q) {o n : Nat} (hon : o + n ≤ 5488) :
    ¬InRange (loc m0 o) n q := fun h' ↦
  outs_not_frame h q (.inr (.inr hq)) (loc_frame (pre_stack h) hon h')

omit [Labels] in
/-- Fewer bytes of the bus. -/
theorem bus_sub {b : BitVec 64} (hnw : NativeRustcVm.NoWrap b busBytes) {o n : Nat}
    (hon : o + n ≤ busBytes) {q : BitVec 64} (hq : InRange (b + BitVec.ofNat 64 o) n q) :
    InRange b busBytes q := by
  rw [busBytes_eq] at hon hnw
  unfold NativeRustcVm.NoWrap at hnw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold InRange at hq; omega
  have e : (b + BitVec.ofNat 64 o).toNat = b.toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [e]; omega), e] at hq
  rw [Sym.inRange_iff (by rw [busBytes_eq]; omega), busBytes_eq]
  omega

omit [Labels] in
/-- The forms are bytes of the bus. -/
theorem forms_sub {b : BitVec 64} (hnw : NativeRustcVm.NoWrap b busBytes) {q : BitVec 64}
    (hq : InRange b formsBytes q) : InRange b busBytes q := by
  have := bus_sub (o := 0) (n := formsBytes) hnw (by decide) (q := q)
    (by rw [Bus.add_zero']; exact hq)
  exact this

end

/-! ## Bytes of the frame kept -/

public section

/-- **Bytes of the frame kept by a call** writing below the frame and `X`. -/
theorem same_call {m0 m d : MachineData} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    {o n : Nat} (hon : o + n ≤ 5488) (hX : ∀ j < n, ¬X (loc m0 o + BitVec.ofNat 64 j)) :
    NativeRustcVm.Layout.Same m.dmem d.dmem (loc m0 o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ hq.elim
    (Bus.slot_not_callee (by have := hS.2.1; omega) hsp (by omega)) (hX j hj)

/-- **Bytes of the frame kept by a block** whose writes in the frame miss them, its other
writes within their regions (`sizes`). -/
theorem same_block [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).WF) {sizes : List Nat}
    (hsz : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).regions.map Prod.snd = sizes)
    {o n : Nat} (hon : o + n ≤ 5488)
    (hw : (S.mem.all fun w ↦ (w.r == 0 && (decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off))) ||
      (w.r != 0 && decide (w.off + w.n ≤ (sizes[w.r]?).getD 0))) = true) :
    NativeRustcVm.Layout.Same m.dmem m'.dmem (loc m0 o) n := by
  intro j hj
  rw [NativeRustcVm.addr_add_add]
  refine hm.get?_mem0 hwf (not_written hwf hsz (r := 0) rfl (j := o + j) (by omega) fun w hw' ↦ ?_)
  have := List.all_eq_true.mp hw w hw'
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at this
  rcases this with ⟨hr, h' | h'⟩ | ⟨hr, h'⟩
  · exact .inl ⟨hr, by omega⟩
  · exact .inl ⟨hr, by omega⟩
  · exact .inr ⟨hr, h'⟩

end

/-! ## Locals kept -/

public section

/-- **Bytes of the frame kept by a call** writing below the frame and `X`, apart from them. -/
theorem keep_loc {m0 st : MachineData} {d : DataMem} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : st.regs.SP.toBitVec = base m0 5488) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) {X : BitVec 64 → Prop}
    (hs : SameOutside st.dmem d (fun q ↦ InRange (stackBelow st N') N' q ∨ X q))
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 5488)
    (hX : ∀ q, X q → ¬InRange (loc m0 o) bs.length q)
    (h : NativeRustcVm.BytesAt st.dmem (loc m0 o) bs) : NativeRustcVm.BytesAt d (loc m0 o) bs :=
  keep_frame hsp (by have := hS.2.1; omega) hs ho
    (fun i hi hq ↦ hX _ hq (by
      rw [← NativeRustcVm.addr_add_add]
      exact NativeRustcVm.inRange_add hi (by omega))) h

/-- **Bytes of the frame kept by a block** whose writes are in `[lo, hi)` of the frame (region
`0`) or within their other regions, the bytes outside `[lo, hi)`. -/
theorem same_out [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).WF) {sizes : List Nat}
    (hsz : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).regions.map Prod.snd = sizes)
    {lo hi : Nat}
    (hw : (S.mem.all fun w ↦ (w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) ||
      (w.r != 0 && decide (w.off + w.n ≤ (sizes[w.r]?).getD 0))) = true)
    {o n : Nat} (ho : o + n ≤ 5488) (hd : o + n ≤ lo ∨ hi ≤ o) :
    NativeRustcVm.Layout.Same m.dmem m'.dmem (loc m0 o) n := by
  refine same_block hm hwf hsz ho ?_
  refine List.all_eq_true.mpr fun w hw' ↦ ?_
  have := List.all_eq_true.mp hw w hw'
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at this ⊢
  rcases this with ⟨⟨hr, h1⟩, h2⟩ | h'
  · exact .inl ⟨hr, by omega⟩
  · exact .inr h'

/-- **Bytes of the frame kept by a block**, as `same_out`. -/
theorem keep_out [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).WF) {sizes : List Nat}
    (hsz : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).regions.map Prod.snd = sizes)
    {lo hi : Nat}
    (hw : (S.mem.all fun w ↦ (w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) ||
      (w.r != 0 && decide (w.off + w.n ≤ (sizes[w.r]?).getD 0))) = true)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 5488) (hd : o + bs.length ≤ lo ∨ hi ≤ o)
    (h : NativeRustcVm.BytesAt m.dmem (loc m0 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (loc m0 o) bs :=
  NativeRustcVm.Layout.BytesAt.of_same h (same_out hm hwf hsz hw ho hd) le_rfl

/-- **A byte a block of the frame wrote** is the frame's. -/
theorem written_loc [Labels] {m0 m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hS : (S.mem.all fun w ↦ w.r == 0 && decide (0 ≤ w.off) && decide (w.off + w.n ≤ 5488)) = true)
    {q : BitVec 64} (hq : Written (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S q)
    (hF : 5488 ≤ m0.regs.SP.toNat) : InRange (loc m0 0) 5488 q := by
  have := written_in (r := 0) rfl hS hq
  have hb := base_toNat (m0 := m0) (F := 5488) hF
  have hl := m0.regs.SP.toNat_lt
  rw [show loc m0 0 = base m0 5488 from Bus.add_zero' _]
  rw [Sym.inRange_iff (by omega)]
  exact ⟨by omega, by omega⟩

/-- Two ranges of the frame apart. -/
theorem loc_apart {m0 : MachineData} (hS : StackOk m0 verifyBusBalanceStack) {o n o' n' : Nat}
    (h1 : o + n ≤ 5488) (h2 : o' + n' ≤ 5488) (hd : o + n ≤ o' ∨ o' + n' ≤ o) (q : BitVec 64)
    (hq : InRange (loc m0 o') n' q) : ¬InRange (loc m0 o) n q := by
  have hN := hS.2.1
  have := N_ge
  have hl := m0.regs.SP.toNat_lt
  rw [Sym.inRange_iff (by rw [loc_toNat hS (by omega)]; omega), loc_toNat hS (by omega)] at hq ⊢
  omega

end

/-! ## Labels -/

public section

/-- A block's leading label is the code's directive at the block's index. -/
theorem label_of_infix {F ds : List Directive} {j : Nat} {l : Label} (h : ds.IsInfixAt F j)
    (h0 : ds[0]? = some (.label l)) : F[j]? = some (.label l) := by
  obtain ⟨t, ht⟩ := h
  have hd : ds ≠ [] := fun he ↦ by rw [he] at h0; cases h0
  have : (F.drop j)[0]? = ds[0]? := by
    rw [← ht, List.getElem?_append_left (List.length_pos_of_ne_nil hd)]
  rw [List.getElem?_drop, Nat.add_zero, h0] at this
  exact this

end

/-! ## The exits -/

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- What `verify_bus_balance` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ VerifyBusBalancePost a s0 L m0 st.data

/-- **The epilogue** (`.LVerifyBusBalance_23`, `b51`): X0 the result's tag, the outputs its
values. -/
theorem exit_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m)
    (hx0 : m.regs.X0 = okWord ((verifyBusBalance L).run s0).isSome)
    (hok : ∀ res s', (verifyBusBalance L).run s0 = some (res, s') →
      TStateAt m.dmem m0.regs.X0.toBitVec a s' ∧ BusWAt m.dmem m0.regs.X4.toBitVec res ∧
        ClaimsWAt m.dmem m0.regs.X5.toBitVec res.claims) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b51Offset)⟩ := by
  have hS := pre_stack h
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then (b51_in_code.trans hp.1 (by simp [b51])) run_b51 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm' hwf (by decide)
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have e0 : st.data.regs.X0 = m.regs.X0 := reg_of hm' (r := .X0) (r' := .X0) rfl
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], by rw [e0]; exact hx0,
    fun res s' he ↦ by rw [hd]; exact hok res s' he, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ by
    rcases hq with hq | hq | hq | hq
    · exact .inr (.inr (.inr hq))
    · exact .inl hq
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl hq))

/-- **A failed phase** (`.LVerifyBusBalance_22`, `b50`): X0 = `0`. -/
theorem fail_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m)
    (hr : (verifyBusBalance L).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b50Offset)⟩ := by
  refine Fr.runBlock (pre_stack h) N_ge rfl hfr (b50_in_code.trans hp.1 (by simp [b50])) run_b50
    rfl rfl (by decide) (by decide) fun st hfr' _ hm hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc (exit_spec hp h hfr' ?_ fun res s' he ↦ by rw [hr] at he; cases he)
  rw [hr]
  exact UInt64.toBitVec_inj.mp (reg_lit hm (r := .X0) (n := 0) rfl)

end

end NativeRustcVmArm.Bus.VerifyBusBalance
