module

public import NativeRustcVmArm.Sumcheck.RoundPoly.Exec
public import NativeRustcVmArm.Sumcheck.Ctx
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVm.Transcript.Update

/-!
# `sumcheck_round_poly`'s frame and its exit

The 112-byte frame below the entry's SP: `read_scalar`'s `Option<EW>` at `8`, the saved X30, X27,
…, X19 at `32` (`slotWords`). `RFrame m0 m`: at the frame (`At`), the slots, X28 and X29 the
entry's, memory changed only in the message, the `TState` and the stack (`Chg`). From it at `.L9`,
`b19` returns X0 (`exit_spec`), at `.L8` with X0 = `0` (`fail_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The saved registers' words, from offset 32 of the frame. -/
def slotWords (m0 : MachineData) : List UInt64 :=
  [m0.regs.X30, m0.regs.getXReg .X27, m0.regs.getXReg .X26, m0.regs.getXReg .X25,
    m0.regs.getXReg .X24, m0.regs.getXReg .X23, m0.regs.getXReg .X22, m0.regs.getXReg .X21,
    m0.regs.getXReg .X20, m0.regs.getXReg .X19]

/-- The frame. -/
abbrev fr (m0 : MachineData) : BitVec 64 := frAt m0 112

/-- The `TState`, the message: X0 and X5 at the entry. -/
abbrev tAt (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
abbrev msgAt (m0 : MachineData) : BitVec 64 := m0.regs.X5.toBitVec

/-- What `sumcheck_round_poly` may change: the message, the `TState`, its stack. -/
def Chg (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (msgAt m0) (16 * maxCount) p ∨ InRange (tAt m0) tstateBytes p ∨
    InRange (stackBelow m0 roundPolyStack) roundPolyStack p

/-- **The frame.** -/
structure RFrame [Labels] (m0 m : MachineData) : Prop where
  at_ : At m0 112 m
  slots : NativeRustcVm.WordsAt m.dmem (fr m0 + BitVec.ofNat 64 32) (slotWords m0)
  x28 : m.regs.getXReg .X28 = m0.regs.getXReg .X28
  x29 : m.regs.getXReg .X29 = m0.regs.getXReg .X29
  same : SameOutside m0.dmem m.dmem (Chg m0)

end

public section

variable [Host] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData}

omit [Host] in
theorem roundPolyStack_eq : roundPolyStack = 720 := by decide

/-- The context of `sumcheck_round_poly`. -/
theorem ctx_of (h : RoundPolyPre a s e m0) : Ctx m0 (tAt m0) a roundPolyStack 112 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, by rw [roundPolyStack_eq]; omega, by decide⟩

/-- The message as an output. -/
theorem msgOk (h : RoundPolyPre a s e m0) :
    OutOk m0 (tAt m0) a (msgAt m0) (16 * maxCount) roundPolyStack :=
  h.2.2.2.2.2.2.2.2.2

/-- The round constants are apart from the changes. -/
theorem not_rc (h : RoundPolyPre a s e m0) {p : BitVec 64} (hp : Chg m0 p) :
    ¬ InRange rcAddr 192 p := by
  have c := ctx_of h
  rcases hp with hp | hp | hp
  · exact NativeRustcVm.Apart.not_inRange (msgOk h).2.2.2.2.2 (msgOk h).2.1 c.rc.2.1 hp
  · exact c.not_rc_tstate hp
  · exact c.not_rc_stack hp

/-- The `TState` and its area are apart from the message and the stack. -/
theorem chg_apart (h : RoundPolyPre a s e m0) {p : BitVec 64}
    (hp : InRange (msgAt m0) (16 * maxCount) p ∨
      InRange (stackBelow m0 roundPolyStack) roundPolyStack p) :
    ¬ InRange (tAt m0) tstateBytes p ∧ ¬ InRange a.words (8 * a.len) p := by
  have c := ctx_of h
  have ho := msgOk h
  have hsw : NoWrap (stackBelow m0 roundPolyStack) roundPolyStack := by
    unfold NoWrap; rw [c.stk]; have := c.spN; have := Ctx.sp_lt m0; omega
  rcases hp with hp | hp
  · exact ⟨NativeRustcVm.Apart.not_inRange ho.2.2.1 ho.2.1 c.fp.1.2 hp,
      NativeRustcVm.Apart.not_inRange ho.2.2.2.1 ho.2.1 c.fp.2.1.2 hp⟩
  · exact ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm hsw c.fp.1.2 hp,
      NativeRustcVm.Apart.not_inRange c.tok.2.1.symm hsw c.fp.2.1.2 hp⟩

theorem slot_word {m : MachineData} (hf : RFrame m0 m) (i : Nat) (hi : i < 10) :
    NativeRustcVm.WordAt m.dmem (fr m0 + BitVec.ofNat 64 (32 + 8 * i)) ((slotWords m0)[i]'(by
      simp [slotWords]; omega)) := by
  have := hf.slots.getElem (i := i) (by simp [slotWords]; omega)
  rwa [NativeRustcVm.addr_add_add] at this

/-- The frame's bytes are in the stack. -/
theorem chg_frame (hpre : RoundPolyPre a s e m0) {p : BitVec 64} (hp : InRange (fr m0) 112 p) :
    Chg m0 p := Or.inr (Or.inr ((ctx_of hpre).inRange_frame hp))

/-- The saved registers' slots are in the frame. -/
theorem slots_in_fr (hpre : RoundPolyPre a s e m0) {p : BitVec 64}
    (hp : InRange (fr m0 + BitVec.ofNat 64 32) 80 p) : InRange (fr m0) 112 p := by
  have c := ctx_of hpre
  have hl := Ctx.sp_lt m0; have := c.spN; have := c.le
  rw [Sym.inRange_iff (by rw [c.frame_toNat (by omega)]; omega), c.frame_toNat (by omega)] at hp
  rw [Sym.inRange_iff c.noWrap_fr, c.fr]
  omega

/-- What a block or callee changes from the frame: its outputs (apart from the saved registers'
slots) and its stack; SP, X28, X29 and the mapped bytes kept. -/
theorem RFrame.after_slots (hpre : RoundPolyPre a s e m0) {m m' : MachineData} (hf : RFrame m0 m)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ p, R p → Chg m0 p ∧ ¬ InRange (fr m0 + BitVec.ofNat 64 32) 80 p)
    (hs : SameOutside m.dmem m'.dmem (fun p ↦ R p ∨ InRange (stackBelow m Nc) Nc p))
    (hsp : m'.regs.SP = m.regs.SP) (hk : Kept m.dmem m'.dmem)
    (h28 : m'.regs.getXReg .X28 = m.regs.getXReg .X28)
    (h29 : m'.regs.getXReg .X29 = m.regs.getXReg .X29) : RFrame m0 m' := by
  have c := ctx_of hpre
  have hst : ∀ p, InRange (stackBelow m Nc) Nc p →
      Chg m0 p ∧ ¬ InRange (fr m0 + BitVec.ofNat 64 32) 80 p := by
    intro p hp
    refine ⟨Or.inr (Or.inr (c.inRange_stack hf.at_ hle hp)), fun hin ↦ ?_⟩
    have := c.apart_frame (o := 0) (n := 112) (Nc := Nc) hf.at_ hle (by omega)
    rw [NativeRustcVm.addr_add_zero] at this
    exact NativeRustcVm.Apart.not_inRange this c.noWrap_fr (by
      unfold NativeRustcVm.NoWrap; have hs := c.spN' hf.at_; have := c.spN; have := Ctx.sp_lt m0
      rw [toNat_stackBelow (by rw [hs]; omega)]; omega) (slots_in_fr hpre hin) hp
  have hall : ∀ p, (R p ∨ InRange (stackBelow m Nc) Nc p) →
      Chg m0 p ∧ ¬ InRange (fr m0 + BitVec.ofNat 64 32) 80 p :=
    fun p hp ↦ hp.elim (hR p) (hst p)
  have hsame : SameOutside m0.dmem m'.dmem (Chg m0) := fun p hp ↦ by
    rw [hs p fun h ↦ hp (hall p h).1]; exact hf.same p hp
  refine ⟨c.at_of (fun p hp ↦ not_rc hpre hp) hsame (fun p h ↦ hk p (hf.at_.kept p h)) ?_,
    NativeRustcVm.BytesAt.of_sameOutside hf.slots hs fun i hi hin ↦ (hall _ hin).2 ?_,
    h28.trans hf.x28, h29.trans hf.x29, hsame⟩
  · show m'.regs.SP.toBitVec = _; rw [hsp]; exact hf.at_.sp
  · rw [NativeRustcVm.length_wordsBytes] at hi
    simp only [slotWords, List.length_cons, List.length_nil] at hi
    exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- What a block or callee changes from the frame: its outputs and its stack, apart from the
frame; SP, X28, X29 and the mapped bytes kept. -/
theorem RFrame.after_write (hpre : RoundPolyPre a s e m0) {m m' : MachineData} (hf : RFrame m0 m)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ p, R p → Chg m0 p ∧ ¬ InRange (fr m0) 112 p)
    (hs : SameOutside m.dmem m'.dmem (fun p ↦ R p ∨ InRange (stackBelow m Nc) Nc p))
    (hsp : m'.regs.SP = m.regs.SP) (hk : Kept m.dmem m'.dmem)
    (h28 : m'.regs.getXReg .X28 = m.regs.getXReg .X28)
    (h29 : m'.regs.getXReg .X29 = m.regs.getXReg .X29) : RFrame m0 m' :=
  hf.after_slots hpre hle (fun p hp ↦ ⟨(hR p hp).1, fun h ↦ (hR p hp).2 (slots_in_fr hpre h)⟩)
    hs hsp hk h28 h29

/-- What a callee changes from the frame: its outputs and its stack, apart from the frame. -/
theorem RFrame.after_call (hpre : RoundPolyPre a s e m0) {m m' : MachineData} (hf : RFrame m0 m)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ p, R p → Chg m0 p ∧ ¬ InRange (fr m0) 112 p)
    (hs : SameOutside m.dmem m'.dmem (fun p ↦ R p ∨ InRange (stackBelow m Nc) Nc p))
    (hsv : Saved m m') : RFrame m0 m' :=
  hf.after_write hpre hle hR hs hsv.2.1 hsv.2.2 (hsv.1 .X28 rfl) (hsv.1 .X29 rfl)

/-- The body's environment: the frame and the message. -/
@[expose] def envB (m0 m : MachineData) : Env := Env.ofMachine m [(fr m0, 112), (msgAt m0, 80)]

theorem wf_envB (hpre : RoundPolyPre a s e m0) {m : MachineData} (hf : RFrame m0 m) :
    (envB m0 m).WF := by
  have c := ctx_of hpre
  have ho := msgOk hpre
  have hmc : maxCount = 5 := rfl
  rw [hmc] at ho
  refine Env.wf_of ⟨⟨c.mapped_fr hf.at_, c.noWrap_fr⟩,
    ⟨fun i hi ↦ hf.at_.kept _ (ho.1 i (by omega)), NativeRustcVm.NoWrap.mono ho.2.1 (by omega)⟩,
    trivial⟩ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  simp only [List.mem_singleton, forall_eq]
  have := c.apart_of_stack (o := 0) (k := 112) (by omega) ho.2.2.2.2.1
  rw [NativeRustcVm.addr_add_zero] at this
  exact NativeRustcVm.Apart.mono this (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by omega)

theorem match_bodyS (hpre : RoundPolyPre a s e m0) {m : MachineData} (hf : RFrame m0 m)
    (hx19 : m.regs.getXReg .X19 = m0.regs.X5) : Match (envB m0 m) bodyS m := by
  have c := ctx_of hpre
  have hal : (frAt m0 112).toNat % 16 = 0 := by
    rw [c.fr]; have := c.stack.1; have := c.spN; have := c.le; omega
  refine match_ofMachine ⟨rfl, fun _ ↦ hal, rfl, by simp, trivial⟩ (by simp [Sym.eval, hf.at_.sp])
    ⟨?_, trivial⟩ trivial trivial trivial
  show (m.regs.getXReg .X19).toBitVec = (envB m0 m).base 1 + BitVec.ofInt 64 0
  rw [hx19]
  simp [envB]

/-- **Through a block without writes** from `m` (`envB`): the frame kept, the memory the same. -/
theorem RFrame.of_block (hpre : RoundPolyPre a s e m0) {m m' : MachineData} (hf : RFrame m0 m)
    {S : SState} (hm : Match (envB m0 m) S m') (hmem : S.mem = []) (hsp : S.sp = .ptr 0 0)
    (h28 : S.reg .X28 = some (.reg .X28)) (h29 : S.reg .X29 = some (.reg .X29)) :
    RFrame m0 m' ∧ m'.dmem = m.dmem := by
  have hdm : m'.dmem = m.dmem := Match.dmem_eq hm (wf_envB hpre hf) hmem
  refine ⟨⟨⟨?_, hdm ▸ hf.at_.kept, fun p hp ↦ by rw [hdm]; exact hf.at_.rc p hp⟩,
    hdm ▸ hf.slots, (UInt64.toBitVec_inj.mp (hm.regs _ _ h28)).trans hf.x28,
    (UInt64.toBitVec_inj.mp (hm.regs _ _ h29)).trans hf.x29, hdm ▸ hf.same⟩, hdm⟩
  rw [hm.sp, hsp]
  simp [Sym.eval, envB, Env.base, Env.ofMachine]

/-- A register a block keeps: the one before it. -/
theorem reg_of_match {m m' : MachineData} {S : SState} (hm : Match (envB m0 m) S m') {r : XReg}
    (h : S.reg r = some (.reg r)) : m'.regs.getXReg r = m.regs.getXReg r :=
  UInt64.toBitVec_inj.mp (hm.regs _ _ h)

/-- A register a block copies from another. -/
theorem reg_of_match' {m m' : MachineData} {S : SState} (hm : Match (envB m0 m) S m') {r r' : XReg}
    (h : S.reg r = some (.reg r')) : m'.regs.getXReg r = m.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs _ _ h)

/-- A register a block sets to the message plus `o`. -/
theorem reg_msg {m m' : MachineData} {S : SState} (hm : Match (envB m0 m) S m') {r : XReg} {o : Nat}
    (h : S.reg r = some (.ptr 1 o)) :
    (m'.regs.getXReg r).toBitVec = msgAt m0 + BitVec.ofNat 64 o := by
  rw [hm.regs _ _ h]
  simp [Sym.eval, envB, Env.base, Env.ofMachine]

/-- A register a block sets to the frame plus `o`. -/
theorem reg_fr {m m' : MachineData} {S : SState} (hm : Match (envB m0 m) S m') {r : XReg} {o : Nat}
    (h : S.reg r = some (.ptr 0 o)) :
    (m'.regs.getXReg r).toBitVec = fr m0 + BitVec.ofNat 64 o := by
  rw [hm.regs _ _ h]
  simp [Sym.eval, envB, Env.base, Env.ofMachine]

/-- **Elements of the message kept** where the memory changed apart from it. -/
theorem msg_keep (hpre : RoundPolyPre a s e m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hR : ∀ p, R p → ¬ InRange (msgAt m0) (16 * maxCount) p)
    {o : Nat} {xs : List EW} (hle : o + 16 * xs.length ≤ 16 * maxCount)
    (h : NativeRustcVm.EWsAt d (msgAt m0 + BitVec.ofNat 64 o) xs) :
    NativeRustcVm.EWsAt d' (msgAt m0 + BitVec.ofNat 64 o) xs := by
  have ho := (msgOk hpre).2.1
  unfold NoWrap at ho
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hR' ↦ hR _ hR' ?_
  rw [NativeRustcVm.length_ewsBytes] at hi
  rw [NativeRustcVm.addr_add_add]
  exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- **The `TState` kept** where the memory changed only in the message and the stack. -/
theorem tstate_keep (hpre : RoundPolyPre a s e m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hk : Kept d d')
    (hR : ∀ p, R p → InRange (msgAt m0) (16 * maxCount) p ∨
      InRange (stackBelow m0 roundPolyStack) roundPolyStack p)
    {s' : TState} (h : TStateAt d (tAt m0) a s') : TStateAt d' (tAt m0) a s' :=
  h.frame (fun p hp ↦ hk p hp) (fun p hp ↦ chg_apart hpre (hR p hp)) hs

theorem noWrap_stack (hpre : RoundPolyPre a s e m0) :
    NoWrap (stackBelow m0 roundPolyStack) roundPolyStack := by
  have c := ctx_of hpre
  unfold NoWrap; rw [c.stk]; have := c.spN; have := Ctx.sp_lt m0; omega

/-- A callee's stack is in the function's. -/
theorem callee_stack (hpre : RoundPolyPre a s e m0) {m : MachineData} (hf : RFrame m0 m)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {p : BitVec 64}
    (hp : InRange (stackBelow m Nc) Nc p) : InRange (stackBelow m0 roundPolyStack) roundPolyStack p :=
  (ctx_of hpre).inRange_stack hf.at_ hle hp

theorem t_not_msg (hpre : RoundPolyPre a s e m0) {p : BitVec 64}
    (hp : InRange (tAt m0) tstateBytes p) : ¬ InRange (msgAt m0) (16 * maxCount) p :=
  NativeRustcVm.Apart.not_inRange (msgOk hpre).2.2.1.symm (ctx_of hpre).fp.1.2 (msgOk hpre).2.1 hp

theorem stack_not_msg (hpre : RoundPolyPre a s e m0) {p : BitVec 64}
    (hp : InRange (stackBelow m0 roundPolyStack) roundPolyStack p) :
    ¬ InRange (msgAt m0) (16 * maxCount) p :=
  NativeRustcVm.Apart.not_inRange (msgOk hpre).2.2.2.2.1.symm (noWrap_stack hpre) (msgOk hpre).2.1 hp

theorem t_not_fr (hpre : RoundPolyPre a s e m0) {p : BitVec 64}
    (hp : InRange (tAt m0) tstateBytes p) : ¬ InRange (fr m0) 112 p := fun hfr ↦
  NativeRustcVm.Apart.not_inRange (ctx_of hpre).tok.1 (ctx_of hpre).fp.1.2 (noWrap_stack hpre) hp
    ((ctx_of hpre).inRange_frame hfr)

theorem msg_not_fr (hpre : RoundPolyPre a s e m0) {p : BitVec 64}
    (hp : InRange (msgAt m0) (16 * maxCount) p) : ¬ InRange (fr m0) 112 p := fun hfr ↦
  stack_not_msg hpre ((ctx_of hpre).inRange_frame hfr) hp

/-- **A part of the message as a callee's output.** -/
theorem msgOut (hpre : RoundPolyPre a s e m0) {m : MachineData} (hf : RFrame m0 m) {Nc : Nat}
    (hle : 112 + Nc ≤ roundPolyStack) {o n : Nat} (ho80 : o < 16 * maxCount)
    (hon : o + n ≤ 16 * maxCount) :
    OutOk m (tAt m0) a (msgAt m0 + BitVec.ofNat 64 o) n Nc := by
  have ho := msgOk hpre
  have hnw := ho.2.1
  unfold NoWrap at hnw
  have hmc : maxCount = 5 := rfl
  have hoff : (msgAt m0 + BitVec.ofNat 64 o).toNat = (msgAt m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have m1 : ∀ {x : BitVec 64} {nx : Nat}, Apart (msgAt m0) (16 * maxCount) x nx →
      Apart (msgAt m0 + BitVec.ofNat 64 o) n x nx := fun h ↦
    NativeRustcVm.Apart.mono h (by rw [hoff]; omega) (by rw [hoff]; omega) (Nat.le_refl _)
      (Nat.le_refl _)
  exact ⟨NativeRustcVm.Mapped.sub (fun i hi ↦ hf.at_.kept _ (ho.1 i hi)) hon,
    NativeRustcVm.NoWrap.sub ho.2.1 hon, m1 ho.2.2.1, m1 ho.2.2.2.1,
    (ctx_of hpre).apart hf.at_ hle (m1 ho.2.2.2.2.1), m1 ho.2.2.2.2.2⟩

/-- A byte of the message from `o` on, as numbers. -/
theorem msg_bounds (hpre : RoundPolyPre a s e m0) {o n : Nat} (ho80 : o < 16 * maxCount)
    (hon : o + n ≤ 16 * maxCount) {p : BitVec 64}
    (hp : InRange (msgAt m0 + BitVec.ofNat 64 o) n p) :
    InRange (msgAt m0) (16 * maxCount) p ∧ (msgAt m0).toNat + o ≤ p.toNat ∧
      p.toNat < (msgAt m0).toNat + o + n := by
  have hnw := (msgOk hpre).2.1
  unfold NoWrap at hnw
  have hmc : maxCount = 5 := rfl
  have hoff : (msgAt m0 + BitVec.ofNat 64 o).toNat = (msgAt m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [hoff]; omega), hoff] at hp
  rw [Sym.inRange_iff hnw]
  omega

variable {k : Nat}

/-- **The exit**: X0 kept, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (hpre : RoundPolyPre a s e m0) {m : MachineData}
    (hf : RFrame m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ st.data.regs.X0 = m.regs.X0 ∧ st.data.dmem = m.dmem ∧
        Saved m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset)⟩ := by
  have c := ctx_of hpre
  have hk : b19.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) := b19_in_code.trans hp.1 (by simp [b19])
  let env := Env.ofMachine m [(fr m0, 112)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨c.mapped_fr hf.at_, c.noWrap_fr⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [c.fr]; have := Ctx.sp_lt m0; have := c.stack.1; omega,
      trivial⟩ (by simp [Sym.eval, hf.at_.sp]) trivial trivial trivial trivial
  have hb0 : env.base 0 = fr m0 := rfl
  refine exec_then hk run_b19 hwf hm fun st hm' hpc ↦ ?_
  have hmA : Match env (after b19 exitS) st.data := by rw [after_eq run_b19]; exact hm'
  have hslot : ∀ (r : XReg) (i : Nat) (hi : i < 10),
      (after b19 exitS).reg r = some (.load 0 (32 + 8 * i) 8) →
      st.data.regs.getXReg r = (slotWords m0)[i]'(by simp [slotWords]; omega) :=
    fun r i hi hr ↦ UInt64.toBitVec_inj.mp ((hmA.regs r _ hr).trans
      (load_word (by rw [hb0]; exact slot_word hf i hi)))
  have hsame : ∀ r, (after b19 exitS).reg r = some (.reg r) → st.data.regs.getXReg r =
      m.regs.getXReg r := fun r hr ↦ UInt64.toBitVec_inj.mp ((hmA.regs r _ hr).trans rfl)
  have hdm : st.data.dmem = m.dmem := Match.dmem_eq hmA hwf (by rw [after_eq run_b19])
  refine Eventually.done _ ⟨?_, hsame .X0 (by rw [after_eq run_b19]; rfl), hdm, ?_, ?_, ?_⟩
  · rw [hpc]
    simp only [retOf]
    rw [show st.data.regs.X30 = st.data.regs.getXReg .X30 from rfl,
      hslot .X30 0 (by decide) (by rw [after_eq run_b19]; rfl)]
    rfl
  · intro r hr
    cases r <;> simp [calleeSaved] at hr
    · exact hslot .X19 9 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X20 8 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X21 7 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X22 6 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X23 5 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X24 4 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X25 3 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X26 2 (by decide) (by rw [after_eq run_b19]; rfl)
    · exact hslot .X27 1 (by decide) (by rw [after_eq run_b19]; rfl)
    · rw [hsame .X28 (by rw [after_eq run_b19]; rfl)]; exact hf.x28
    · rw [hsame .X29 (by rw [after_eq run_b19]; rfl)]; exact hf.x29
  · apply UInt64.toBitVec_inj.mp
    rw [hmA.sp, after_eq run_b19]
    simp only [Sym.eval, hb0, fr, frAt]
    simp
  · rw [hdm]; exact hf.at_.kept

/-- **A failure**: at `.L8`, X0 = `0`, then the exit. -/
theorem fail_spec (hp : Placed code k) (hpre : RoundPolyPre a s e m0) {m : MachineData}
    (hf : RFrame m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ st.data.regs.X0 = 0 ∧ st.data.dmem = m.dmem ∧
        Saved m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset)⟩ := by
  have c := ctx_of hpre
  have hk : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) := b18_in_code.trans hp.1 (by simp [b18])
  let env := Env.ofMachine m [(fr m0, 112)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨c.mapped_fr hf.at_, c.noWrap_fr⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [c.fr]; have := Ctx.sp_lt m0; have := c.stack.1; omega,
      trivial⟩ (by simp [Sym.eval, hf.at_.sp]) trivial trivial trivial trivial
  refine exec_then hk run_b18 hwf hm fun st hm' hpc ↦ ?_
  have hm'' : Match env (after b18 exitS) st.data := by rw [after_eq run_b18]; exact hm'
  have hdm : st.data.dmem = m.dmem := Match.dmem_eq hm'' hwf (by rw [after_eq run_b18])
  have hf' : RFrame m0 st.data := by
    refine ⟨⟨?_, hdm ▸ hf.at_.kept, fun p hp ↦ by rw [hdm]; exact hf.at_.rc p hp⟩,
      hdm ▸ hf.slots, ?_, ?_, hdm ▸ hf.same⟩
    · rw [hm'.sp, ← hf.at_.sp, hm.sp]; rfl
    · exact (Match.reg_eq hm hm' rfl rfl).trans hf.x28
    · exact (Match.reg_eq hm hm' rfl rfl).trans hf.x29
  have hx0 : st.data.regs.X0 = 0 := UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc
  subst hpc
  refine Eventually.mono (exit_spec hp hpre hf') fun st ⟨h1, h2, h3, h4⟩ ↦
    ⟨h1, h2.trans hx0, h3.trans hdm, h4⟩

end

end NativeRustcVmArm.Sumcheck.RoundPoly
