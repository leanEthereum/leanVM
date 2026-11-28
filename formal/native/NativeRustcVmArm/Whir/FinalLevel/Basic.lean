module

public import NativeRustcVmArm.Whir.FinalLevel.Exec
public import NativeRustcVmArm.Whir.TFrame
public import NativeRustcVmArm.Whir.State
public import NativeRustcVmArm.Whir.WhirLevels.Basis
public import NativeRustcVmArm.Whir.FoldRounds.Round

/-!
# `final_level`: its frame, its context

From the entry `m0` (the `TState` X0, the index X1, the level X2, `μ` X3, `laneFolds` X4, the
basis X5, the `WhirW` X6): the 2672-byte frame (`FFr`, X19 to X30 saved at 2576 to 2671), the
outputs (`outs`: the queries' buffer of the `WhirW`, the `TState`), the entry's facts (`Ctx`), the
call context (`Ctx.tctx`), the inputs kept in the frame's states (`Ctx.same`, `Ctx.level_at`,
`Ctx.basis_at`, `Ctx.state_at`, `Ctx.rounds_at`), the frame's environments.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(2576, .X29), (2584, .X30), (2592, .X28), (2600, .X27), (2608, .X26), (2616, .X25),
    (2624, .X24), (2632, .X23), (2640, .X22), (2648, .X21), (2656, .X20), (2664, .X19)]

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The level. -/
abbrev lvA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
/-- The basis. -/
abbrev bA (m0 : MachineData) : BitVec 64 := m0.regs.X5.toBitVec
/-- The `WhirW`. -/
abbrev pA (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec
/-- The `WhirW`'s queries' buffer. -/
abbrev qA (m0 : MachineData) : BitVec 64 := off (pA m0) queriesOff
/-- `μ`. -/
abbrev mu (m0 : MachineData) : Nat := m0.regs.X3.toNat

/-- The outputs: the queries' buffer, the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (qA m0) queryBufBytes q ∨ InRange (tA m0) tstateBytes q

/-- The frame. -/
abbrev FFr (m0 st : MachineData) : Prop := Fr m0 2672 finalLevelStack slots [] (outs m0) st

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 2672 + BitVec.ofNat 64 o

/-- The frame's environment, the regions `rs` after it. -/
abbrev fenv (m0 st : MachineData) (rs : List (BitVec 64 × Nat)) : Env :=
  Env.ofMachine st ((base m0 2672, 2672) :: rs)

section
variable [Labels]

/-- **The entry's facts**: `final_level`'s precondition, by name. -/
structure Ctx (a : DecArea) (s0 : TState) (level : Whir.Level) (ba : BasisAddrs) (b : BasisW)
    (w : WhirStateW) (rounds : Array FoldRoundW) (m0 : MachineData) : Prop where
  stack : StackOk m0 finalLevelStack
  rc : RcAt m0 finalLevelStack
  ro : RodataAt m0 finalLevelStack
  tok : TStateOk m0 (tA m0) a finalLevelStack
  tro : NativeRustcVm.RodataApart rodataAddr (tA m0) tstateBytes
  ts0 : TStateAt m0.dmem (tA m0) a s0
  wa : WhirAt m0.dmem (pA m0) w rounds
  lv : LevelAt m0.dmem (lvA m0) level
  bw : BasisWAt m0.dmem (bA m0) ba b
  mu64 : mu m0 < 64
  fold : 2 ^ mu m0 + level.fold ≤ laneCap
  alphas : w.alphas.size + mu m0 ≤ stackCap
  rate : level.logInvRate < 64
  queries : level.queries ≤ queryCap
  pout : WhirOut m0 (tA m0) a (pA m0) whirBytes finalLevelStack
  lin : WhirIn m0 (lvA m0) levelBytes finalLevelStack
  lp : Apart (lvA m0) levelBytes (pA m0) whirBytes
  lt : Apart (lvA m0) levelBytes (tA m0) tstateBytes
  bp : BasisIn m0 (bA m0) ba finalLevelStack (pA m0) whirBytes
  bt : BasisIn m0 (bA m0) ba finalLevelStack (tA m0) tstateBytes
  bap : BasisApart (bA m0) ba

/-- `final_level`'s postcondition, reached. -/
abbrev Goal (a : DecArea) (s0 : TState) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ FinalLevelPost a s0 level b w rounds m0 st.data

end

end

public section

theorem stack_eq : finalLevelStack = 5856 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 2672 := by decide

theorem slots_ge : ∀ p ∈ slots, 2576 ≤ p.1 := by decide

/-- The frame's bytes are in the entry's stack. -/
theorem frame_sub {m0 : MachineData} {F N : Nat} (hN : N ≤ m0.regs.SP.toNat) (hF : F ≤ N)
    {q : BitVec 64} (hq : InRange (base m0 F) F q) : InRange (stackBelow m0 N) N q := by
  have e1 := base_toNat (m0 := m0) (F := F) (by omega)
  have e2 := base_toNat (m0 := m0) (F := N) hN
  exact NativeRustcVm.InRange.mono hq (base_noWrap (by omega)) (base_noWrap hN)
    (by show (base m0 N).toNat ≤ _; omega) (by show _ ≤ (base m0 N).toNat + _; omega)

/-- The frame's byte `o`, as a number. -/
theorem loc_toNat {m0 : MachineData} (hN : 2672 ≤ m0.regs.SP.toNat) {o : Nat} (ho : o ≤ 2672) :
    (loc m0 o).toNat = m0.regs.SP.toNat - 2672 + o := by
  have := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.toNat_add_ofNat (by rw [base_toNat hN]; omega), base_toNat hN]

section
variable [Labels] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

theorem Ctx.of_pre (h : FinalLevelPre a s0 level ba b w rounds m0) :
    Ctx a s0 level ba b w rounds m0 := by
  obtain ⟨⟨hS, hrc, hro, htok, htro⟩, hts, hwa, hlv, hbw, hmu, hfo, hal, hra, hq, hpo, hlin, hlp,
    hlt, hbp, hbt, hbap⟩ := h
  exact ⟨hS, hrc, hro, htok, htro, hts, hwa, hlv, hbw, hmu, hfo, hal, hra, hq, hpo, hlin, hlp, hlt,
    hbp, hbt, hbap⟩

namespace Ctx

variable (c : Ctx a s0 level ba b w rounds m0)
include c

theorem hN : finalLevelStack ≤ m0.regs.SP.toNat := c.stack.2.1

theorem hN' : 5856 ≤ m0.regs.SP.toNat := by have := c.hN; rw [stack_eq] at this; exact this

theorem pnw : NoWrap (pA m0) whirBytes := c.pout.1.2.1

theorem qnw : NoWrap (qA m0) queryBufBytes :=
  NativeRustcVm.NoWrap.sub c.pnw (by decide)

theorem tnw : NoWrap (tA m0) tstateBytes := c.ts0.footprint.1.2

theorem qA_toNat : (qA m0).toNat = (pA m0).toNat + queriesOff := by
  have := c.pnw; unfold NoWrap whirBytes at this
  exact toNat_off (by unfold queriesOff; omega)

/-- A range apart from the `WhirW` is apart from its queries' buffer. -/
theorem apart_q {x : BitVec 64} {n : Nat} (h : Apart x n (pA m0) whirBytes) :
    Apart x n (qA m0) queryBufBytes := by
  have := c.qA_toNat
  unfold Apart at h ⊢; rw [this]; unfold whirBytes queriesOff queryBufBytes queryCap at *; omega

/-- The queries' buffer is in the `WhirW`. -/
theorem q_sub {q : BitVec 64} (hq : InRange (qA m0) queryBufBytes q) :
    InRange (pA m0) whirBytes q :=
  NativeRustcVm.InRange.of_sub hq c.pnw (by decide)

theorem outs_not_frame {F : Nat} (hF : F ≤ finalLevelStack) {q : BitVec 64} (hq : outs m0 q) :
    ¬InRange (base m0 F) F q := fun hf ↦ by
  have hs := frame_sub c.hN hF hf
  have hnN := base_noWrap (m0 := m0) (F := finalLevelStack) c.hN
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange c.pout.1.2.2.2.2.1 c.pnw hnN (c.q_sub hq) hs
  · exact NativeRustcVm.Apart.not_inRange c.tok.1 c.tnw hnN hq hs

/-- **The context of the calls.** -/
theorem tctx : TCtx m0 2672 finalLevelStack (tA m0) a (outs m0) := by
  have hfp := c.ts0.footprint
  have hrc := c.rc
  have hpo := c.pout.1
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  refine ⟨c.stack, hrc, c.tok, hfp, by rw [stack_eq]; decide, rfl, fun q hq hr ↦ ?_,
    fun q hq hd ↦ ?_, fun q hq ↦ Or.inr hq,
    fun q hq ↦ c.outs_not_frame (by rw [stack_eq]; decide) hq⟩
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.2 c.pnw hrc.2.1 (c.q_sub hq) hr
    · exact NativeRustcVm.Apart.not_inRange c.tok.2.2 c.tnw hrc.2.1 hq hr
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 c.pnw hnd (c.q_sub hq) hd
    · exact NativeRustcVm.Apart.not_inRange hfp.2.2 c.tnw hnd hq hd

/-- Bytes apart from the stack, the queries' buffer and the `TState` stay the same in the frame's
states. -/
theorem same {st : MachineData} (hf : FFr m0 st) {x : BitVec 64} {n : Nat} (hnw : NoWrap x n)
    (hs : Apart x n (stackBelow m0 finalLevelStack) finalLevelStack)
    (hq : Apart x n (qA m0) queryBufBytes) (ht : Apart x n (tA m0) tstateBytes) :
    NativeRustcVm.Layout.Same m0.dmem st.dmem x n := by
  refine NativeRustcVm.Layout.Same.of_sameOutside hf.same fun j hj hr ↦ ?_
  rcases hr with hr | hr | hr
  · exact NativeRustcVm.Apart.not_inRange_add hs hnw (base_noWrap c.hN) hj hr
  · exact NativeRustcVm.Apart.not_inRange_add hq hnw c.qnw hj hr
  · exact NativeRustcVm.Apart.not_inRange_add ht hnw c.tnw hj hr

/-- A part `[o, o + n)` of the `WhirW` before its queries' buffer stays the same. -/
theorem same_p {st : MachineData} (hf : FFr m0 st) {o n : Nat} (hon : o + n ≤ queriesOff) :
    NativeRustcVm.Layout.Same m0.dmem st.dmem (off (pA m0) o) n := by
  have hpn := c.pnw
  have hp : (off (pA m0) o).toNat = (pA m0).toNat + o :=
    toNat_off (by unfold NoWrap whirBytes at hpn; unfold queriesOff at hon; omega)
  have hq := c.qA_toNat
  have hps := c.pout.1.2.2.2.2.1
  have hpt := c.pout.1.2.2.1
  refine c.same hf ?_ ?_ ?_ ?_
  · unfold NoWrap at hpn ⊢; rw [hp]; unfold whirBytes queriesOff at *; omega
  · unfold Apart at hps ⊢; rw [hp]; unfold whirBytes queriesOff at *; omega
  · unfold Apart; rw [hp, hq]; omega
  · unfold Apart at hpt ⊢; rw [hp]; unfold whirBytes queriesOff at *; omega

/-- The level in the frame's states. -/
theorem level_at {st : MachineData} (hf : FFr m0 st) : LevelAt st.dmem (lvA m0) level := by
  have hs := c.same hf c.lin.1.2 c.lin.2 (c.apart_q c.lp) c.lt
  obtain ⟨h1, h2, h3, h4⟩ := c.lv
  exact ⟨h1, h2, h3, NativeRustcVm.Tables.WordsAt.of_same h4 hs (by simp [levelBytes])⟩

/-- The basis in the frame's states. -/
theorem basis_at {st : MachineData} (hf : FFr m0 st) : BasisWAt st.dmem (bA m0) ba b :=
  WhirLevels.basisWAt_of_same c.bw (c.same hf c.bp.1.1.2 c.bp.1.2 (c.apart_q c.bp.2.1)
    c.bt.2.1) fun r hr ↦
    c.same hf (c.bp.2.2 r hr).1.1.2 (c.bp.2.2 r hr).1.2 (c.apart_q (c.bp.2.2 r hr).2)
      (c.bt.2.2 r hr).2

/-- The state in the frame's states. -/
theorem state_at {st : MachineData} (hf : FFr m0 st) : WhirStateAt st.dmem (pA m0) w := by
  have hs := c.same_p hf (o := 0) (n := stateBytes) (by decide)
  rw [off_zero] at hs
  exact c.wa.1.agree fun j hj _ ↦ hs j hj

/-- The rounds in the frame's states. -/
theorem rounds_at {st : MachineData} (hf : FFr m0 st) :
    BufRoundsAt st.dmem (off (pA m0) roundsOff) rounds.toList := by
  have hs := c.same_p hf (o := roundsOff) (n := 200) (by decide)
  exact FoldRounds.bufRoundsAt_agree c.wa.2 fun j hj _ ↦ hs j hj

/-! ## The frame's environments -/

theorem frame_mapped' {st : MachineData} (hf : FFr m0 st) :
    NativeRustcVm.Mapped st.dmem (base m0 2672) 2672 :=
  fun i hi ↦ hf.kept _ (frame_mapped c.stack (by rw [stack_eq]; decide) i hi)

theorem fwf {st : MachineData} (hf : FFr m0 st) : (fenv m0 st []).WF :=
  Env.wf_of ⟨⟨c.frame_mapped' hf, base_noWrap (by have := c.hN'; omega)⟩, trivial⟩
    (List.pairwise_singleton _ _)

/-- The frame's environment with a region `(x, n)` apart from the entry's stack. -/
theorem fwf1 {st : MachineData} (hf : FFr m0 st) {x : BitVec 64} {n : Nat}
    (hm : NativeRustcVm.Mapped m0.dmem x n) (hnw : NoWrap x n)
    (hs : Apart x n (stackBelow m0 finalLevelStack) finalLevelStack) : (fenv m0 st [(x, n)]).WF :=
  Env.wf_of ⟨⟨c.frame_mapped' hf, base_noWrap (by have := c.hN'; omega)⟩,
    ⟨fun i hi ↦ hf.kept _ (hm i hi), hnw⟩, trivial⟩
    (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm (NativeRustcVmArm.Ring.apart_frame
      c.hN (by rw [stack_eq]; decide) hs)))

theorem aligned : (base m0 2672).toNat % 16 = 0 :=
  frame_aligned c.stack (by rw [stack_eq]; decide) rfl

theorem fmatch {st : MachineData} (hf : FFr m0 st) : Match (fenv m0 st []) fS st :=
  match_ofMachine ⟨rfl, fun _ ↦ c.aligned, trivial⟩ (by rw [hf.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

/-! ## What a callee gets -/

section
variable {st : MachineData} {N' : Nat} (hf : FFr m0 st) (hle : 2672 + N' ≤ finalLevelStack)
include hf hle

theorem stackOk' : StackOk st N' := c.tctx.stackOk hf hle

theorem rcAt' : RcAt st N' := c.tctx.rcAt hf hle

theorem tstateOk' : TStateOk st (tA m0) a N' := c.tctx.tstateOk hf hle

/-- The read-only data for a callee. -/
theorem rodataAt' : RodataAt st N' := by
  refine rodataAt_callee c.ro hf.same (fun q hq t ↦ ?_) hf.sp c.hN (by rw [stack_eq]; decide)
    (by omega)
  rcases hq with hq | hq | hq
  · exact rodata_not_stack c.ro c.hN t hq
  · exact rodata_not_out c.pout.2 c.pnw t (c.q_sub hq) (c.ro t).2.1
  · exact rodata_not_out c.tro c.tnw t hq (c.ro t).2.1

/-- **The transcript's context** for a callee. -/
theorem whirT : WhirT st (tA m0) a N' :=
  ⟨c.stackOk' hf hle, c.rcAt' hf hle, c.rodataAt' hf hle, c.tstateOk' hf hle, c.tro⟩

/-- An output in the frame, `n` bytes at `o`. -/
theorem localOk' {o n : Nat} (hon : o + n ≤ 2672) : OutOk st (tA m0) a (loc m0 o) n N' :=
  c.tctx.localOk hf hle hon

/-- An input for a callee. -/
theorem whirIn' {x : BitVec 64} {n : Nat} (h : WhirIn m0 x n finalLevelStack) :
    WhirIn st x n N' :=
  ⟨⟨fun i hi ↦ hf.kept _ (h.1.1 i hi), h.1.2⟩, hf.apart c.hN h.2 hle⟩

end

/-- The `WhirW` as an input. -/
theorem pIn : WhirIn m0 (pA m0) whirBytes finalLevelStack :=
  ⟨⟨c.pout.1.1, c.pnw⟩, c.pout.1.2.2.2.2.1⟩

/-- A part of the `WhirW` as an input. -/
theorem pIn_sub {o n : Nat} (h : o + n ≤ whirBytes) (hn : 0 < n) :
    WhirIn m0 (off (pA m0) o) n finalLevelStack := by
  have hp := c.pIn
  have hnw := c.pnw
  have ho : (off (pA m0) o).toNat = (pA m0).toNat + o := toNat_off (by
    unfold NoWrap whirBytes at hnw; unfold whirBytes at h; omega)
  refine ⟨⟨NativeRustcVm.Mapped.sub hp.1.1 h, ?_⟩, ?_⟩
  · unfold NoWrap at hnw ⊢; rw [ho]; omega
  · have := hp.2; unfold OffStack Apart at this ⊢; rw [ho]; omega

end Ctx

end

/-- **Between the read of the folded lane and the glued claims**: the frame, `2 ^ μ` in X19, `μ`
in X20, the basis in X21, the `WhirW` in X27, `laneFolds` in X28. -/
structure Base (m0 st : MachineData) : Prop where
  fr : FFr m0 st
  x19 : st.regs.X19.toNat = 2 ^ mu m0
  x20 : st.regs.X20 = m0.regs.X3
  x21 : st.regs.X21 = m0.regs.X5
  x27 : st.regs.X27 = m0.regs.X6
  x28 : st.regs.X28 = m0.regs.X4

/-- `Base` kept by a state of the frame whose callee-saved registers are kept. -/
theorem Base.saved {m0 st st' : MachineData} (h : Base m0 st) (hf : FFr m0 st')
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) : Base m0 st' where
  fr := hf
  x19 := by rw [show st'.regs.X19 = st.regs.X19 from hcs .X19 rfl]; exact h.x19
  x20 := (hcs .X20 rfl).trans h.x20
  x21 := (hcs .X21 rfl).trans h.x21
  x27 := (hcs .X27 rfl).trans h.x27
  x28 := (hcs .X28 rfl).trans h.x28

end

end NativeRustcVmArm.Whir.FinalLevel
