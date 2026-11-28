module

public import NativeRustcVmX64.Whir.NextLevel.Exec
public import NativeRustcVmX64.Whir.WhirLevels.Steps
public import NativeRustcVm.Whir.Sample

/-!
# `next_level`: its frame, its context, the model (x86-64)

From the entry `m0` (the `TState` RDI, the index RSI, the level RDX, the next level's fold RCX
and rate exponent R8, `μ` R9, the state `w` the stack argument): the 8176-byte frame (`fa`, its
byte `j` `loc m0 j`), memory changed only in the stack and the outputs (`Sm`, `outs`: the `TState`
and the state `w`), the entry's facts (`Ctx`) and the addresses as numbers (`Geo`). `run_eq`:
`nextLevelM` as a chain of its steps.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The level. -/
abbrev lA (m0 : MachineData) : BitVec 64 := reg m0 .rdx
/-- The state `w` (`WhirW`), the stack argument. -/
abbrev pA (m0 : MachineData) : BitVec 64 := stackArg m0 0
/-- The frame's base. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 8176
/-- The frame's byte `j`. -/
abbrev loc (m0 : MachineData) (j : Nat) : BitVec 64 := off (fa m0) j

/-- The outputs: the state and the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (pA m0) whirBytes q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q

/-- Memory changed only in the stack and the outputs. -/
abbrev Sm (m0 d : MachineData) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange (stackBelow m0 nextLevelStack) nextLevelStack q ∨ outs m0 q)

/-- **The frame**, RSP at offset `o`. -/
structure Fr (m0 : MachineData) (o : Nat) (d : MachineData) : Prop where
  frame : Frame m0 8176 slots o d
  same : Sm m0 d

/-- The model's run. -/
abbrev runN (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW) (m0 : MachineData)
    (s : TState) : Option (WhirStateW × TState) :=
  (nextLevelM (reg m0 .rsi).toNat level ⟨(reg m0 .rcx).toNat, (reg m0 .r8).toNat, 0⟩
    (reg m0 .r9).toNat w rounds).run s

/-- The addresses as numbers: RSP, the `TState`, the state, the level, the decoded area, the
round constants. -/
structure Geo (sp t p l aw al rc : Nat) : Prop where
  hN : 11312 ≤ sp
  hA : sp + 16 ≤ 2 ^ 64
  tW : t + 760 ≤ 2 ^ 64
  pW : p + 63200 ≤ 2 ^ 64
  lW : l + 24 ≤ 2 ^ 64
  aW : aw + al ≤ 2 ^ 64
  rW : rc + 192 ≤ 2 ^ 64
  tS : t + 760 ≤ sp - 11312 ∨ sp + 16 ≤ t
  pS : p + 63200 ≤ sp - 11312 ∨ sp + 16 ≤ p
  aS : aw + al ≤ sp - 11312 ∨ sp + 8 ≤ aw
  lS : l + 24 ≤ sp - 11312 ∨ sp + 8 ≤ l
  rS : rc + 192 ≤ sp - 11312 ∨ sp + 8 ≤ rc
  pT : p + 63200 ≤ t ∨ t + 760 ≤ p
  pA : p + 63200 ≤ aw ∨ aw + al ≤ p
  tA : t + 760 ≤ aw ∨ aw + al ≤ t
  lP : l + 24 ≤ p ∨ p + 63200 ≤ l
  lT : l + 24 ≤ t ∨ t + 760 ≤ l
  tR : t + 760 ≤ rc ∨ rc + 192 ≤ t
  pR : p + 63200 ≤ rc ∨ rc + 192 ≤ p

section
variable [Labels]

/-- **The entry's facts.** -/
structure Ctx (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) : Prop where
  wt : WhirT m0 (tA m0) a nextLevelStack
  args : ArgsOk m0 1
  ts : TStateAt m0.dmem (tA m0) a s
  roots : s.roots.size < maxRoots
  wa : WhirAt m0.dmem (pA m0) w rounds
  lv : LevelAt m0.dmem (lA m0) level
  fold : level.fold ≤ roundCap
  rate : level.logInvRate < 64
  qs : level.queries ≤ queryCap
  nf : (reg m0 .rcx).toNat < 63
  nr : (reg m0 .r8).toNat < 64
  mu : (reg m0 .r9).toNat ≤ stackCap
  glued : w.glued.size + 2 ≤ gluedCap
  pout : WhirOut m0 (tA m0) a (pA m0) whirBytes nextLevelStack
  lin : WhirIn m0 (lA m0) levelBytes nextLevelStack
  lp : NativeRustcVm.Apart (lA m0) levelBytes (pA m0) whirBytes
  lt : NativeRustcVm.Apart (lA m0) levelBytes (tA m0) tstateBytes
  at' : NativeRustcVm.Apart (rspOf m0 + 8#64) 8 (tA m0) tstateBytes
  ap : NativeRustcVm.Apart (rspOf m0 + 8#64) 8 (pA m0) whirBytes
  got : GotAt m0 nextLevelStack ([(tA m0, tstateBytes), (a.words, 8 * a.len),
    (pA m0, whirBytes), (lA m0, levelBytes), (rspOf m0 + 8#64, 8)] ++ rodataAreas)
    ["memcpy", "memset"]

/-- The function's goal. -/
abbrev Goal (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    NextLevelPost a s level w rounds m0 st.data

end

end

/-! ## The model -/

@[expose] public section

/-- From `query_openings` on. -/
def tail8 (index mu : Nat) (w : WhirStateW) (rounds : Array FoldRoundW) (xs ood : Array EW)
    (v : EW) (qs : Array UInt64) (lam : EW) (s8 : TState) : Option (WhirStateW × TState) :=
  ((queryOpenings index qs).run s8).bind fun p9 ↦
    some (glueLevel w lam mu ood v qs (powers lam qs.size)
      (batchedOf index mu rounds xs qs p9.1 (powers lam qs.size)), p9.2)

/-- From `sample_queries` on. -/
def tail6 (index mu : Nat) (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (xs ood : Array EW) (v : EW) (s6 : TState) : Option (WhirStateW × TState) :=
  ((sampleQueries (mu + level.logInvRate) level.queries).run s6).bind fun p7 ↦
    tail8 index mu w rounds xs ood v p7.1 (sq p7.2).1 (sq p7.2).2

/-- From `read_scalar` on. -/
def tail4 (index mu : Nat) (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (xs ood : Array EW) (s4 : TState) : Option (WhirStateW × TState) :=
  (readScalar.run s4).bind fun p5 ↦ ((grind Whir.queryGrindingBits).run p5.2).bind fun p6 ↦
    tail6 index mu level w rounds xs ood p5.1 p6.2

/-- From `sample_challenges` on. -/
def tail3 (index mu : Nat) (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (xs : Array EW) (s3 : TState) : Option (WhirStateW × TState) :=
  ((sampleChallenges mu).run s3).bind fun p4 ↦ tail4 index mu level w rounds xs p4.1 p4.2

end

public section

/-- **`nextLevelM` as a chain of its steps.** -/
theorem run_eq (index : Nat) (level next : Whir.Level) (mu : Nat) (w : WhirStateW)
    (rounds : Array FoldRoundW) (s : TState) :
    (nextLevelM index level next mu w rounds).run s =
      ((readCommitment (mu - next.fold + next.logInvRate) (2 * 2 ^ next.fold)).run s).bind
        fun p1 ↦ ((readScalars level.fold).run p1.2).bind
        fun p2 ↦ ((grind Whir.oodGrindingBits).run p2.2).bind
        fun p3 ↦ tail3 index mu level w rounds p2.1 p3.2 := by
  rfl

theorem stack_eq : nextLevelStack = 11312 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 8176 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 8128 ≤ p.1 := by decide

theorem comb_arg {sp x n ar : Nat} (hn : 0 < n) (hN : 11312 ≤ sp) (har : ar = sp + 8)
    (h1 : x + n ≤ sp - 11312 ∨ sp - 11312 + (11312 + 8) ≤ x) (h2 : ar + 8 ≤ x ∨ x + n ≤ ar) :
    x + n ≤ sp - 11312 ∨ sp + 16 ≤ x := by omega

theorem comb_stk {sp x n : Nat} (h : x + n ≤ sp - 11312 ∨ sp - 11312 + (11312 + 8) ≤ x) :
    x + n ≤ sp - 11312 ∨ sp + 8 ≤ x := by omega

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

theorem Ctx.of_pre (h : NextLevelPre a s level w rounds m0) : Ctx a s level w rounds m0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, hg⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, hg⟩

namespace Ctx

variable (c : Ctx a s level w rounds m0)
include c

theorem stack : StackOk m0 nextLevelStack := c.wt.1

/-- **The addresses as numbers.** -/
theorem geo : Geo (rspOf m0).toNat (tA m0).toNat (pA m0).toNat (lA m0).toNat a.words.toNat
    (8 * a.len) rcAddr.toNat := by
  have hS := c.wt.1
  have hN : nextLevelStack ≤ (rspOf m0).toNat := hS.1
  have hsb : (stackBelow m0 nextLevelStack).toNat = (rspOf m0).toNat - 11312 := by
    rw [stackBelow_toNat hN, stack_eq]
  have hfp := c.ts.footprint
  have hA : (rspOf m0).toNat + 8 + 8 * 1 ≤ 2 ^ 64 := c.args.2
  have harg : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl]; omega
  have e1 : tstateBytes = 760 := rfl
  have e2 : whirBytes = 63200 := rfl
  have e3 : levelBytes = 24 := rfl
  have h1 : (tA m0).toNat + tstateBytes ≤ (stackBelow m0 nextLevelStack).toNat ∨
      (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8) ≤ (tA m0).toNat :=
    c.wt.2.2.2.1.1
  have h2 : a.words.toNat + 8 * a.len ≤ (stackBelow m0 nextLevelStack).toNat ∨
      (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8) ≤ a.words.toNat :=
    c.wt.2.2.2.1.2.1
  have h3 : (pA m0).toNat + whirBytes ≤ (stackBelow m0 nextLevelStack).toNat ∨
      (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8) ≤ (pA m0).toNat :=
    c.pout.1.2.2.2.2.1
  have h4 : (lA m0).toNat + levelBytes ≤ (stackBelow m0 nextLevelStack).toNat ∨
      (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8) ≤ (lA m0).toNat := c.lin.2
  have h5 : (pA m0).toNat + whirBytes ≤ (tA m0).toNat ∨ (tA m0).toNat + tstateBytes ≤ (pA m0).toNat :=
    c.pout.1.2.2.1
  have h6 : (pA m0).toNat + whirBytes ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (pA m0).toNat :=
    c.pout.1.2.2.2.1
  have h7 : (tA m0).toNat + tstateBytes ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (tA m0).toNat :=
    hfp.2.2
  have h8 : (lA m0).toNat + levelBytes ≤ (pA m0).toNat ∨ (pA m0).toNat + whirBytes ≤ (lA m0).toNat :=
    c.lp
  have h9 : (lA m0).toNat + levelBytes ≤ (tA m0).toNat ∨ (tA m0).toNat + tstateBytes ≤ (lA m0).toNat :=
    c.lt
  have h10 : (rspOf m0 + 8#64).toNat + 8 ≤ (tA m0).toNat ∨
      (tA m0).toNat + tstateBytes ≤ (rspOf m0 + 8#64).toNat := c.at'
  have h11 : (rspOf m0 + 8#64).toNat + 8 ≤ (pA m0).toNat ∨
      (pA m0).toNat + whirBytes ≤ (rspOf m0 + 8#64).toNat := c.ap
  have h12 : rcAddr.toNat + 192 ≤ (stackBelow m0 nextLevelStack).toNat ∨
      (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8) ≤ rcAddr.toNat := c.wt.2.1.2.2
  have h13 : (tA m0).toNat + tstateBytes ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat :=
    c.wt.2.2.2.1.2.2
  have h14 : (pA m0).toNat + whirBytes ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (pA m0).toNat :=
    c.pout.1.2.2.2.2.2
  have w1 : (tA m0).toNat + 760 ≤ 2 ^ 64 := hfp.1.2
  have w2 : (pA m0).toNat + 63200 ≤ 2 ^ 64 := c.pout.1.2.1
  have w3 : (lA m0).toNat + 24 ≤ 2 ^ 64 := c.lin.1.2
  have w4 : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hfp.2.1.2
  have w5 : rcAddr.toNat + 192 ≤ 2 ^ 64 := c.wt.2.1.2.1
  rw [hsb, stack_eq] at h1 h2 h3 h4 h12
  rw [e1] at h1 h5 h7 h9 h10 h13
  rw [e2] at h3 h5 h6 h8 h11 h14
  rw [e3] at h4 h8 h9
  rw [stack_eq] at hN
  have hA' : (rspOf m0).toNat + 16 ≤ 2 ^ 64 := by omega
  exact ⟨hN, hA', w1, w2, w3, w4, w5, comb_arg (by decide) hN harg h1 h10,
    comb_arg (by decide) hN harg h3 h11, comb_stk h2,
    comb_stk h4, comb_stk h12, h5, h6, h7, h8, h9, h13, h14⟩

end Ctx

end

end

end NativeRustcVmX64.Whir.Levels.NL
