module

public import NativeRustcVmX64.Whir.FinalLevel.Exec
public import NativeRustcVmX64.Whir.FinalLevel.Model
public import NativeRustcVmX64.Whir.WhirLevels.ArgFrame
public import NativeRustcVmX64.Whir.WhirLevels.Same
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Sumcheck.Ctx

/-!
# `final_level`: its frame, its context (x86-64)

From the entry `m0` (the `TState` RDI, the index RSI, the level RDX, `μ` RCX, `laneFolds` R8, the
basis R9, the `WhirW` `w` the stack argument): the 2672-byte frame (`fa`, its byte `j` `loc m0 j`:
the six pushes at `2624` to `2672`, the body's `N(%rsp)` at `40 + N`, the pushed argument words
and return addresses below `40`), memory changed only in the stack and the outputs (`Sm`, `outs`:
the `WhirW`'s query buffer and the `TState`), the entry's facts (`Ctx`) and the addresses as
numbers (`Geo`).
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The level. -/
abbrev lA (m0 : MachineData) : BitVec 64 := reg m0 .rdx
/-- The basis. -/
abbrev bA (m0 : MachineData) : BitVec 64 := reg m0 .r9
/-- The `WhirW`, the stack argument. -/
abbrev pA (m0 : MachineData) : BitVec 64 := stackArg m0 0
/-- The `WhirW`'s query buffer. -/
abbrev qA (m0 : MachineData) : BitVec 64 := pA m0 + BitVec.ofNat 64 61352
/-- `μ`. -/
abbrev mu (m0 : MachineData) : Nat := (reg m0 .rcx).toNat
/-- The frame's base. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 2672
/-- The frame's byte `j`. -/
abbrev loc (m0 : MachineData) (j : Nat) : BitVec 64 := off (fa m0) j

/-- The outputs: the query buffer and the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (qA m0) queryBufBytes q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q

/-- Memory changed only in the stack and the outputs. -/
abbrev Sm (m0 d : MachineData) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange (stackBelow m0 finalLevelStack) finalLevelStack q ∨ outs m0 q)

/-- **The frame**, RSP at offset `o`. -/
structure Fr (m0 : MachineData) (o : Nat) (d : MachineData) : Prop where
  frame : Frame m0 2672 slots o d
  same : Sm m0 d

/-- The model's run. -/
abbrev runF (level : Whir.Level) (b : BasisW) (w : WhirStateW) (rounds : Array FoldRoundW)
    (m0 : MachineData) (s : TState) : Option (Unit × TState) :=
  (finalLevelM (reg m0 .rsi).toNat level (mu m0) (reg m0 .r8).toNat b w rounds).run s

/-- The addresses as numbers: RSP, the `TState`, the `WhirW`, the level, the decoded area, the
round constants. -/
structure Geo (sp t p l aw al rc : Nat) : Prop where
  hN : 5760 ≤ sp
  hA : sp + 16 ≤ 2 ^ 64
  tW : t + 760 ≤ 2 ^ 64
  pW : p + 63200 ≤ 2 ^ 64
  lW : l + 24 ≤ 2 ^ 64
  aW : aw + al ≤ 2 ^ 64
  rW : rc + 192 ≤ 2 ^ 64
  tS : t + 760 ≤ sp - 5760 ∨ sp + 16 ≤ t
  pS : p + 63200 ≤ sp - 5760 ∨ sp + 16 ≤ p
  aS : aw + al ≤ sp - 5760 ∨ sp + 8 ≤ aw
  lS : l + 24 ≤ sp - 5760 ∨ sp + 8 ≤ l
  rS : rc + 192 ≤ sp - 5760 ∨ sp + 8 ≤ rc
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
structure Ctx (a : DecArea) (s : TState) (level : Whir.Level) (ba : BasisAddrs) (b : BasisW)
    (w : WhirStateW) (rounds : Array FoldRoundW) (m0 : MachineData) : Prop where
  wt : WhirT m0 (tA m0) a finalLevelStack
  args : ArgsOk m0 1
  ts : TStateAt m0.dmem (tA m0) a s
  wa : WhirAt m0.dmem (pA m0) w rounds
  lv : LevelAt m0.dmem (lA m0) level
  bw : BasisWAt m0.dmem (bA m0) ba b
  mu64 : mu m0 < 64
  fold : 2 ^ mu m0 + level.fold ≤ laneCap
  alphas : w.alphas.size + mu m0 ≤ stackCap
  rate : level.logInvRate < 64
  qs : level.queries ≤ queryCap
  pout : WhirOut m0 (tA m0) a (pA m0) whirBytes finalLevelStack
  lin : WhirIn m0 (lA m0) levelBytes finalLevelStack
  lp : NativeRustcVm.Apart (lA m0) levelBytes (pA m0) whirBytes
  lt : NativeRustcVm.Apart (lA m0) levelBytes (tA m0) tstateBytes
  bp : BasisIn m0 (bA m0) ba finalLevelStack (pA m0) whirBytes
  bt : BasisIn m0 (bA m0) ba finalLevelStack (tA m0) tstateBytes
  bap : BasisApart (bA m0) ba
  at' : NativeRustcVm.Apart (rspOf m0 + 8#64) 8 (tA m0) tstateBytes
  ap : NativeRustcVm.Apart (rspOf m0 + 8#64) 8 (pA m0) whirBytes
  got : GotAt m0 finalLevelStack
    ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
      (lA m0, levelBytes), (rspOf m0 + 8#64, 8)] ++ rodataAreas) ["memcpy", "memset"]

/-- The function's goal. -/
abbrev Goal (a : DecArea) (s : TState) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    FinalLevelPost a s level b w rounds m0 st.data

end

end

public section

theorem stack_eq : finalLevelStack = 5760 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 2672 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 2624 ≤ p.1 := by decide

theorem comb_arg {sp x n ar : Nat} (hn : 0 < n) (hN : 5760 ≤ sp) (har : ar = sp + 8)
    (h1 : x + n ≤ sp - 5760 ∨ sp - 5760 + (5760 + 8) ≤ x) (h2 : ar + 8 ≤ x ∨ x + n ≤ ar) :
    x + n ≤ sp - 5760 ∨ sp + 16 ≤ x := by omega

theorem comb_stk {sp x n : Nat} (h : x + n ≤ sp - 5760 ∨ sp - 5760 + (5760 + 8) ≤ x) :
    x + n ≤ sp - 5760 ∨ sp + 8 ≤ x := by omega

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

theorem Ctx.of_pre (h : FinalLevelPre a s level ba b w rounds m0) :
    Ctx a s level ba b w rounds m0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩

namespace Ctx

variable (c : Ctx a s level ba b w rounds m0)
include c

theorem stack : StackOk m0 finalLevelStack := c.wt.1

/-- **The addresses as numbers.** -/
theorem geo : Geo (rspOf m0).toNat (tA m0).toNat (pA m0).toNat (lA m0).toNat a.words.toNat
    (8 * a.len) rcAddr.toNat := by
  have hS := c.wt.1
  have hN : finalLevelStack ≤ (rspOf m0).toNat := hS.1
  have hsb : (stackBelow m0 finalLevelStack).toNat = (rspOf m0).toNat - 5760 := by
    rw [stackBelow_toNat hN, stack_eq]
  have hfp := c.ts.footprint
  have hA : (rspOf m0).toNat + 8 + 8 * 1 ≤ 2 ^ 64 := c.args.2
  have harg : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl]; omega
  have e1 : tstateBytes = 760 := rfl
  have e2 : whirBytes = 63200 := rfl
  have e3 : levelBytes = 24 := rfl
  have h1 : (tA m0).toNat + tstateBytes ≤ (stackBelow m0 finalLevelStack).toNat ∨
      (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8) ≤ (tA m0).toNat :=
    c.wt.2.2.2.1.1
  have h2 : a.words.toNat + 8 * a.len ≤ (stackBelow m0 finalLevelStack).toNat ∨
      (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8) ≤ a.words.toNat :=
    c.wt.2.2.2.1.2.1
  have h3 : (pA m0).toNat + whirBytes ≤ (stackBelow m0 finalLevelStack).toNat ∨
      (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8) ≤ (pA m0).toNat :=
    c.pout.1.2.2.2.2.1
  have h4 : (lA m0).toNat + levelBytes ≤ (stackBelow m0 finalLevelStack).toNat ∨
      (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8) ≤ (lA m0).toNat := c.lin.2
  have h5 : (pA m0).toNat + whirBytes ≤ (tA m0).toNat ∨
      (tA m0).toNat + tstateBytes ≤ (pA m0).toNat := c.pout.1.2.2.1
  have h6 : (pA m0).toNat + whirBytes ≤ a.words.toNat ∨
      a.words.toNat + 8 * a.len ≤ (pA m0).toNat := c.pout.1.2.2.2.1
  have h7 : (tA m0).toNat + tstateBytes ≤ a.words.toNat ∨
      a.words.toNat + 8 * a.len ≤ (tA m0).toNat := hfp.2.2
  have h8 : (lA m0).toNat + levelBytes ≤ (pA m0).toNat ∨
      (pA m0).toNat + whirBytes ≤ (lA m0).toNat := c.lp
  have h9 : (lA m0).toNat + levelBytes ≤ (tA m0).toNat ∨
      (tA m0).toNat + tstateBytes ≤ (lA m0).toNat := c.lt
  have h10 : (rspOf m0 + 8#64).toNat + 8 ≤ (tA m0).toNat ∨
      (tA m0).toNat + tstateBytes ≤ (rspOf m0 + 8#64).toNat := c.at'
  have h11 : (rspOf m0 + 8#64).toNat + 8 ≤ (pA m0).toNat ∨
      (pA m0).toNat + whirBytes ≤ (rspOf m0 + 8#64).toNat := c.ap
  have h12 : rcAddr.toNat + 192 ≤ (stackBelow m0 finalLevelStack).toNat ∨
      (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8) ≤ rcAddr.toNat :=
    c.wt.2.1.2.2
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

end NativeRustcVmX64.Whir.Levels.FL
