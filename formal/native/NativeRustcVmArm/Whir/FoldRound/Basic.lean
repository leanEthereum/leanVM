module

public import NativeRustcVmArm.Whir.FoldRound.Exec
public import NativeRustcVmArm.Whir.TFrame
public import NativeRustcVmArm.Whir.State
public import NativeRustcVm.Whir.Fold

/-!
# `fold_round`: its frame, its context

From the entry `m0` (the output X0, the `TState` X1, the state X2): the 208-byte frame (`FFr`,
X19 to X30 saved at 112 to 207), the `Option<EW>` `read_scalar` writes at 88 (`loc m0 88`), the
outputs (`outs`: the output, the state, the `TState`), the context `ctx` for the calls. Between
blocks (`Base`): X19, X20, X23 hold the output, the state and the `TState`, the state unchanged.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(112, .X29), (120, .X30), (128, .X28), (136, .X27), (144, .X26), (152, .X25), (160, .X24),
    (168, .X23), (176, .X22), (184, .X21), (192, .X20), (200, .X19)]

/-- The output. -/
abbrev oA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The state. -/
abbrev pA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec

/-- The outputs. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (oA m0) 40 q ∨ InRange (pA m0) stateBytes q ∨ InRange (tA m0) tstateBytes q

/-- The frame. -/
abbrev FFr (m0 st : MachineData) : Prop := Fr m0 208 foldRoundStack slots [] (outs m0) st

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 208 + BitVec.ofNat 64 o

/-- Between blocks: the frame, the output, the state and the `TState` in X19, X20, X23, the state
`w` at X20. -/
structure Base [Labels] (w : WhirStateW) (m0 st : MachineData) : Prop where
  fr : FFr m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X2
  x23 : st.regs.X23 = m0.regs.X1
  ws : WhirStateAt st.dmem (pA m0) w

end

public section

theorem stack_eq : foldRoundStack = 800 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 208 := by decide

/-- The frame's bytes are in the entry's stack. -/
theorem frame_sub {m0 : MachineData} {F N : Nat} (hN : N ≤ m0.regs.SP.toNat) (hF : F ≤ N)
    {q : BitVec 64} (hq : InRange (base m0 F) F q) : InRange (stackBelow m0 N) N q := by
  have e1 := base_toNat (m0 := m0) (F := F) (by omega)
  have e2 := base_toNat (m0 := m0) (F := N) hN
  exact NativeRustcVm.InRange.mono hq (base_noWrap (by omega)) (base_noWrap hN)
    (by show (base m0 N).toNat ≤ _; omega) (by show _ ≤ (base m0 N).toNat + _; omega)

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

theorem pre_hN (h : FoldRoundPre a s w m0) : foldRoundStack ≤ m0.regs.SP.toNat := h.1.1.2.1

/-- A range apart from the entry's stack misses the frame. -/
theorem not_frame (h : FoldRoundPre a s w m0) {x : BitVec 64} {n : Nat}
    (hx : Apart x n (stackBelow m0 foldRoundStack) foldRoundStack) (hnx : NoWrap x n)
    {q : BitVec 64} (hq : InRange x n q) : ¬InRange (base m0 208) 208 q := fun hf ↦
  NativeRustcVm.Apart.not_inRange hx hnx (base_noWrap (pre_hN h)) hq
    (frame_sub (pre_hN h) (by rw [stack_eq]; decide) hf)

/-- **The context of `fold_round`'s calls.** -/
theorem ctx (h : FoldRoundPre a s w m0) : TCtx m0 208 foldRoundStack (tA m0) a (outs m0) := by
  obtain ⟨⟨hS, hrc, -, htok, -⟩, hts, -, -, ⟨hpo, -⟩, ⟨hoo, -⟩, -⟩ := h
  have hfp := hts.footprint
  have hnt : NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  refine ⟨hS, hrc, htok, hfp, by rw [stack_eq]; decide, rfl, fun q hq hr ↦ ?_, fun q hq hd ↦ ?_,
    fun q hq ↦ Or.inr (Or.inr hq), fun q hq hf ↦ ?_⟩
  · rcases hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange hoo.2.2.2.2.2 hoo.2.1 hrc.2.1 hq hr
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.2 hpo.2.1 hrc.2.1 hq hr
    · exact NativeRustcVm.Apart.not_inRange htok.2.2 hnt hrc.2.1 hq hr
  · rcases hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange hoo.2.2.2.1 hoo.2.1 hnd hq hd
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 hpo.2.1 hnd hq hd
    · exact NativeRustcVm.Apart.not_inRange hfp.2.2 hnt hnd hq hd
  · have hs := frame_sub hS.2.1 (by rw [stack_eq]; decide) hf
    have hnN := base_noWrap (m0 := m0) (F := foldRoundStack) hS.2.1
    rcases hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange hoo.2.2.2.2.1 hoo.2.1 hnN hq hs
    · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.1 hpo.2.1 hnN hq hs
    · exact NativeRustcVm.Apart.not_inRange htok.1 hnt hnN hq hs

end

end

end NativeRustcVmArm.Whir.FoldRound
