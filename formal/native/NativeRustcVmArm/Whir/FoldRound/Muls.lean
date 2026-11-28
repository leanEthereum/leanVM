module

public import NativeRustcVmArm.Whir.FoldRound.MulStep

/-!
# `fold_round`: the six products

From `b12` (`AtB12`): `P1 = α·(claim + u0)` (`b12`, reading the claim from the state), `P2 = α·α`
(`b13`), `P3 = P2·v` (`b14`), `P4 = β·c0` (`b15`), `P5 = α·β` (`b16`), `P6 = P5·(c1 + c0)` (`b17`),
to `b18` (`AtB18`), the partial products saved in the frame.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

@[expose] public section

/-- `α`, `β` of the round after the grind's state `s5`. -/
abbrev alA (s5 : TState) : EW := (sq s5).1
abbrev beA (s5 : TState) : EW := (sq (sq s5).2).1

/-- The products. -/
def p1 (w : WhirStateW) (s5 : TState) (u0 : EW) : EW :=
  EW.mul (alA s5) ⟨w.claim.c0 ^^^ u0.c0, w.claim.c1 ^^^ u0.c1⟩
def p3 (s5 : TState) (v : EW) : EW := EW.mul (EW.mul (alA s5) (alA s5)) v
def p4 (s5 : TState) (c0 : EW) : EW := EW.mul (beA s5) c0
def p6 (s5 : TState) (c0 c1 : EW) : EW :=
  EW.mul (EW.mul (alA s5) (beA s5)) ⟨c1.c0 ^^^ c0.c0, c1.c1 ^^^ c0.c1⟩

end

public section

section
variable [Labels]

/-- **At `b18`.** -/
structure AtB18 (a : DecArea) (s0 : TState) (w : WhirStateW) (m0 : MachineData) (s5 : TState)
    (u0 v c0 c1 : EW) (st : MachineData) : Prop where
  tb : Tb a w m0 (sq (sq s5).2).2 st
  x0 : st.regs.X0 = (p6 s5 c0 c1).c0
  x1 : st.regs.X1 = (p6 s5 c0 c1).c1
  x28 : st.regs.X28 = (p4 s5 c0).c0
  x29 : st.regs.X29 = u0.c0
  x24 : st.regs.X24 = u0.c1
  x22 : st.regs.X22 = (alA s5).c1
  x23 : st.regs.X23 = (beA s5).c1
  fw : FW st.dmem m0 [(56, (p1 w s5 u0).c0), (64, (p1 w s5 u0).c1), (32, (p3 s5 v).c0),
    (40, (p3 s5 v).c1), (24, (p4 s5 c0).c1), (16, (beA s5).c0), (8, (alA s5).c0)]
  model : (foldRound w).run s0 = some ((foldW w u0 v c0 c1 (alA s5) (beA s5),
    ⟨alA s5, beA s5⟩), (sq (sq s5).2).2)

omit [Labels] in
theorem FW.append {d : Mem 64} {m0 : MachineData} {L L' : List (Nat × UInt64)} (h : FW d m0 L)
    (h' : FW d m0 L') : FW d m0 (L ++ L') := fun o v hp ↦ by
  rcases List.mem_append.mp hp with hp | hp
  · exact h o v hp
  · exact h' o v hp

/-- The frame and the state's head. -/
abbrev stateEnv (m0 st : MachineData) : Env :=
  Env.ofMachine st [(base m0 208, 208), (pA m0, 24)]

end

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

theorem state_wf (h : FoldRoundPre a s0 w m0) {st : MachineData} (hf : FFr m0 st) :
    (stateEnv m0 st).WF := by
  have hpo : OutOk m0 (tA m0) a (pA m0) stateBytes foldRoundStack := h.2.2.2.2.1.1
  have hN := pre_hN h
  rw [stack_eq] at hN
  refine Env.wf_of ⟨⟨frame_mapped' h hf, base_noWrap (by omega)⟩,
    ⟨fun i hi ↦ hf.kept _ (hpo.1 i (by unfold stateBytes; omega)),
      NativeRustcVm.NoWrap.mono hpo.2.1 (show 24 ≤ stateBytes by decide)⟩, trivial⟩
    (List.pairwise_pair.mpr (NativeRustcVm.Apart.mono (NativeRustcVm.Apart.symm
      (NativeRustcVmArm.Ring.apart_frame (pre_hN h) (by rw [stack_eq]; decide) hpo.2.2.2.2.1))
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (show (pA m0).toNat + 24 ≤ (pA m0).toNat + stateBytes by unfold stateBytes; omega)))

/-- The frame and the state's head, from a state of the tail. -/
theorem state_match (h : FoldRoundPre a s0 w m0) {s : TState} {st : MachineData}
    (hb : Tb a w m0 s st) : Match (stateEnv m0 st) stateS st := by
  refine match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl, rfl,
    fun h ↦ absurd h (by decide), trivial⟩ (by rw [hb.fr.sp]; simp [Sym.eval])
    ⟨?_, trivial⟩ trivial trivial trivial
  show (st.regs.getXReg .X20).toBitVec = _
  simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, BitVec.add_zero]
  exact congrArg UInt64.toBitVec hb.x20

omit [Host] in
theorem claim_load [Labels] {s : TState} {st : MachineData} (hb : Tb a w m0 s st) :
    (stateEnv m0 st).load 1 0 8 = w.claim.c0.toBitVec ∧
      (stateEnv m0 st).load 1 8 8 = w.claim.c1.toBitVec := by
  have hc := NativeRustcVm.ewAt_iff.mp hb.ws.claim
  exact ⟨load_word (by simpa using hc.1), load_word (by simpa using hc.2)⟩

end

end NativeRustcVmArm.Whir.FoldRound
