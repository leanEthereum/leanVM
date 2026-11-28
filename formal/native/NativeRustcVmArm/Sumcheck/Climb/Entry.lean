module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Sumcheck.Climb.Frame

/-!
# `climb`'s entry

`b0` saves the registers, copies the node into the frame and leaves for `.LClimb_8` at height `0`;
else `b1` sets up the loop's registers and jumps to `.LClimb_4` (`entry_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Climb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Climb
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck

@[expose] public section

/-- **The loop's invariant** at `.LClimb_4`, `l < |P|` levels climbed. -/
structure Inv (m0 : MachineData) (N : Digest) (P : Array Digest) (l : Nat) (m : MachineData) :
    Prop where
  frame : Frame m0 (climbTo N m0.regs.X2 P l).1 m
  lt : l < P.size
  x20 : (m.regs.getXReg .X20).toNat = P.size - l
  x21 : m.regs.getXReg .X21 = (climbTo N m0.regs.X2 P l).2
  x22 : (m.regs.getXReg .X22).toNat = 4 * l
  x23 : (m.regs.getXReg .X23).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * l + 16)

end

public section

variable [Host] {N : Digest} {P : Array Digest} {m0 : MachineData} {k : Nat}

/-- The entry's environment: the frame and the node. -/
def env0 (m0 : MachineData) : Env := Env.ofMachine m0 [(fr m0, 144), (m0.regs.X1.toBitVec, 32)]

theorem wf_env0 (hpre : ClimbPre N P m0) : (env0 m0).WF := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have ⟨_, _, _, _, hN, _, hnw, _, _, _, hap, _⟩ := hpre
  have hmN : Mapped m0.dmem m0.regs.X1.toBitVec 32 := by
    have := NativeRustcVm.WordsAt.mapped hN
    simp only [Vector.length_toList] at this
    exact this
  refine Env.wf_of ⟨⟨mapped_fr hpre (fun _ h ↦ h), by show _ + 144 ≤ _; rw [g.fr]; omega⟩,
      ⟨hmN, hnw⟩, trivial⟩
    (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  simp only [List.mem_singleton, forall_eq]
  unfold Apart at hap ⊢
  rw [g.stk, climbStack_eq] at hap
  rw [g.fr]
  omega

/-- After `b0`'s writes, the frame holds the node and the saved registers. -/
theorem frame_of_b0 (hpre : ClimbPre N P m0) {S : SState} {m : MachineData}
    (hm : Match (env0 m0) S m) (hmem : S.mem = (after b0 entryS).mem) (hsp : S.sp = .ptr 0 0)
    (hx19 : S.reg .X19 = some (.reg .X0))
    (hregs : ∀ r ∈ outer, S.reg r = some (.reg r)) : Frame m0 N m := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have hwf := wf_env0 hpre
  have hN := hpre.2.2.2.2.1
  have hb0 : (env0 m0).base 0 = fr m0 := rfl
  have hb1 : (env0 m0).base 1 = m0.regs.X1.toBitVec := rfl
  have hw : ∀ i < 4, ∀ j < 8,
      findWrite 0 (8 * i + j) S.mem = some (.load 1 (8 * i) 8, j) := by
    rw [hmem, after_eq run_b0]; decide +kernel
  have hws : ∀ j < 8, findWrite 0 (96 + j) S.mem = some (.reg .X30, j) ∧
      findWrite 0 (104 + j) S.mem = some (.reg .X23, j) ∧
      findWrite 0 (112 + j) S.mem = some (.reg .X22, j) ∧
      findWrite 0 (120 + j) S.mem = some (.reg .X21, j) ∧
      findWrite 0 (128 + j) S.mem = some (.reg .X20, j) ∧
      findWrite 0 (136 + j) S.mem = some (.reg .X19, j) := by
    rw [hmem, after_eq run_b0]; decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm.sp, hsp]; simp [Sym.eval, hb0]
  · rw [hm.regs .X19 _ hx19]; rfl
  · rw [NativeRustcVm.wordsAt_iff]
    intro i hi
    have hD : N.toList.length = 4 := by simp
    rw [hD] at hi
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm (r := 0) (o := 8 * i) rfl
      (by omega) (hw i hi)
    rw [show (Sym.load 1 (8 * i) 8).eval (env0 m0) = (env0 m0).load 1 (8 * i) 8 from rfl,
      load_word (by rw [hb1]; exact hN.getElem (i := i) (by simpa using hi))] at this
    exact this
  · rw [NativeRustcVm.wordsAt_iff]
    intro i hi
    simp only [slotWords, List.length_cons, List.length_nil] at hi
    rw [NativeRustcVm.addr_add_add]
    have key : ∀ (o : Nat) (r : XReg), o + 8 ≤ 144 → (∀ j < 8, findWrite 0 (o + j) S.mem =
        some (.reg r, j)) → NativeRustcVm.WordAt m.dmem (fr m0 + BitVec.ofNat 64 o)
          (m0.regs.getXReg r) := by
      intro o r ho h
      have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm (r := 0) (o := o) rfl ho h
      rw [show (Sym.reg r).eval (env0 m0) = (m0.regs.getXReg r).toBitVec by
        simp [Sym.eval, env0]] at this
      exact this
    match i, hi with
    | 0, _ => exact key 96 .X30 (by omega) fun j hj ↦ (hws j hj).1
    | 1, _ => exact key 104 .X23 (by omega) fun j hj ↦ (hws j hj).2.1
    | 2, _ => exact key 112 .X22 (by omega) fun j hj ↦ (hws j hj).2.2.1
    | 3, _ => exact key 120 .X21 (by omega) fun j hj ↦ (hws j hj).2.2.2.1
    | 4, _ => exact key 128 .X20 (by omega) fun j hj ↦ (hws j hj).2.2.2.2.1
    | 5, _ => exact key 136 .X19 (by omega) fun j hj ↦ (hws j hj).2.2.2.2.2
  · intro r hr
    exact UInt64.toBitVec_inj.mp ((hm.regs r _ (hregs r hr)).trans rfl)
  · intro p hpn
    rw [hm.get?_mem0 hwf fun hw ↦ hpn (fr_inRange g (Written.inRange (r := 0) rfl
      (by rw [g.fr]; omega) (by rw [hmem, after_eq run_b0]; decide +kernel) hw))]
    rfl
  · exact hm.kept hwf

/-- **The entry**: at `.LClimb_8` with the node at height `0`, else at `.LClimb_4` with nothing
climbed. -/
theorem entry_spec (hp : Placed code k) (hpre : ClimbPre N P m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset) ∧ P.size = 0 ∧ Frame m0 N st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b5Offset) ∧ Inv m0 N P 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b0Offset)⟩ := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have hwf := wf_env0 hpre
  have hm : Match (env0 m0) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [g.fr]; omega, rfl, by simp, trivial⟩
      (by simp [Sym.eval, fr]) ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hsize := hpre.2.2.2.1
  refine exec_then hk0 run_b0 hwf hm fun st hm' hpc ↦ ?_
  have hfr : Frame m0 N st.data :=
    frame_of_b0 hpre hm' (by rw [after_eq run_b0]) rfl rfl
      (by intro r hr; simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hc : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X4) (.lit 0)).eval (env0 m0) =
      (m0.regs.X4.toBitVec == 0#64) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]; rfl
  simp only [PcOk] at hpc
  rw [hc] at hpc
  have hl8 : Labels.label NativeRustcVmArm.Vm.Climb.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset) := hp.label (j := NativeRustcVmArm.Vm.Climb.b10Offset) NativeRustcVmArm.Vm.Climb.label_8_at
  have hl4 : Labels.label NativeRustcVmArm.Vm.Climb.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b5Offset) := hp.label (j := NativeRustcVmArm.Vm.Climb.b5Offset) NativeRustcVmArm.Vm.Climb.label_4_at
  by_cases h0 : m0.regs.X4 = 0
  · have : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset) := by
      have h0' : (m0.regs.X4.toBitVec == 0#64) = true := by rw [h0]; rfl
      simp only [h0', ↓reduceIte] at hpc
      rw [hpc, hl8]
    exact Eventually.done _ (Or.inl ⟨this, by rw [hsize, h0]; rfl, hfr⟩)
  · have h0' : (m0.regs.X4.toBitVec == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h ↦ h0 (UInt64.toBitVec_inj.mp h)
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at hpc
    have hm0 : Match (env0 m0) (after b0 entryS) st.data := by rw [after_eq run_b0]; exact hm'
    refine exec_at hk1 run_b1 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
    have hm1' : Match (env0 m0) (after b1 (after b0 entryS)) st1.data := by
      rw [after_eq run_b1]; exact hm1
    have hfr1 : Frame m0 N st1.data :=
      frame_of_b0 hpre hm1' (by rw [after_eq run_b1, after_eq run_b0]) (by
          rw [after_eq run_b1]) (by rw [after_eq run_b1]; rfl)
        (by intro r hr; simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
            rw [after_eq run_b1]
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    have hpos : 0 < P.size := by
      rw [hsize]
      exact Nat.pos_of_ne_zero fun h ↦ h0 (UInt64.toNat_inj.mp (by simpa using h))
    refine Eventually.done _ (Or.inr ⟨?_, ?_, hpos, ?_, ?_, ?_, ?_⟩)
    · rw [hpc1]; exact hl4
    · simpa [climbTo_zero] using hfr1
    · rw [UInt64.toNat, hm1.regs .X20 _ rfl, hsize]; rfl
    · apply UInt64.toBitVec_inj.mp
      rw [hm1.regs .X21 _ rfl]; rfl
    · rw [UInt64.toNat, hm1.regs .X22 _ rfl]; rfl
    · rw [hm1.regs .X23 _ rfl]
      sym_simp
      rfl

end

end NativeRustcVmArm.Sumcheck.Climb
