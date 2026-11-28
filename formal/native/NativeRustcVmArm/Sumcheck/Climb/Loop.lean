module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Sumcheck.Climb.Call

/-!
# `climb`'s loop

After `hash_pair`, `b4` copies the new digest over the accumulator, halves the position, counts
the level, and leaves for `.LClimb_8` after the last level or goes back to the loop head
(`b4_spec`). The loop (`loop_spec`): from the head, at `.LClimb_8` with the frame holding
`climb N q P`.
-/

namespace NativeRustcVmArm.Sumcheck.Climb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Climb
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck

public section

variable [Host] {N : Digest} {P : Array Digest} {m0 : MachineData} {k : Nat}

/-- **After `hash_pair`**: the next level's loop head, or the exit after the last. -/
theorem b4_spec (hp : Placed code k) (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData}
    (hc : Called m0 N P l m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset) ∧ l + 1 = P.size ∧
          Frame m0 (climbTo N m0.regs.X2 P (l + 1)).1 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b5Offset) ∧ Inv m0 N P (l + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b4Offset)⟩ := by
  have ⟨gfr, gstk, gle, glt, gal⟩ := fr_geo hpre
  have hl := hc.lt
  have h32 : P.size ≤ 32 := by
    have h1 : P.size = m0.regs.X4.toNat := hpre.2.2.2.1
    have h2 : m0.regs.X4.toNat ≤ 32 := hpre.2.2.1
    omega
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b4Offset) := b4_in_code.trans hp.1 (by simp [b4])
  have hl8 : Labels.label NativeRustcVmArm.Vm.Climb.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset) := hp.label (j := NativeRustcVmArm.Vm.Climb.b10Offset) NativeRustcVmArm.Vm.Climb.label_8_at
  let env := Env.ofMachine m [(fr m0, 144)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨mapped_fr hpre hc.kept, by show _ + 144 ≤ _; rw [gfr]; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env retS m :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [gfr]; omega, trivial⟩ (by simp [Sym.eval, hc.sp])
      trivial trivial trivial trivial
  have hb0 : env.base 0 = fr m0 := rfl
  refine exec_then hk4 run_b4 hwf hm fun st hm' hpc ↦ ?_
  have hmA : Match env (after b4 retS) st.data := by rw [after_eq run_b4]; exact hm'
  -- The new accumulator.
  have hfrN : ∀ o, o ≤ 144 → (fr m0 + BitVec.ofNat 64 o).toNat = (fr m0).toNat + o :=
    fun o ho ↦ NativeRustcVm.toNat_add_ofNat (by omega)
  have hW : ∀ p, Written env (after b4 retS) p → (fr m0).toNat ≤ p.toNat ∧
      p.toNat < (fr m0).toNat + 32 :=
    fun p h ↦ by
      have := Written.toNat (r := 0) (lo := 0) (hi := 32) rfl
        (by rw [after_eq run_b4]; decide +kernel) h
      omega
  have hst : ∀ p, ¬((fr m0).toNat ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 32) →
      st.data.dmem.get? p = m.dmem.get? p :=
    fun p hp ↦ hmA.get?_mem0 hwf fun h ↦ hp (hW p h)
  have hacc : NativeRustcVm.WordsAt st.data.dmem (fr m0)
      (climbTo N m0.regs.X2 P (l + 1)).1.toList := by
    have hw : ∀ i < 4, ∀ j < 8,
        findWrite 0 (8 * i + j) (after b4 retS).mem = some (.load 0 (64 + 8 * i) 8, j) := by
      rw [after_eq run_b4]; decide +kernel
    rw [NativeRustcVm.wordsAt_iff]
    intro i hi
    simp only [Vector.length_toList] at hi
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hmA (r := 0) (o := 8 * i) rfl
      (by omega) (hw i hi)
    rw [show (Sym.load 0 (64 + 8 * i) 8).eval env = env.load 0 (64 + 8 * i) 8 from rfl,
      load_word (by
        rw [hb0, ← NativeRustcVm.addr_add_add]
        exact hc.hashed.getElem (i := i) (by simpa using hi))] at this
    exact this
  have hslots : NativeRustcVm.WordsAt st.data.dmem (fr m0 + BitVec.ofNat 64 96) (slotWords m0) :=
    NativeRustcVm.BytesAt.of_sameOutside hc.slots (R := fun p ↦
      (fr m0).toNat ≤ p.toNat ∧ p.toNat < (fr m0).toNat + 32) (fun p hp ↦ hst p hp)
      fun i hi ↦ by
        rw [NativeRustcVm.length_wordsBytes] at hi
        simp only [slotWords, List.length_cons, List.length_nil] at hi
        rw [NativeRustcVm.addr_add_add, hfrN _ (by omega)]
        omega
  have hkeep : ∀ r ∈ [XReg.X19] ++ outer, st.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    apply UInt64.toBitVec_inj.mp
    refine (hmA.regs r (.reg r) ?_).trans rfl
    simp only [outer, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rw [after_eq run_b4]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hfr : Frame m0 (climbTo N m0.regs.X2 P (l + 1)).1 st.data := by
    refine ⟨?_, ?_, hacc, hslots, fun r hr ↦ ?_, fun p hp ↦ ?_,
      fun p h ↦ hmA.kept hwf p (hc.kept p h)⟩
    · rw [hmA.sp]; rw [after_eq run_b4]; simp [Sym.eval, hb0]
    · rw [hkeep .X19 (by simp)]; exact hc.x19
    · rw [hkeep r (by simp [hr])]; exact hc.regs r hr
    · have hp' : ¬(m0.regs.SP.toNat - 912 ≤ p.toNat ∧ p.toNat < m0.regs.SP.toNat) := by
        rw [Sym.inRange_iff (by rw [gstk, climbStack_eq]; omega), gstk, climbStack_eq] at hp
        omega
      rw [hst p (by omega)]
      exact hc.same p hp
  have hreg : ∀ (r : XReg) (v : Sym), (after b4 retS).reg r = some v →
      (st.data.regs.getXReg r).toBitVec = v.eval env := fun r v h ↦ hmA.regs r v h
  have h20 : (m.regs.getXReg .X20).toNat = P.size - l := hc.x20
  have hx20 : (env.regs .X20) = BitVec.ofNat 64 (P.size - l) := by
    show (m.regs.getXReg .X20).toBitVec = _
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, h20, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc1 : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X20) (.lit 1)).eval env =
      decide (l + 1 = P.size) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, hx20]
    by_cases h : l + 1 = P.size
    · simp [show P.size - l = 1 by omega, h]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      simp at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
  simp only [PcOk, hc1] at hpc
  by_cases hend : l + 1 = P.size
  · simp only [hend, decide_true, ↓reduceIte, hl8] at hpc
    exact Eventually.done _ (Or.inl ⟨hpc, hend, hfr⟩)
  · simp only [hend, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc
    refine Eventually.done _ (Or.inr ⟨by rw [hpc]; rfl, ?_, by omega, ?_, ?_, ?_, ?_⟩)
    · exact hfr
    · have := hreg .X20 _ (by rw [after_eq run_b4]; rfl)
      sym_simp at this
      rw [UInt64.toNat, this, hx20, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    · apply UInt64.toBitVec_inj.mp
      have := hreg .X21 _ (by rw [after_eq run_b4]; rfl)
      sym_simp at this
      rw [this, climbTo_succ _ _ _ hl, climbStep]
      show (UInt64.ofBitVec (evalUBFM (w := .W64) (m.regs.getXReg .X21).toBitVec 1 63)).toBitVec = _
      rw [hc.x21, evalUBFM_half]
    · have := hreg .X22 _ (by rw [after_eq run_b4]; rfl)
      sym_simp at this
      rw [UInt64.toNat, this, BitVec.toNat_add]
      show ((m.regs.getXReg .X22).toBitVec.toNat + 4 % 2 ^ 64) % 2 ^ 64 = _
      rw [UInt64.toNat_toBitVec, hc.x22]
      omega
    · have := hreg .X23 _ (by rw [after_eq run_b4]; rfl)
      sym_simp at this
      rw [this]
      show (m.regs.getXReg .X23).toBitVec + 32#64 = _
      rw [hc.x23, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

/-- **The loop**: from the head, at `.LClimb_8` with `climb N q P` in the frame. -/
theorem loop_spec (hp : Placed code k)
    (hhp : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset) ∧ Frame m0 (climb N m0.regs.X2 P) st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b5Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b5Offset) ∧
      ∃ l, P.size - l = n ∧ Inv m0 N P l st.data) (fun n st ⟨hpc, l, hn, hi⟩ ↦ ?_)
    ⟨rfl, l, rfl, hinv⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  have hl := hi.lt
  refine Eventually.bind (call_spec hp hhp hpre hi) fun st ⟨hpc, hc⟩ ↦ ?_
  obtain ⟨d', pc'⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (b4_spec hp hpre hc) fun st h ↦ ?_
  rcases h with ⟨hpc, hend, hfr⟩ | ⟨hpc, hinv'⟩
  · refine Or.inl ⟨hpc, ?_⟩
    rw [← climbTo_size, ← hend]
    exact hfr
  · exact Or.inr ⟨P.size - (l + 1), by omega, hpc, l + 1, rfl, hinv'⟩

end

end NativeRustcVmArm.Sumcheck.Climb
