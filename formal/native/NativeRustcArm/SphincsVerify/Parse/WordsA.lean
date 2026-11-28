module

public import NativeRustcArm.SphincsVerify.Parse.Turn
public import NativeRustcArm.SphincsVerify.Parse.WordsExec

/-!
# The parse, part 3: the signature's first words (`b3 .. b7`)

`b3` sets the loop `b4`'s source X8 (the context's byte 1112) and counter X9 (`-4224`); `b4`
copies the words 8 .. 535 to the frame's byte 468 (132 turns of 4 words); `b5` copies the words
536, 537, stores the first layer's counter big-endian, and sets up the loop `b6`, which copies the
first layer's words 539 .. 678 (35 turns); `b7` copies the words 679 .. 682 and stores the second
layer's counter. Result: `Loop8 0` at `b8` (directive 88).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- In `b4`'s loop after `j` turns. -/
def Loop4 (r : Run) (j : Nat) (m : MachineData) : Prop :=
  AtWords r m ∧ BytesAt m.dmem (r.off 468) (wb r.w 8 (4 * j)) ∧
    Run.RegIs m .X8 (r.m0.regs.X0.toBitVec + BitVec.ofNat 64 1112) ∧
    Run.RegIs m .X9 (BitVec.ofNat 64 (2 ^ 64 - 4224 + 32 * j))

/-- The raw signature's bytes after `b5`. -/
def pre5 (w : Nat → UInt64) : List UInt8 := wb w 8 528 ++ wb w 536 2 ++ be32 (w 538).toUInt32

theorem length_pre5 (w : Nat → UInt64) : (pre5 w).length = 4244 := by
  simp [pre5, length_wb, be32]

/-- In `b6`'s loop after `j` turns. -/
def Loop6 (r : Run) (j : Nat) (m : MachineData) : Prop :=
  AtWords r m ∧ BytesAt m.dmem (r.off 468) (pre5 r.w ++ wb r.w 539 (4 * j)) ∧
    Run.RegIs m .X8 (r.input + BitVec.ofNat 64 (8 * (542 + 4 * j))) ∧
    Run.RegIs m .X9 (BitVec.ofNat 64 (140 - 4 * j)) ∧
    Run.RegIs m .X10 (BitVec.ofNat 64 (4244 + 32 * j)) ∧ Run.RegIs m .X11 (r.off 468)

/-- The raw signature's bytes after `b7`. -/
def pre7 (w : Nat → UInt64) : List UInt8 :=
  pre5 w ++ wb w 539 140 ++ wb w 679 4 ++ be32 (w 683).toUInt32

/-- In `b8`'s loop after `j` turns. -/
def Loop8 (r : Run) (j : Nat) (m : MachineData) : Prop :=
  AtWords r m ∧ BytesAt m.dmem (r.off 468) (pre7 r.w ++ wb r.w 684 (4 * j)) ∧
    Run.RegIs m .X8 (BitVec.ofNat 64 (32 * j)) ∧
    Run.RegIs m .X9 (r.input + BitVec.ofNat 64 (8 * 687)) ∧ Run.RegIs m .X10 (r.off 468)

end

public section

variable (r : Run)

theorem length_pre7 (w : Nat → UInt64) : (pre7 w).length = 5400 := by
  simp [pre7, length_pre5, length_wb, be32]

theorem atWords_regs [Labels] {m m' : MachineData} (hA : AtWords r m) (hd : m'.dmem = m.dmem)
    (hsp : m'.regs.SP = m.regs.SP)
    (hreg : ∀ x ∈ wordRegs, m'.regs.getXReg x = m.regs.getXReg x) : AtWords r m' := by
  obtain ⟨hF, hmsg, h19, h20, h21, h22, h23, h24, h25⟩ := hA
  have e : ∀ x ∈ wordRegs, ∀ v, Run.RegIs m x v → Run.RegIs m' x v := fun x hx v h => by
    unfold Run.RegIs at *
    rw [hreg x hx]
    exact h
  exact ⟨hF.of_block (by rw [hsp]; exact hF.1) (by rw [hreg .X29 (by simp)]; exact hF.2.1)
      (R := fun _ => False) (fun p _ => by rw [hd]) (fun _ h => h.elim) (fun p h => by rw [hd]; exact h),
    hd ▸ hmsg, e .X19 (by simp) _ h19, e .X20 (by simp) _ h20, e .X21 (by simp) _ h21,
    e .X22 (by simp) _ h22, e .X23 (by simp) _ h23, e .X24 (by simp) _ h24, e .X25 (by simp) _ h25⟩

variable [NativeRustcArm.Host]

/-- **`b3`**: the loop's source and counter. -/
theorem b3_spec (hp : Placed code r.k) {m : MachineData} (hA : AtWords r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b4Offset ∧ Loop4 r 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset⟩ := by
  have hk : b3.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := Env.wf_nil m
  refine exec_then hk run_b3 hwf (match_nil m) fun st hm' hpc ↦ .done _ ⟨hpc, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hsp, hreg⟩ := keepsRegs_regs (rs := wordRegs) (match_nil m) hm' (by decide)
    exact atWords_regs r hA (hm'.dmem_eq hwf rfl) hsp hreg
  · intro i hi; simp [wb, Native.Keccak.wordsBytes] at hi
  · rw [Run.RegIs, hm'.regs .X8 _ rfl]
    have h19 := hA.2.2.1
    simp only [Run.RegIs] at h19
    sym_simp
    rw [Env.ofMachine_regs, h19]
  · rw [Run.RegIs, hm'.regs .X9 _ rfl]
    rfl

/-- **A turn of `b4`**. -/
theorem b4_spec (hp : Placed code r.k) (hpre : r.Pre) {j : Nat} (hj : j < 132) {m : MachineData}
    (h : Loop4 r j m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦
      (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b5Offset ∧ AtWords r st.data ∧ BytesAt st.data.dmem (r.off 468) (wb r.w 8 528)) ∨
      (j + 1 < 132 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b4Offset ∧ Loop4 r (j + 1) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b4Offset⟩ := by
  obtain ⟨hA, hraw, h8, h9⟩ := h
  have hk : b4.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have h20 : (m.regs.getXReg .X20).toBitVec = r.off 468 := hA.2.2.2.1
  have h8' : (m.regs.getXReg .X8).toBitVec = r.m0.regs.X0.toBitVec + BitVec.ofNat 64 1112 := h8
  have h9' : (m.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 4224 + 32 * j) := h9
  have hm : Match (Env.ofMachine m [(r.off (468 + 32 * j), 32),
      (r.input + BitVec.ofNat 64 (8 * (8 + 4 * j)), 32)]) loop4S m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl trivial trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs, h20, h9']
        show _ = r.off (468 + 32 * j) + BitVec.ofInt 64 (-4224)
        refine alias_neg 4224 ?_
        bv_lin, by
        sym_simp
        simp only [Env.ofMachine_regs, h8', h9']
        show _ = r.input + BitVec.ofNat 64 (8 * (8 + 4 * j)) + BitVec.ofInt 64 (-4200)
        refine alias_neg 4200 ?_
        bv_lin, trivial⟩
  have hwf := wf_frame_input r hpre hA.1.2.2.2.1 hA.1.2.2.2.2 (a := 468 + 32 * j) (n := 32)
    (s := 8 + 4 * j) (k := 32) (by omega) (by omega) (by decide) (fun _ => 0)
  refine exec_then hk run_b4 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨-, hA', hnew, hout⟩ := copy_turn r hpre hA (d := 468 + 32 * j) (s := 8 + 4 * j)
    (by omega) (by omega) (by omega) hm hm' (by decide) (by decide) (by decide)
  have hraw' : BytesAt st.data.dmem (r.off 468) (wb r.w 8 (4 * (j + 1))) := by
    rw [show 4 * (j + 1) = 4 * j + 4 by omega, wb_add]
    refine BytesAt.append (keep r hpre hraw hout (length_wb _ _ _) (by left; omega) (by omega)
      (by omega)) ?_
    rw [length_wb, off_add, show 468 + 8 * (4 * j) = 468 + 32 * j by omega]
    exact hnew
  have h8'' : Run.RegIs st.data .X8 (r.m0.regs.X0.toBitVec + BitVec.ofNat 64 1112) :=
    (hm'.regs .X8 _ rfl).trans h8'
  have h9'' : Run.RegIs st.data .X9 (BitVec.ofNat 64 (2 ^ 64 - 4224 + 32 * (j + 1))) := by
    rw [Run.RegIs, hm'.regs .X9 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, h9']
    bv_lin
  simp only [PcOk] at hpc
  sym_simp at hpc
  rw [Env.ofMachine_regs, h9'] at hpc
  split at hpc
  · rename_i hc
    have hj1 : j + 1 < 132 := by
      by_contra hcon
      obtain rfl : j = 131 := by omega
      revert hc
      decide
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_3_at] at hpc
    exact .done _ (Or.inr ⟨hj1, hpc, hA', hraw', h8'', h9''⟩)
  · rename_i hc
    have hj1 : j = 131 := by
      have hc' : BitVec.ofNat 64 (2 ^ 64 - 4224 + 32 * j) + 32#64 = 0#64 := by simpa using hc
      have := congrArg BitVec.toNat hc'
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    subst hj1
    exact .done _ (Or.inl ⟨hpc, hA', hraw'⟩)

/-- **`b3` and the loop `b4`**: the words 8 .. 535. -/
theorem b4_loop (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b5Offset ∧ AtWords r st.data ∧
      BytesAt st.data.dmem (r.off 468) (wb r.w 8 528)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset⟩ :=
  Eventually.bind (b3_spec r hp hA) fun _ h ↦
    count_loop (P := fun j st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b4Offset ∧ Loop4 r j st.data) 132
      (fun j st hj ⟨hpc, h⟩ ↦ by
        obtain ⟨m, pc⟩ := st
        simp only at hpc
        subst hpc
        exact b4_spec r hp hpre hj h) (by decide) h

/-- The frame and the input, for `b5`, `b7`, `b9`, `b11`. -/
abbrev straightEnv (m : MachineData) : Env :=
  Env.ofMachine m [(r.off 0, 29376), (r.input + BitVec.ofNat 64 (8 * 0), 7816)]

theorem straight_ptr1 (m : MachineData) (o : Nat) :
    Sym.eval (straightEnv r m) (.ptr 1 (o : Int)) = r.input + BitVec.ofNat 64 (8 * 0) + BitVec.ofNat 64 o :=
  eval_ptr_nat rfl o

theorem straight_ptr0 (m : MachineData) (o : Nat) :
    Sym.eval (straightEnv r m) (.ptr 0 (o : Int)) = r.off o :=
  (eval_ptr_off r (i := 0) rfl o).trans (by rw [Nat.zero_add])

theorem straight_wf (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) : (straightEnv r m).WF :=
  wf_frame_input r hpre hF.2.2.2.1 hF.2.2.2.2 (a := 0) (n := 29376) (s := 0) (k := 7816)
    (by decide) (by decide) (by decide) (fun _ => 0)

theorem straight_match (hpre : r.Pre) {m : MachineData} (hA : AtWords r m) :
    Match (straightEnv r m) straightS m :=
  match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by decide) (by decide),
      ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩⟩
    (hA.1.1.trans ((eval_ptr_off r (i := 0) rfl 0).trans (Run.off_zero r)).symm)
    ⟨hA.2.2.1.trans ((eval_ptr (i := 1) rfl _).trans (input_sub r)).symm,
      hA.2.2.2.1.trans (eval_ptr_off r (i := 0) rfl 468).symm,
      hA.2.2.2.2.2.2.2.2.trans (eval_ptr_off r (i := 0) rfl 4564).symm,
      hA.1.2.1.trans (eval_ptr_off r (i := 0) rfl 29280).symm, trivial⟩
    trivial trivial trivial

/-- **`b5`**: the words 536, 537 and the first layer's counter; the loop `b6`'s registers. -/
theorem b5_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m)
    (hraw : BytesAt m.dmem (r.off 468) (wb r.w 8 528)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b6Offset ∧ Loop6 r 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b5Offset⟩ := by
  have hk : b5.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := straight_wf r hpre hA.1
  have hS := hA.1.2.2.2.1
  refine exec_then hk run_b5 hwf (straight_match r hpre hA) fun st hm' hpc ↦ ?_
  obtain ⟨hA', hout⟩ := atWords_of_block r hpre hA (d := 0) (lo := 4692) (hi := 4712) rfl
    (by decide) (by decide) (by decide) (by decide) (straight_match r hpre hA) hm' hwf (by decide)
    (by decide)
  have h1 := keep r hpre hraw hout (length_wb _ _ _) (by left; decide) (by decide) (by decide)
  have h2 := copy hm' (r := 0) (o := 4692) (r' := 1) (o' := 4288) (n := 16) rfl (by decide)
    (by decide) (length_wb r.w 536 2)
    (bytesAt_wb' r hpre hS (s := 0) (o := 4288) (k := 536) (n := 2) rfl (by decide))
  have h3 := bytesAt_rev hm' (r := 0) (o := 4708) (r' := 1) (o' := 4304) rfl (by decide) (by decide)
    (word_at r hpre hS (s := 0) (o := 4304) (k := 538) rfl (by decide))
  rw [off_add] at h2 h3
  refine .done _ ⟨hpc, hA', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_zero, show wb r.w 539 0 = [] from rfl, List.append_nil, pre5]
    refine BytesAt.append (BytesAt.append h1 ?_) ?_
    · rw [length_wb, off_add]; exact h2
    · rw [List.length_append, length_wb, length_wb, off_add]; exact h3
  · rw [Run.RegIs, hm'.regs .X8 _ rfl]
    refine (straight_ptr1 r m 4336).trans ?_
    bv_lin
  · rw [Run.RegIs, hm'.regs .X9 _ rfl]; rfl
  · rw [Run.RegIs, hm'.regs .X10 _ rfl]; rfl
  · rw [Run.RegIs, hm'.regs .X11 _ rfl]; exact straight_ptr0 r m 468

end

end NativeRustcArm.SphincsVerifyProof.Parse
