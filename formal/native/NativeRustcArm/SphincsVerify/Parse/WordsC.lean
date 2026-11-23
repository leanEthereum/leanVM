module

public import NativeRustcArm.SphincsVerify.Parse.WordsB

/-!
# The parse, part 5: the second and third layers' words (`b8 .. b10`)

The loop `b8` copies the second layer's words 684 .. 823 to the frame's byte 5868 (35 turns, X8
the offset); `b9` copies the words 824 .. 827, stores the third layer's counter big-endian and
sets up the loop `b10`, which copies the words 829 .. 972 to the frame's byte 7024 (36 turns).
Result: `AtWords` and the raw signature but its last 32 bytes (`pre10`) at `b11` (directive 126).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The raw signature's bytes after `b9`. -/
def pre9 (w : Nat → UInt64) : List UInt8 :=
  pre7 w ++ wb w 684 140 ++ wb w 824 4 ++ be32 (w 828).toUInt32

/-- The raw signature's bytes after `b10`. -/
def pre10 (w : Nat → UInt64) : List UInt8 := pre9 w ++ wb w 829 144

/-- In `b10`'s loop after `j` turns. -/
def Loop10 (r : Run) (j : Nat) (m : MachineData) : Prop :=
  AtWords r m ∧ BytesAt m.dmem (r.off 468) (pre9 r.w ++ wb r.w 829 (4 * j)) ∧
    Run.RegIs m .X8 (r.input + BitVec.ofNat 64 (8 * (832 + 4 * j))) ∧
    Run.RegIs m .X9 (BitVec.ofNat 64 (144 - 4 * j)) ∧
    Run.RegIs m .X10 (BitVec.ofNat 64 (6556 + 32 * j)) ∧ Run.RegIs m .X11 (r.off 468)

end

public section

theorem length_pre9 (w : Nat → UInt64) : (pre9 w).length = 6556 := by
  simp [pre9, length_pre7, length_wb, be32]

theorem length_pre10 (w : Nat → UInt64) : (pre10 w).length = 7708 := by
  simp [pre10, length_pre9, length_wb]

variable (r : Run) [NativeRustcArm.Host]

/-- **A turn of `b8`**. -/
theorem b8_spec (hp : Placed code r.k) (hpre : r.Pre) {j : Nat} (hj : j < 35) {m : MachineData}
    (h : Loop8 r j m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦
      (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b9Offset ∧ AtWords r st.data ∧
        BytesAt st.data.dmem (r.off 468) (pre7 r.w ++ wb r.w 684 140)) ∨
      (j + 1 < 35 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b8Offset ∧ Loop8 r (j + 1) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b8Offset⟩ := by
  obtain ⟨hA, hraw, h8, h9, h10⟩ := h
  have hk : b8.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have h8' : (m.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 (32 * j) := h8
  have h9' : (m.regs.getXReg .X9).toBitVec = r.input + BitVec.ofNat 64 (8 * 687) := h9
  have h10' : (m.regs.getXReg .X10).toBitVec = r.off 468 := h10
  have hm : Match (Env.ofMachine m [(r.off (5868 + 32 * j), 32),
      (r.input + BitVec.ofNat 64 (8 * (684 + 4 * j)), 32)]) loop8S m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl trivial trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs, h10', h8']
        show _ = r.off (5868 + 32 * j) + BitVec.ofInt 64 (-5400)
        refine alias_neg 5400 ?_
        bv_lin, by
        sym_simp
        simp only [Env.ofMachine_regs, h9', h8']
        show _ = r.input + BitVec.ofNat 64 (8 * (684 + 4 * j)) + BitVec.ofInt 64 ((24 : Nat) : Int)
        refine alias_pos 24 ?_
        bv_lin, trivial⟩
  have hwf := wf_frame_input r hpre hA.1.2.2.2.1 hA.1.2.2.2.2 (a := 5868 + 32 * j) (n := 32)
    (s := 684 + 4 * j) (k := 32) (by omega) (by omega) (by decide) (fun _ => 0)
  refine exec_then hk run_b8 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨-, hA', hnew, hout⟩ := copy_turn r hpre hA (d := 5868 + 32 * j) (s := 684 + 4 * j)
    (by omega) (by omega) (by omega) hm hm' (by decide) (by decide) (by decide)
  have hraw' : BytesAt st.data.dmem (r.off 468) (pre7 r.w ++ wb r.w 684 (4 * (j + 1))) := by
    rw [show 4 * (j + 1) = 4 * j + 4 by omega, wb_add, ← List.append_assoc]
    refine BytesAt.append (keep r hpre hraw hout (by rw [List.length_append, length_pre7, length_wb])
      (by left; omega) (by omega) (by omega)) ?_
    rw [List.length_append, length_pre7, length_wb, off_add,
      show 468 + (5400 + 8 * (4 * j)) = 5868 + 32 * j by omega]
    exact hnew
  have h8'' : Run.RegIs st.data .X8 (BitVec.ofNat 64 (32 * (j + 1))) := by
    rw [Run.RegIs, hm'.regs .X8 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, h8']
    bv_lin
  have h9'' : Run.RegIs st.data .X9 (r.input + BitVec.ofNat 64 (8 * 687)) :=
    (hm'.regs .X9 _ rfl).trans h9'
  have h10'' : Run.RegIs st.data .X10 (r.off 468) := (hm'.regs .X10 _ rfl).trans h10'
  simp only [PcOk] at hpc
  sym_simp at hpc
  rw [Env.ofMachine_regs, h8'] at hpc
  split at hpc
  · rename_i hc
    have hj1 : j + 1 < 35 := by
      by_contra hcon
      obtain rfl : j = 34 := by omega
      revert hc
      decide
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_7_at] at hpc
    exact .done _ (Or.inr ⟨hj1, hpc, hA', hraw', h8'', h9'', h10''⟩)
  · rename_i hc
    have hj1 : j = 34 := by
      have hc' : BitVec.ofNat 64 (32 * j) + 32#64 = 1120#64 := by simpa using hc
      have := congrArg BitVec.toNat hc'
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    subst hj1
    exact .done _ (Or.inl ⟨hpc, hA', hraw'⟩)

/-- **The loop `b8`**. -/
theorem b8_loop (hp : Placed code r.k) (hpre : r.Pre) {st : MachineState}
    (h : st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b8Offset ∧ Loop8 r 0 st.data) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b9Offset ∧ AtWords r st.data ∧
      BytesAt st.data.dmem (r.off 468) (pre7 r.w ++ wb r.w 684 140)) st :=
  count_loop (P := fun j st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b8Offset ∧ Loop8 r j st.data) 35
    (fun j st hj ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      exact b8_spec r hp hpre hj h) (by decide) h

/-- **`b9`**: the words 824 .. 827 and the third layer's counter; the loop `b10`'s registers. -/
theorem b9_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m)
    (hraw : BytesAt m.dmem (r.off 468) (pre7 r.w ++ wb r.w 684 140)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b10Offset ∧ Loop10 r 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b9Offset⟩ := by
  have hk : b9.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b9Offset) :=
    b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := straight_wf r hpre hA.1
  have hS := hA.1.2.2.2.1
  refine exec_then hk run_b9 hwf (straight_match r hpre hA) fun st hm' hpc ↦ ?_
  obtain ⟨hA', hout⟩ := atWords_of_block r hpre hA (d := 0) (lo := 6988) (hi := 7024) rfl
    (by decide) (by decide) (by decide) (by decide) (straight_match r hpre hA) hm' hwf (by decide)
    (by decide)
  have h1 := keep r hpre hraw hout (by rw [List.length_append, length_pre7, length_wb])
    (by left; decide) (by decide) (by decide)
  have h2 := copy hm' (r := 0) (o := 6988) (r' := 1) (o' := 6592) (n := 32) rfl (by decide)
    (by decide) (length_wb r.w 824 4)
    (bytesAt_wb' r hpre hS (s := 0) (o := 6592) (k := 824) (n := 4) rfl (by decide))
  have h3 := bytesAt_rev hm' (r := 0) (o := 7020) (r' := 1) (o' := 6624) rfl (by decide) (by decide)
    (word_at r hpre hS (s := 0) (o := 6624) (k := 828) rfl (by decide))
  rw [off_add] at h2 h3
  refine .done _ ⟨hpc, hA', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_zero, show wb r.w 829 0 = [] from rfl, List.append_nil, pre9]
    refine BytesAt.append (BytesAt.append h1 ?_) ?_
    · rw [List.length_append, length_pre7, length_wb, off_add]; exact h2
    · rw [List.length_append, List.length_append, length_pre7, length_wb, length_wb, off_add]
      exact h3
  · rw [Run.RegIs, hm'.regs .X8 _ rfl]
    refine (straight_ptr1 r m 6656).trans ?_
    bv_lin
  · rw [Run.RegIs, hm'.regs .X9 _ rfl]; rfl
  · rw [Run.RegIs, hm'.regs .X10 _ rfl]; rfl
  · rw [Run.RegIs, hm'.regs .X11 _ rfl]; exact straight_ptr0 r m 468

/-- **A turn of `b10`**. -/
theorem b10_spec (hp : Placed code r.k) (hpre : r.Pre) {j : Nat} (hj : j < 36) {m : MachineData}
    (h : Loop10 r j m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦
      (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b11Offset ∧ AtWords r st.data ∧ BytesAt st.data.dmem (r.off 468) (pre10 r.w)) ∨
      (j + 1 < 36 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b10Offset ∧ Loop10 r (j + 1) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b10Offset⟩ := by
  obtain ⟨hA, hraw, h8, h9, h10, h11⟩ := h
  have hk : b10.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b10Offset) :=
    b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have h8' : (m.regs.getXReg .X8).toBitVec = r.input + BitVec.ofNat 64 (8 * (832 + 4 * j)) := h8
  have h9' : (m.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (144 - 4 * j) := h9
  have h10' : (m.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (6556 + 32 * j) := h10
  have h11' : (m.regs.getXReg .X11).toBitVec = r.off 468 := h11
  have hm : Match (Env.ofMachine m [(r.off (7024 + 32 * j), 32),
      (r.input + BitVec.ofNat 64 (8 * (829 + 4 * j)), 32)]) loopPS m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl
      ⟨by
        show (m.regs.getXReg .X8).toBitVec =
          r.input + BitVec.ofNat 64 (8 * (829 + 4 * j)) + BitVec.ofInt 64 ((24 : Nat) : Int)
        rw [h8']
        refine alias_pos 24 ?_
        bv_lin, trivial⟩ trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs, h10', h11']
        show _ = r.off (7024 + 32 * j) + BitVec.ofInt 64 ((0 : Nat) : Int)
        refine alias_pos 0 ?_
        bv_lin, trivial⟩
  have hwf := wf_frame_input r hpre hA.1.2.2.2.1 hA.1.2.2.2.2 (a := 7024 + 32 * j) (n := 32)
    (s := 829 + 4 * j) (k := 32) (by omega) (by omega) (by decide) (fun _ => 0)
  refine exec_then hk run_b10 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨-, hA', hnew, hout⟩ := copy_turn r hpre hA (d := 7024 + 32 * j) (s := 829 + 4 * j)
    (by omega) (by omega) (by omega) hm hm' (by decide) (by decide) (by decide)
  have hraw' : BytesAt st.data.dmem (r.off 468) (pre9 r.w ++ wb r.w 829 (4 * (j + 1))) := by
    rw [show 4 * (j + 1) = 4 * j + 4 by omega, wb_add, ← List.append_assoc]
    refine BytesAt.append (keep r hpre hraw hout (by rw [List.length_append, length_pre9, length_wb])
      (by left; omega) (by omega) (by omega)) ?_
    rw [List.length_append, length_pre9, length_wb, off_add,
      show 468 + (6556 + 8 * (4 * j)) = 7024 + 32 * j by omega]
    exact hnew
  have h8'' : Run.RegIs st.data .X8 (r.input + BitVec.ofNat 64 (8 * (832 + 4 * (j + 1)))) := by
    rw [Run.RegIs, hm'.regs .X8 _ rfl]
    refine (eval_ptr_nat (i := 1) rfl 56).trans ?_
    bv_lin
  have h9'' : Run.RegIs st.data .X9 (BitVec.ofNat 64 (144 - 4 * (j + 1))) := by
    rw [Run.RegIs, hm'.regs .X9 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, h9']
    bv_lin
  have h10'' : Run.RegIs st.data .X10 (BitVec.ofNat 64 (6556 + 32 * (j + 1))) := by
    rw [Run.RegIs, hm'.regs .X10 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, h10']
    bv_lin
  have h11'' : Run.RegIs st.data .X11 (r.off 468) := (hm'.regs .X11 _ rfl).trans h11'
  simp only [PcOk] at hpc
  sym_simp at hpc
  rw [Env.ofMachine_regs, h9'] at hpc
  split at hpc
  · rename_i hc
    have hj1 : j + 1 < 36 := by
      by_contra hcon
      obtain rfl : j = 35 := by omega
      revert hc
      decide
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_9_at] at hpc
    exact .done _ (Or.inr ⟨hj1, hpc, hA', hraw', h8'', h9'', h10'', h11''⟩)
  · rename_i hc
    have hj1 : j = 35 := by
      have hc' : BitVec.ofNat 64 (144 - 4 * j) = 4#64 := by simpa using hc
      have := congrArg BitVec.toNat hc'
      simp only [BitVec.toNat_ofNat] at this
      omega
    subst hj1
    exact .done _ (Or.inl ⟨hpc, hA', hraw'⟩)

/-- **`b9` and the loop `b10`**. -/
theorem b10_loop (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m)
    (hraw : BytesAt m.dmem (r.off 468) (pre7 r.w ++ wb r.w 684 140)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b11Offset ∧ AtWords r st.data ∧
      BytesAt st.data.dmem (r.off 468) (pre10 r.w)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b9Offset⟩ :=
  Eventually.bind (b9_spec r hp hpre hA hraw) fun _ h ↦
    count_loop (P := fun j st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b10Offset ∧ Loop10 r j st.data) 36
      (fun j st hj ⟨hpc, h⟩ ↦ by
        obtain ⟨m, pc⟩ := st
        simp only at hpc
        subst hpc
        exact b10_spec r hp hpre hj h) (by decide) h

/-- **The words' blocks `b3 .. b10`**: from `AtWords` at `b3`, the raw signature but its last
32 bytes, at `b11`. -/
theorem words_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b11Offset ∧ AtWords r st.data ∧
      BytesAt st.data.dmem (r.off 468) (pre10 r.w)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset⟩ := by
  refine Eventually.bind (b4_loop r hp hpre hA) fun st ⟨hpc, hA, hraw⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.bind (b6_loop r hp hpre hA hraw) fun st ⟨hpc, hA, hraw⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.bind (b7_spec r hp hpre hA hraw) fun st h ↦ ?_
  refine Eventually.bind (b8_loop r hp hpre h) fun st ⟨hpc, hA, hraw⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  exact b10_loop r hp hpre hA hraw

end

end NativeRustcArm.SphincsVerifyProof.Parse
