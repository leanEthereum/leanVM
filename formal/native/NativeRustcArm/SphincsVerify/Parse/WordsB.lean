module

public import NativeRustcArm.SphincsVerify.Parse.WordsA

/-!
# The parse, part 4: the first layer's words (`b6`, `b7`)

The loop `b6` copies the first layer's words 539 .. 678 to the frame's byte 4712 (35 turns of 4
words, X8 the source's end, X9 the words left, X10 the destination's offset from X11); `b7` copies
the words 679 .. 682, stores the second layer's counter big-endian and sets up the loop `b8`.
Result: `Loop8 0` at `b8` (directive 88).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

public section

variable (r : Run) [NativeRustcArm.Host]

/-- **A turn of `b6`**. -/
theorem b6_spec (hp : Placed code r.k) (hpre : r.Pre) {j : Nat} (hj : j < 35) {m : MachineData}
    (h : Loop6 r j m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦
      (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset ∧ AtWords r st.data ∧
        BytesAt st.data.dmem (r.off 468) (pre5 r.w ++ wb r.w 539 140)) ∨
      (j + 1 < 35 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b6Offset ∧ Loop6 r (j + 1) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b6Offset⟩ := by
  obtain ⟨hA, hraw, h8, h9, h10, h11⟩ := h
  have hk : b6.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have h8' : (m.regs.getXReg .X8).toBitVec = r.input + BitVec.ofNat 64 (8 * (542 + 4 * j)) := h8
  have h9' : (m.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (140 - 4 * j) := h9
  have h10' : (m.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (4244 + 32 * j) := h10
  have h11' : (m.regs.getXReg .X11).toBitVec = r.off 468 := h11
  have hm : Match (Env.ofMachine m [(r.off (4712 + 32 * j), 32),
      (r.input + BitVec.ofNat 64 (8 * (539 + 4 * j)), 32)]) loopPS m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl
      ⟨by
        show (m.regs.getXReg .X8).toBitVec =
          r.input + BitVec.ofNat 64 (8 * (539 + 4 * j)) + BitVec.ofInt 64 ((24 : Nat) : Int)
        rw [h8']
        refine alias_pos 24 ?_
        bv_lin, trivial⟩ trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs, h10', h11']
        show _ = r.off (4712 + 32 * j) + BitVec.ofInt 64 ((0 : Nat) : Int)
        refine alias_pos 0 ?_
        bv_lin, trivial⟩
  have hwf := wf_frame_input r hpre hA.1.2.2.2.1 hA.1.2.2.2.2 (a := 4712 + 32 * j) (n := 32)
    (s := 539 + 4 * j) (k := 32) (by omega) (by omega) (by decide) (fun _ => 0)
  refine exec_then hk run_b6 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨-, hA', hnew, hout⟩ := copy_turn r hpre hA (d := 4712 + 32 * j) (s := 539 + 4 * j)
    (by omega) (by omega) (by omega) hm hm' (by decide) (by decide) (by decide)
  have hraw' : BytesAt st.data.dmem (r.off 468) (pre5 r.w ++ wb r.w 539 (4 * (j + 1))) := by
    rw [show 4 * (j + 1) = 4 * j + 4 by omega, wb_add, ← List.append_assoc]
    refine BytesAt.append (keep r hpre hraw hout (by rw [List.length_append, length_pre5, length_wb])
      (by left; omega) (by omega) (by omega)) ?_
    rw [List.length_append, length_pre5, length_wb, off_add,
      show 468 + (4244 + 8 * (4 * j)) = 4712 + 32 * j by omega]
    exact hnew
  have h8'' : Run.RegIs st.data .X8 (r.input + BitVec.ofNat 64 (8 * (542 + 4 * (j + 1)))) := by
    rw [Run.RegIs, hm'.regs .X8 _ rfl]
    refine (eval_ptr_nat (i := 1) rfl 56).trans ?_
    bv_lin
  have h9'' : Run.RegIs st.data .X9 (BitVec.ofNat 64 (140 - 4 * (j + 1))) := by
    rw [Run.RegIs, hm'.regs .X9 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, h9']
    bv_lin
  have h10'' : Run.RegIs st.data .X10 (BitVec.ofNat 64 (4244 + 32 * (j + 1))) := by
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
    have hj1 : j + 1 < 35 := by
      by_contra hcon
      obtain rfl : j = 34 := by omega
      revert hc
      decide
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_5_at] at hpc
    exact .done _ (Or.inr ⟨hj1, hpc, hA', hraw', h8'', h9'', h10'', h11''⟩)
  · rename_i hc
    have hj1 : j = 34 := by
      have hc' : BitVec.ofNat 64 (140 - 4 * j) = 4#64 := by simpa using hc
      have := congrArg BitVec.toNat hc'
      simp only [BitVec.toNat_ofNat] at this
      omega
    subst hj1
    exact .done _ (Or.inl ⟨hpc, hA', hraw'⟩)

/-- **`b5` and the loop `b6`**. -/
theorem b6_loop (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m)
    (hraw : BytesAt m.dmem (r.off 468) (wb r.w 8 528)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset ∧ AtWords r st.data ∧
      BytesAt st.data.dmem (r.off 468) (pre5 r.w ++ wb r.w 539 140)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b5Offset⟩ :=
  Eventually.bind (b5_spec r hp hpre hA hraw) fun _ h ↦
    count_loop (P := fun j st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b6Offset ∧ Loop6 r j st.data) 35
      (fun j st hj ⟨hpc, h⟩ ↦ by
        obtain ⟨m, pc⟩ := st
        simp only at hpc
        subst hpc
        exact b6_spec r hp hpre hj h) (by decide) h

/-- **`b7`**: the words 679 .. 682 and the second layer's counter; the loop `b8`'s registers. -/
theorem b7_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m)
    (hraw : BytesAt m.dmem (r.off 468) (pre5 r.w ++ wb r.w 539 140)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b8Offset ∧ Loop8 r 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset⟩ := by
  have hk : b7.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := straight_wf r hpre hA.1
  have hS := hA.1.2.2.2.1
  refine exec_then hk run_b7 hwf (straight_match r hpre hA) fun st hm' hpc ↦ ?_
  obtain ⟨hA', hout⟩ := atWords_of_block r hpre hA (d := 0) (lo := 5832) (hi := 5868) rfl
    (by decide) (by decide) (by decide) (by decide) (straight_match r hpre hA) hm' hwf (by decide)
    (by decide)
  have h1 := keep r hpre hraw hout (by rw [List.length_append, length_pre5, length_wb])
    (by left; decide) (by decide) (by decide)
  have h2 := copy hm' (r := 0) (o := 5832) (r' := 1) (o' := 5432) (n := 32) rfl (by decide)
    (by decide) (length_wb r.w 679 4)
    (bytesAt_wb' r hpre hS (s := 0) (o := 5432) (k := 679) (n := 4) rfl (by decide))
  have h3 := bytesAt_rev hm' (r := 0) (o := 5864) (r' := 1) (o' := 5464) rfl (by decide) (by decide)
    (word_at r hpre hS (s := 0) (o := 5464) (k := 683) rfl (by decide))
  rw [off_add] at h2 h3
  refine .done _ ⟨hpc, hA', ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_zero, show wb r.w 684 0 = [] from rfl, List.append_nil, pre7]
    refine BytesAt.append (BytesAt.append h1 ?_) ?_
    · rw [List.length_append, length_pre5, length_wb, off_add]; exact h2
    · rw [List.length_append, List.length_append, length_pre5, length_wb, length_wb, off_add]
      exact h3
  · rw [Run.RegIs, hm'.regs .X8 _ rfl]; rfl
  · rw [Run.RegIs, hm'.regs .X9 _ rfl]
    refine (straight_ptr1 r m 5496).trans ?_
    bv_lin
  · rw [Run.RegIs, hm'.regs .X10 _ rfl]; exact straight_ptr0 r m 468

end

end NativeRustcArm.SphincsVerifyProof.Parse
