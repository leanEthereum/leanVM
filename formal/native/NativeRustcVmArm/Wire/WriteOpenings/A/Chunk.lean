module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Copy

/-!
# `write_openings`' leaf copy loops (`h > 0`)

Four words at a time (`chunk_loop`, `b9`, then `b10`): the leaf copied, or its last words set up;
one word at a time (`rem_loop`, `b12`): the leaf copied.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j i : Nat} [Host]

/-- **Four words at a time** (`b9`, `b10`). -/
theorem chunk_loop (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : ChunkA R j i t st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtB13 R j i st' ∨ AtB11 R j i (q4 R.lw) st') st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = q4 R.lw - t ∧ ChunkA R j i t st) (fun n st ⟨t, hn, H⟩ ↦ ?_)
    ⟨t, rfl, H⟩
  have C := H.c
  have hlw := G.lw64
  have hj := C.lt
  have hi := C.ilt
  have tq := H.tq
  have t4 := H.t4
  have hq : q4 R.lw ≤ R.lw := by unfold q4; omega
  have hin1 := leaf_inside G hi (t := t) (n := 32) (by omega) (by omega)
  have hin2 := opening_inside G hj (t := t) (n := 32) (by omega) (by omega)
  have hwf := G.wf2 C.fr.kept (i := 4) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin1 hin2
  have hm : Match (envOf R st.data [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32),
      (R.oa (ob j + 8 + 8 * t), 32)]) (cpS 32 .X9 16 .X10 24) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [C.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x9, base1, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
          NativeRustcVm.addr_add_add], by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x10, base2, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
          NativeRustcVm.addr_add_add]
        show R.out + _ = R.out + _
        congr 2
        omega, trivial⟩
  refine run_block G hp b9_in_code (by simp [b9]) run_b9 C.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j + 8 + 8 * t)) 32) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 32) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have hon : ob j + 8 + 8 * t + 32 ≤ phaseBytes := by omega
  have w0 := copied hm1 (r := 2) (o := 0) (sz := 32) (r' := 1) (o' := 0) rfl (by omega)
    (by decide)
  have w1 := copied hm1 (r := 2) (o := 8) (sz := 32) (r' := 1) (o' := 8) rfl (by omega)
    (by decide)
  have w2 := copied hm1 (r := 2) (o := 16) (sz := 32) (r' := 1) (o' := 16) rfl (by omega)
    (by decide)
  have w3 := copied hm1 (r := 2) (o := 24) (sz := 32) (r' := 1) (o' := 24) rfl (by omega)
    (by decide)
  simp only [Env.ofMachine_mem0, base1] at w0 w1 w2 w3
  obtain ⟨hmem, hleaf⟩ := G.copy4 hj (by omega) hs C.mem C.leaf
    (leaf_copied G C.fr (u := 0) hi (by omega) w0) (leaf_copied G C.fr (u := 1) hi (by omega) w1)
    (leaf_copied G C.fr (u := 2) hi (by omega) w2) (leaf_copied G C.fr (u := 3) hi (by omega) w3)
  have hk1 := regs_keep hm hm1 (rs := .X8 :: cpRegs) (by decide)
  have C1 : CopyA R j i (t + 4) s1.data :=
    ⟨hfr1, C.cs.keep fun r hr ↦ hk1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h <;> simp [h]), C.cr.keep fun r hr ↦ hk1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h]), by rw [hk1 .X25 (by simp)]; exact C.x25, hj, hi,
      C.h0, C.pos, G.w1_keep hs hon C.w1, hmem, hleaf, by omega⟩
  have x8 : rv s1.data .X8 = R.lv + BitVec.ofNat 64 (512 * i) := by
    rw [hk1 .X8 (by simp)]; exact H.x8
  have x11 : rv st.data .X11 = BitVec.ofNat 64 (q4 R.lw - t) := H.x11
  have hc : (SBool.cmp .eq .W64 (.reg .X11) (.lit 4)).not.eval (envOf R st.data
      [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32), (R.oa (ob j + 8 + 8 * t), 32)]) =
      decide (t + 4 ≠ q4 R.lw) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x11, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    by_cases h : t + 4 = q4 R.lw
    · rw [decide_eq_true (by omega : q4 R.lw - t = 4),
        decide_eq_false (by omega : ¬t + 4 ≠ q4 R.lw)]
      rfl
    · rw [decide_eq_false (by omega : ¬q4 R.lw - t = 4),
        decide_eq_true (by omega : t + 4 ≠ q4 R.lw)]
      rfl
  simp only [PcOk, hc] at hpc1
  by_cases hl : t + 4 = q4 R.lw
  · simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    -- `b10`
    have hwf2 := G.wf0 hfr1.kept
    have hm2 := frMatch G hfr1
    refine run_block G hp b10_in_code (by simp [b10]) run_b10 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hk2 := regs_keep hm2 hm2' (rs := .X8 :: cpRegs) (by decide)
    have C2 : CopyA R j i (t + 4) s2.data :=
      C1.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr)
    have hc2 : (SBool.cmp .eq .W64 (.reg .X21) (.reg .X15)).eval (envOf R s1.data []) =
        decide (R.lw = q4 R.lw) := by
      simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
      rw [C1.cs.x21, C1.cr.x15, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    simp only [PcOk, hc2] at hpc2
    by_cases he : R.lw = q4 R.lw
    · rw [decide_eq_true he] at hpc2
      simp only [↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b13Offset) NativeRustcVmArm.Vm.WriteOpenings.label_12_at] at hpc2
      refine .done _ (.inl (.inl ⟨hpc2, ?_⟩))
      rw [show R.lw = t + 4 by omega]
      exact C2
    · rw [decide_eq_false he] at hpc2
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
      refine .done _ (.inl (.inr ⟨hpc2.trans (congrArg Host.addrOf rfl), hl ▸ C2,
        by rw [hk2 .X8 (by simp)]; exact x8, ?_, by omega⟩))
      rw [hm2'.regs .X10 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [C1.cs.x21, and124 (by omega)]
  · simp only [hl, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b9Offset) NativeRustcVmArm.Vm.WriteOpenings.label_8_at]
      at hpc1
    refine .done _ (.inr ⟨q4 R.lw - (t + 4), by omega, t + 4, rfl, hpc1, C1, x8, ?_, ?_, ?_,
      by omega, by unfold q4 at *; omega⟩)
    · rw [hm1.regs .X9 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x9]
      exact addr_add (by omega)
    · rw [hm1.regs .X10 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x10]
      exact addr_add (by omega)
    · rw [hm1.regs .X11 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [x11, ofNat_sub (by omega)]
      congr 1

/-- **One word at a time** (`b12`). -/
theorem rem_loop (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : RemA R j i t st) : Eventually (step1 Host.exe) (AtB13 R j i) st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = R.lw - t ∧ RemA R j i t st) (fun n st ⟨t, hn, H⟩ ↦ ?_)
    ⟨t, rfl, H⟩
  have C := H.c
  have hlw := G.lw64
  have hj := C.lt
  have hi := C.ilt
  have ht := H.tlt
  have hin1 := leaf_inside G hi (t := t) (n := 8) (by omega) (by omega)
  have hin2 := opening_inside G hj (t := t) (n := 8) (by omega) (by omega)
  have hwf := G.wf2 C.fr.kept (i := 4) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin1 hin2
  have hm : Match (envOf R st.data [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 8),
      (R.oa (ob j + 8 + 8 * t), 8)]) (cpS 8 .X8 0 .X9 0) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [C.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x8, base1, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x9, base2, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine run_block G hp b12_in_code (by simp [b12]) run_b12 C.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j + 8 + 8 * t)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have hon : ob j + 8 + 8 * t + 8 ≤ phaseBytes := by omega
  have w0 := copied hm1 (r := 2) (o := 0) (sz := 8) (r' := 1) (o' := 0) rfl (by omega)
    (by decide)
  simp only [Env.ofMachine_mem0, base1] at w0
  obtain ⟨hmem, hleaf⟩ := G.copy1 hj (by omega) hs C.mem C.leaf
    (leaf_copied G C.fr (u := 0) hi (by omega) w0)
  have hk1 := regs_keep hm hm1 (rs := cpRegs) (by decide)
  have C1 : CopyA R j i (t + 1) s1.data :=
    ⟨hfr1, C.cs.keep fun r hr ↦ hk1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h <;> simp [h]), C.cr.keep fun r hr ↦ hk1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h]), by rw [hk1 .X25 (by simp)]; exact C.x25, hj, hi,
      C.h0, C.pos, G.w1_keep hs hon C.w1, hmem, hleaf, by omega⟩
  have x10 : rv st.data .X10 = BitVec.ofNat 64 (R.lw - t) := H.x10
  have hc : (SBool.cmp .eq .W64 (.reg .X10) (.lit 1)).not.eval (envOf R st.data
      [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 8), (R.oa (ob j + 8 + 8 * t), 8)]) =
      decide (t + 1 ≠ R.lw) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x10, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    by_cases h : t + 1 = R.lw
    · rw [decide_eq_true (by omega : R.lw - t = 1), decide_eq_false (by omega : ¬t + 1 ≠ R.lw)]
      rfl
    · rw [decide_eq_false (by omega : ¬R.lw - t = 1), decide_eq_true (by omega : t + 1 ≠ R.lw)]
      rfl
  simp only [PcOk, hc] at hpc1
  by_cases hl : t + 1 = R.lw
  · simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    exact .done _ (.inl ⟨hpc1.trans (congrArg Host.addrOf rfl), hl ▸ C1⟩)
  · simp only [hl, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b12Offset) NativeRustcVmArm.Vm.WriteOpenings.label_11_at]
      at hpc1
    refine .done _ (.inr ⟨R.lw - (t + 1), by omega, t + 1, rfl, hpc1, C1, ?_, ?_, ?_, by omega⟩)
    · rw [hm1.regs .X8 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x8]
      exact addr_add (by omega)
    · rw [hm1.regs .X9 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x9]
      exact addr_add (by omega)
    · rw [hm1.regs .X10 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [x10, ofNat_sub (by omega)]
      congr 1

end

end NativeRustcVmArm.Wire.WriteOpenings
