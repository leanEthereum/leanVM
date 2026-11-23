module

public import NativeRustcVmArm.Wire.WriteOpenings.B.Copy

/-!
# `write_openings`' leaf copy loops (`h = 0`, a leaf)

Four words at a time (`chunkB_loop`, `b32`, then `b33`): the leaf copied, or its last words set
up; one word at a time (`remB_loop`, `b35`): the leaf copied.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j i : Nat} [Host]

/-- **Four words at a time** (`b32`, `b33`). -/
theorem chunkB_loop (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : ChunkB R j i t st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtB36 R j i st' ∨ AtB34 R j i (q4 R.lw) st') st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = q4 R.lw - t ∧ ChunkB R j i t st) (fun n st ⟨t, hn, H⟩ ↦ ?_)
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
      (R.oa (ob j + 8 + 8 * t), 32)]) (cpS 32 .X14 16 .X15 24) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [C.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x14, base1, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
          NativeRustcVm.addr_add_add], by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x15, base2, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
          NativeRustcVm.addr_add_add]
        show R.out + _ = R.out + _
        congr 2
        omega, trivial⟩
  refine run_block G hp b32_in_code (by simp [b32]) run_b32 C.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j + 8 + 8 * t)) 32) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 32) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
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
  have hk1 := regs_keep hm hm1 (rs := .X13 :: rbRegs) (by decide)
  have C1 : CopyB R j i (t + 4) s1.data :=
    ⟨hfr1, C.rb.keep fun r hr ↦ hk1 r (List.mem_cons_of_mem _ hr), hj, hi, C.hz, C.pos, hmem,
      hleaf, by omega⟩
  have x13 : rv s1.data .X13 = R.lv + BitVec.ofNat 64 (512 * i) := by
    rw [hk1 .X13 (by simp)]; exact H.x13
  have x16 : rv st.data .X16 = BitVec.ofNat 64 (q4 R.lw - t) := H.x16
  have hc : (SBool.cmp .eq .W64 (.reg .X16) (.lit 4)).not.eval (envOf R st.data
      [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32), (R.oa (ob j + 8 + 8 * t), 32)]) =
      decide (t + 4 ≠ q4 R.lw) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x16, ofNat_toNat (by omega), ofNat_toNat (by omega)]
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
    -- `b33`
    have hwf2 := G.wf0 hfr1.kept
    have hm2 := frMatch G hfr1
    refine run_block G hp b33_in_code (by simp [b33]) run_b33 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hk2 := regs_keep hm2 hm2' (rs := .X13 :: rbRegs) (by decide)
    have C2 : CopyB R j i (t + 4) s2.data :=
      C1.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr)
    have hc2 : (SBool.cmp .eq .W64 (.reg .X21) (.reg .X8)).eval (envOf R s1.data []) =
        decide (R.lw = q4 R.lw) := by
      simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
      rw [C1.rb.x21, C1.rb.x8, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    simp only [PcOk, hc2] at hpc2
    by_cases he : R.lw = q4 R.lw
    · rw [decide_eq_true he] at hpc2
      simp only [↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b36Offset) NativeRustcVmArm.Vm.WriteOpenings.label_32_at] at hpc2
      refine .done _ (.inl (.inl ⟨hpc2, ?_⟩))
      rw [show R.lw = t + 4 by omega]
      exact C2
    · rw [decide_eq_false he] at hpc2
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
      refine .done _ (.inl (.inr ⟨hpc2.trans (congrArg Host.addrOf rfl), hl ▸ C2,
        by rw [hk2 .X13 (by simp)]; exact x13, ?_, by omega⟩))
      rw [hm2'.regs .X15 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [C1.rb.x21, and124 (by omega)]
  · simp only [hl, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b32Offset) NativeRustcVmArm.Vm.WriteOpenings.label_28_at]
      at hpc1
    refine .done _ (.inr ⟨q4 R.lw - (t + 4), by omega, t + 4, rfl, hpc1, C1, x13, ?_, ?_, ?_,
      by omega, by unfold q4 at *; omega⟩)
    · rw [hm1.regs .X14 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x14]
      exact addr_add (by omega)
    · rw [hm1.regs .X15 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x15]
      exact addr_add (by omega)
    · rw [hm1.regs .X16 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [x16, ofNat_sub (by omega)]
      congr 1

/-- **One word at a time** (`b35`). -/
theorem remB_loop (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : RemB R j i t st) : Eventually (step1 Host.exe) (AtB36 R j i) st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = R.lw - t ∧ RemB R j i t st) (fun n st ⟨t, hn, H⟩ ↦ ?_)
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
      (R.oa (ob j + 8 + 8 * t), 8)]) (cpS 8 .X13 0 .X14 0) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [C.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x13, base1, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x14, base2, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine run_block G hp b35_in_code (by simp [b35]) run_b35 C.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j + 8 + 8 * t)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have w0 := copied hm1 (r := 2) (o := 0) (sz := 8) (r' := 1) (o' := 0) rfl (by omega)
    (by decide)
  simp only [Env.ofMachine_mem0, base1] at w0
  obtain ⟨hmem, hleaf⟩ := G.copy1 hj (by omega) hs C.mem C.leaf
    (leaf_copied G C.fr (u := 0) hi (by omega) w0)
  have hk1 := regs_keep hm hm1 (rs := rbRegs) (by decide)
  have C1 : CopyB R j i (t + 1) s1.data :=
    ⟨hfr1, C.rb.keep hk1, hj, hi, C.hz, C.pos, hmem, hleaf, by omega⟩
  have x15 : rv st.data .X15 = BitVec.ofNat 64 (R.lw - t) := H.x15
  have hc : (SBool.cmp .eq .W64 (.reg .X15) (.lit 1)).not.eval (envOf R st.data
      [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 8), (R.oa (ob j + 8 + 8 * t), 8)]) =
      decide (t + 1 ≠ R.lw) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x15, ofNat_toNat (by omega), ofNat_toNat (by omega)]
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
  · simp only [hl, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b35Offset) NativeRustcVmArm.Vm.WriteOpenings.label_31_at]
      at hpc1
    refine .done _ (.inr ⟨R.lw - (t + 1), by omega, t + 1, rfl, hpc1, C1, ?_, ?_, ?_, by omega⟩)
    · rw [hm1.regs .X13 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x13]
      exact addr_add (by omega)
    · rw [hm1.regs .X14 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.x14]
      exact addr_add (by omega)
    · rw [hm1.regs .X15 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [x15, ofNat_sub (by omega)]
      congr 1

end

end NativeRustcVmArm.Wire.WriteOpenings
