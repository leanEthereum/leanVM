module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Dig

/-!
# `write_openings`' level step

Back from `find` to the digest (`dig_step`: `b18`, `b19`); the digest written (`store_step`,
`b15`): the next level (`LevA`) or the opening done (`EndA`). The levels' loop (`lev_loop`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j l : Nat}

/-- Level `l`'s digest of opening `j` in the phase. -/
theorem dig_inside (G : Geo R) (hj : j < R.nq) (hl : l < R.h) :
    Inside (R.oa (ob j + 520 + 32 * l)) 32 (R.big 7) := by
  have := ob_le (j := j) (by have := G.nq256; omega)
  have hh := G.h32
  exact inside_off G.outNw (by show _ ≤ phaseBytes; unfold ob at *; omega) (by omega)

variable [Host]

/-- **Back from `find`** (`b18`, `b19`): the digest. -/
theorem dig_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : F18 R j l st) :
    Eventually (step1 Host.exe) (DigA R j l) st := by
  have S := H.s
  have hwf := G.wf0 S.fr.kept
  have hm := frMatch G S.fr
  refine run_block G hp b18_in_code (by simp [b18]) run_b18 S.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := .X1 :: .X24 :: levRegs) (by decide)
  have S1 : LevS R j l s1.data := S.keep hfr1 hd1 fun r hr ↦
    hk1 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  have h8 : rv s1.data .X8 = 0#64 := by rw [hm1.regs .X8 _ rfl]; rfl
  simp only [PcOk, SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs] at hpc1
  cases hn : (R.keys l).findIdx? (· == skey (R.qw j) l) with
  | none =>
    have h0 := H.none hn
    rw [show (st.data.regs.getXReg .X0).toBitVec = st.data.regs.X0.toBitVec from rfl, h0] at hpc1
    simp only [show (!decide ((UInt64.toBitVec 0).toNat = (1#64).toNat)) = true from rfl,
      ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b14Offset) NativeRustcVmArm.Vm.WriteOpenings.label_13_at] at hpc1
    exact zero_step hp G hpc1 S1 h8 hn
  | some n =>
    obtain ⟨h0, h1⟩ := H.some n hn
    rw [show (st.data.regs.getXReg .X0).toBitVec = st.data.regs.X0.toBitVec from rfl, h0] at hpc1
    simp only [show (!decide ((UInt64.toBitVec 1).toNat = (1#64).toNat)) = false from rfl,
      Bool.false_eq_true, ↓reduceIte] at hpc1
    have hnc : n < (R.cw l).toNat := by
      have := findIdx_lt hn; rwa [keys_length] at this
    have hc := H.cle
    have S1' := S1
    have hx1 : (rv s1.data .X1).toNat = n := by
      rw [hk1 .X1 (by simp)]; exact h1
    have hx24 : rv s1.data .X24 = (R.cw l).toBitVec := by
      rw [hk1 .X24 (by simp)]; exact H.x24
    have hwf2 := G.wf0 S1.fr.kept
    have hm2 := frMatch G S1.fr
    refine run_block G hp b19_in_code (by simp [b19]) run_b19 S1.fr hpc1 hwf2 hm2 rfl
      (writesOk_frame (by decide)) fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hk2 := regs_keep hm2 hm2' (rs := .X1 :: levRegs) (by decide)
    simp only [PcOk, SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs, hx24, hx1,
      UInt64.toNat_toBitVec, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hpc2
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by simp; omega))] at hpc2
    refine node_step hp G (hpc2.trans (congrArg Host.addrOf rfl))
      (S1.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr)) ?_ hc hnc hn
    rw [hk2 .X1 List.mem_cons_self]; exact hx1

/-- **The digest written** (`b15`): the next level, or the opening done. -/
theorem store_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : DigA R j l st) :
    Eventually (step1 Host.exe) (fun st' ↦ EndA R j st' ∨ LevA R j (l + 1) st') st := by
  have S := H.s
  have hl := S.llt
  have hj := S.lt
  have hh := G.h32
  have hlw := G.lw64
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have hin := dig_inside G hj hl
  have hwf := G.wf1 S.fr.kept (by omega) (by omega) hin
  have hm : Match (envOf R st.data [(R.oa (ob j + 520 + 32 * l), 32)]) dS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩ (by rw [S.fr.sp]; simp [Sym.eval])
      trivial trivial trivial ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [S.x20, base1, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
          NativeRustcVm.addr_add_add]
        show R.out + _ = R.out + _
        congr 2; omega, trivial⟩
  refine run_block G hp b15_in_code (by simp [b15]) run_b15 S.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 1) (by omega) rfl hin (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j + 520 + 32 * l)) 32) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 1) (o := 0) (n := 32) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hon : ob j + 520 + 32 * l + 32 ≤ phaseBytes := by unfold ob at *; omega
  have hk1 := regs_keep hm hm1 (rs := [.X19, .X21, .X22, .X23, .X26, .X29, .X25]) (by decide)
  have hw : WordsAt s1.data.dmem (R.oa (ob j + 520 + 32 * l)) (R.digest l (R.qw j)) := by
    rw [H.dg]
    have w0 := stored hm1 (r := 1) (o := 0) (sz := 32) (v := .reg .X11) rfl (by omega)
      (by decide)
    have w8 := stored hm1 (r := 1) (o := 8) (sz := 32) (v := .reg .X10) rfl (by omega)
      (by decide)
    have w16 := stored hm1 (r := 1) (o := 16) (sz := 32) (v := .reg .X9) rfl (by omega)
      (by decide)
    have w24 := stored hm1 (r := 1) (o := 24) (sz := 32) (v := .reg .X8) rfl (by omega)
      (by decide)
    rw [NativeRustcVm.addr_add_zero] at w0
    exact words4 w0 w8 w16 w24
  have hmem : Begun R j s1.data.dmem :=
    ⟨G.done_keep hs hon (by omega) S.mem.1 (by omega),
      G.wordAt_keep hs hon S.mem.2 (by omega) (by omega)⟩
  have hleaf : ∃ i, R.pos (R.qw j) = some i ∧ R.LeafPart s1.data.dmem j i R.lw := by
    obtain ⟨i, hi, hlp⟩ := S.leaf
    exact ⟨i, hi, G.wordsAt_keep hs hon hlp (by simp; omega) (by simp; omega)⟩
  have hpath : R.PathPart s1.data.dmem j (l + 1) := by
    have hp0 := G.wordsAt_keep hs hon S.path (by rw [path_length]; omega)
      (by rw [path_length]; omega)
    unfold Run.PathPart at hp0 ⊢
    rw [List.range_succ, List.flatMap_append, NativeRustcVm.wordsAt_append_iff]
    refine ⟨hp0, ?_⟩
    rw [path_length, NativeRustcVm.addr_add_add,
      show ob j + 520 + 8 * (4 * l) = ob j + 520 + 32 * l by omega]
    simpa using hw
  have w1 := G.w1_keep hs hon S.w1
  have w2 := G.w2_keep hs hon S.w2
  have e20 : rv s1.data .X20 = R.oa (ob j + 544 + 32 * (l + 1)) := by
    rw [hm1.regs .X20 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [S.x20, NativeRustcVm.addr_add_add]
    show R.out + _ = R.out + _
    congr 2
  have e27 : rv s1.data .X27 = BitVec.ofNat 64 (l + 1) := by
    rw [hm1.regs .X27 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [S.x27, ofNat_add]
  have e28 : rv s1.data .X28 = BitVec.ofNat 64 (10240 * (l + 1)) := by
    rw [hm1.regs .X28 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [S.x28, S.cs.x22, ofNat_add]
    congr 1
  have hc : (SBool.cmp .eq .W64 (.reg .X26) (.bin .add .W64 (.reg .X28) (.reg .X22))).eval
      (envOf R st.data [(R.oa (ob j + 520 + 32 * l), 32)]) = decide (l + 1 = R.h) := by
    simp only [SBool.eval, eq_apply, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64,
      Env.ofMachine_regs]
    rw [S.cs.x26, S.x28, S.cs.x22, ofNat_add, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    by_cases h : l + 1 = R.h
    · rw [decide_eq_true (by omega), decide_eq_true h]
    · rw [decide_eq_false (by omega), decide_eq_false h]
  simp only [PcOk, hc] at hpc1
  have Cs1 : Cs R s1.data := S.cs.keep fun r hr ↦ hk1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp [h])
  by_cases hend : l + 1 = R.h
  · simp only [hend, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b21Offset) NativeRustcVmArm.Vm.WriteOpenings.label_19_at] at hpc1
    refine .done _ (.inl ⟨hpc1, hfr1, Cs1, hj, by omega, w1, w2, hmem.1.1, fun j' hj' ↦ ?_⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h' | rfl
    · exact hmem.1.2 j' h'
    · obtain ⟨i, hi, hlp⟩ := hleaf
      exact ⟨i, hi, hmem.2, hlp, hend ▸ hpath⟩
  · simp only [hend, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine .done _ (.inr ⟨hpc1.trans (congrArg Host.addrOf rfl), ⟨hfr1, Cs1, e20,
      by rw [hk1 .X25 (by simp)]; exact S.x25, e27, e28, hj, by omega, w1, w2, hmem, hleaf,
      hpath⟩⟩)

end

end NativeRustcVmArm.Wire.WriteOpenings
