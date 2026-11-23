module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Climb
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names

/-!
# `open_phase`: a climb's check (x86-64)

At `b16` (`Climbed`), `b16` to `b19` test the path's top word by word against the root's (the
frame's `48 - 8 i`; `test_spec`): a mismatch leaves for `NativeRustcVmX64.Vm.OpenPhase.label_19` (`exit_fail`, the climbs
fail); `b20` steps the counters: back to `NativeRustcVmX64.Vm.OpenPhase.label_7` with one climb more (`CInv`), or after
the last one `NativeRustcVmX64.Vm.OpenPhase.label_13` (`exit_rows`) (`round_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.OpenPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.OpenPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}
  {h w j : Nat}

/-- **A test of the path's top**: `ds` compares its word `i` (the frame's `64 + 8 i`) with the
root's (the frame's `48 - 8 i`) and leaves for `NativeRustcVmX64.Vm.OpenPhase.label_19` where they differ. -/
theorem test_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) {m : MachineData} (hc : Climbed m0 P Q R h w j m)
    {ds : List Directive} {S' : SState} {a i : Nat} (hi4 : i < 4)
    (hk : ds.IsInfixAt Host.prog a) (hx : exec ds frS = some (S', .cond (cw i) NativeRustcVmX64.Vm.OpenPhase.label_19))
    (hok : WTestOk S') :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨
        (st.pc = Host.addrOf (a + ds.length) ∧ Climbed m0 P Q R h w j st.data ∧
          (climb (hashWords (P[j]'hc.inv.lt).leaf) (P[j]'hc.inv.lt).leafIndex
            (P[j]'hc.inv.lt).path).toList[i]'(by simpa using hi4) =
            R.toList[i]'(by simpa using hi4)))
      ⟨m, Host.addrOf a⟩ := by
  have hst := hpre.1
  have hlt := hc.inv.lt
  obtain ⟨hmid, hmem, hkb⟩ := hok
  refine frTest hst hc.inv.fr hk hx nofun hmid hmem hkb fun st hf hd hkr hm hpc ↦ ?_
  obtain ⟨T, hT⟩ : ∃ T, T = climb (hashWords (P[j]'hlt).leaf) (P[j]'hlt).leafIndex
      (P[j]'hlt).path := ⟨_, rfl⟩
  have htop : NativeRustcVm.WordsAt m.dmem (off (fa m0) 64) T.toList := by rw [hT]; exact hc.top
  have hwi : NativeRustcVm.WordAt m.dmem (off (fa m0) (64 + 8 * i))
      (T.toList[i]'(by simpa using hi4)) := by
    have := wordsAt_iff.mp htop i (by simpa using hi4)
    rwa [off_off] at this
  have hev : (cw i).eval (frameEnv m0 m 176 [] (fun _ ↦ 0) 0) =
      !((T.toList[i]'(by simpa using hi4)).toBitVec ==
        (R.toList[i]'(by simpa using hi4)).toBitVec) := by
    simp only [cw, SBool.eval, Sym.eval, CmpOp.apply, low_W64]
    rw [load_ofMachine (o := 64 + 8 * i) rfl hwi,
      load_ofMachine (o := 48 - 8 * i) rfl (hc.inv.root i hi4)]
  simp only [PcOk, hev] at hpc
  by_cases heq : T.toList[i]'(by simpa using hi4) = R.toList[i]'(by simpa using hi4)
  · rw [heq] at hpc
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    refine .done _ (.inr ⟨hpc, ⟨hc.inv.keep hf (fun r hr ↦ hkr r
      (by rcases hr with h | h | h | h | h <;> subst h <;> decide)
      (by rcases hr with h | h | h | h | h <;> subst h <;> rfl)) (fun _ _ _ ↦ by rw [hd]),
      by have := hc.top; rwa [← hd] at this⟩, by subst hT; exact heq⟩)
  · have hne : ((T.toList[i]'(by simpa using hi4)).toBitVec ==
        (R.toList[i]'(by simpa using hi4)).toBitVec) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h' ↦ heq (UInt64.toBitVec_inj.mp h')
    rw [hne] at hpc
    simp only [Bool.not_false, ↓reduceIte] at hpc
    obtain ⟨d, pc⟩ := st
    have hpc' : pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b22Offset) := hpc.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_19_at)
    subst hpc'
    refine Eventually.mono (exit_fail hp hpre hf (by rw [hd]; exact hc.inv.w16) ?_)
      fun st h ↦ .inl h
    refine climbs_none hph hc.inv.shape hc.inv.pos fun hcl ↦ heq ?_
    rw [hT, hcl j hlt hlt]

/-- **A climb's check**: from `b16`, the exit (a mismatch, or the rows after the last climb) or
`NativeRustcVmX64.Vm.OpenPhase.label_7` with one climb more. -/
theorem round_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) {m : MachineData} (hc : Climbed m0 P Q R h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b13Offset) ∧ CInv m0 P Q R h w (j + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b16Offset)⟩ := by
  have hst := hpre.1
  have hlt := hc.inv.lt
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hpw : phaseWords = 49411 := rfl
  -- `b16` to `b19`: the path's top is the root.
  refine Eventually.bind (test_spec hp hpre hph hc (a := k + NativeRustcVmX64.Vm.OpenPhase.b16Offset) (i := 0) (by decide)
    (infix_of b16_in_code (by simp [b16]) hp) exit_b16 ok_b16) fun st1 h1 ↦ ?_
  rcases h1 with h1 | ⟨hpc1, hc1, e0⟩
  · exact .done _ (.inl h1)
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1
  rw [NativeRustcVmX64.Vm.OpenPhase.b16_length] at hpc1
  subst hpc1
  refine Eventually.bind (test_spec hp hpre hph hc1 (a := k + NativeRustcVmX64.Vm.OpenPhase.b17Offset) (i := 1) (by decide)
    (infix_of b17_in_code (by simp [b17]) hp) exit_b17 ok_b17) fun st2 h2 ↦ ?_
  rcases h2 with h2 | ⟨hpc2, hc2, e1⟩
  · exact .done _ (.inl h2)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2
  rw [NativeRustcVmX64.Vm.OpenPhase.b17_length] at hpc2
  subst hpc2
  refine Eventually.bind (test_spec hp hpre hph hc2 (a := k + NativeRustcVmX64.Vm.OpenPhase.b18Offset) (i := 2) (by decide)
    (infix_of b18_in_code (by simp [b18]) hp) exit_b18 ok_b18) fun st3 h3 ↦ ?_
  rcases h3 with h3 | ⟨hpc3, hc3, e2⟩
  · exact .done _ (.inl h3)
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc3
  rw [NativeRustcVmX64.Vm.OpenPhase.b18_length] at hpc3
  subst hpc3
  refine Eventually.bind (test_spec hp hpre hph hc3 (a := k + NativeRustcVmX64.Vm.OpenPhase.b19Offset) (i := 3) (by decide)
    (infix_of b19_in_code (by simp [b19]) hp) exit_b19 ok_b19) fun st4 h4 ↦ ?_
  rcases h4 with h4 | ⟨hpc4, hc4, e3⟩
  · exact .done _ (.inl h4)
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4
  rw [NativeRustcVmX64.Vm.OpenPhase.b19_length] at hpc4
  subst hpc4
  have hTR : climb (hashWords (P[j]'hlt).leaf) (P[j]'hlt).leafIndex (P[j]'hlt).path = R :=
    Vector.toList_inj.mp (List.ext_getElem (by simp) fun n h1 _ ↦ by
      simp only [Vector.length_toList] at h1
      match n, h1 with
      | 0, _ => exact e0
      | 1, _ => exact e1
      | 2, _ => exact e2
      | 3, _ => exact e3)
  have hcl : ClimbsOk R P (j + 1) := (climbsOk_succ hlt).2 ⟨hc.inv.climbs, hTR⟩
  -- `b20`: the counters.
  have hi := hc4.inv
  obtain ⟨hmid, hmem, h12, h15, hkb⟩ := ok_b20
  refine frTest hst hi.fr (infix_of b20_in_code (by simp [b20]) hp) exit_b20 nofun hmid hmem hkb
    fun st5 hf5 hd5 hk5 hm5 hpc5 ↦ ?_
  have hj12 : (reg d4 .r12).toNat = j := hi.r12
  have hev : c20.eval (frameEnv m0 d4 176 [] (fun _ ↦ 0) 0) = !decide (j + 1 = P.size) := by
    simp only [c20, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs]
    rw [show d4.regs.get64 .r13 = P.size.toUInt64.toBitVec from hi.r13,
      toUInt64_beq (by omega)]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, BitVec.toNat_add,
      show (d4.regs.get64 .r12).toNat = j from hj12]
    simp only [BitVec.toNat_ofNat]
    have : P.size < 2 ^ 64 := by omega
    omega
  simp only [PcOk, hev] at hpc5
  have hk' : ∀ r, r = .rbp ∨ r = .r13 ∨ r = .r14 → reg st5.data r = reg d4 r := by
    rintro r (rfl | rfl | rfl) <;> exact hk5 _ (by decide) rfl
  have hl : LowKept m0 d4 st5.data := fun _ _ _ ↦ by rw [hd5]
  by_cases hj1 : j + 1 = P.size
  · -- after the last climb: the rows.
    simp only [hj1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    obtain ⟨d5, pc5⟩ := st5
    have hpc5' : pc5 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b21Offset) := hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b20_next)
    subst hpc5'
    refine Eventually.mono (exit_rows hp hpre hf5 (hl.word (by omega) (by omega) hi.w16) hph.2.1
      hph.2.2.1 ((hk' _ (by simp)).trans hi.rbp) ((hk' _ (by simp)).trans hi.r13)
      ((hk' _ (by simp)).trans hi.r14) (leaf_words hpre hph hf5.same) ?_) fun st h ↦ .inl h
    exact climbs_some hph hi.shape hi.pos (hj1 ▸ hcl)
  · -- one climb more.
    simp only [hj1, decide_false, Bool.not_false, ↓reduceIte] at hpc5
    have hj1' : j + 1 < P.size := by omega
    refine .done _ (.inr ⟨hpc5.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_7_at), hf5, hj1', hi.shape, hi.pos, hcl,
      ?_, (hk' _ (by simp)).trans hi.r13, (hk' _ (by simp)).trans hi.r14, ?_,
      (hk' _ (by simp)).trans hi.rbp, hl.word (by omega) (by omega) hi.w16,
      hl.word (by omega) (by omega) hi.w56,
      fun i hi4 ↦ hl.word (by omega) (by omega) (hi.root i hi4)⟩)
    · rw [show reg st5.data .r12 = _ from hm5.regs .r12 _ h12]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, BitVec.toNat_add,
        show (d4.regs.get64 .r12).toNat = j from hj12, BitVec.toNat_ofNat,
        show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
      omega
    · rw [show reg st5.data .r15 = _ from hm5.regs .r15 _ h15]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show d4.regs.get64 .r15 = off (phO m0) (544 + 1544 * j) from hi.r15]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, ph_toNat hpre (by rw [hpw]; omega),
        ph_toNat hpre (by rw [hpw]; omega)]
      simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
      have hnw : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hpre.2.2.2.2.2.2.2.2.1
      omega

end

end NativeRustcVmX64.Sumcheck.OpenPhase
