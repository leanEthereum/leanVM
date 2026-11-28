module

public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Call

/-!
# `open_phase`: a climb's leaf hash

From the loop head `.L11` (`CInv`), `b13` (the counter, never zero there) and `b14` call
`keccak256_words` with `hash_words`' closure on opening `j`'s leaf words: at `b15`, the hash at
the frame's `48` (`Hashed`, `hash_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

@[expose] public section

/-- At `b15`: opening `j`'s leaf hashed at the frame's `48`. -/
structure Hashed [Labels] (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (R : Digest)
    (h w j : Nat) (m : MachineData) : Prop where
  inv : CInv m0 P Q R h w j m
  hash : NativeRustcVm.WordsAt m.dmem (base m0 176 + BitVec.ofNat 64 48)
    (hashWords (P[j]'inv.lt).leaf).toList

end

public section

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- **A climb's leaf hash**: from `.L11`, `b15` with opening `j`'s leaf hashed. -/
theorem hash_spec (hp : Placed code k)
    (hkh : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    (hpre : OpenPhasePre P R Q m0) {h w : Nat} (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat}
    {m : MachineData} (hi : CInv m0 P Q R h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b15Offset) ∧ Hashed m0 P Q R h w j st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset)⟩ := by
  have hS := hpre.1
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset) := b13_in_code.trans hp.1 (by simp [b13])
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b14Offset) := b14_in_code.trans hp.1 (by simp [b14])
  have how : openingWords = 193 := rfl
  have hpw : phaseWords = 49411 := rfl
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hw64 : w ≤ 64 := hph.2.1
  have hlt := hi.lt
  have hwn : w.toUInt64.toNat = w := by simp [Nat.toUInt64]; omega
  -- `b13`: the counter is not zero.
  refine frTestD hpre hi.fr hk13 run_b13 rfl rfl (fun r ↦ by cases r <;> rfl)
    fun st1 hf1 he1 hd1 hpc1 ↦ ?_
  have hc13 : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X25) (.lit 0)).eval
      (Env.ofMachine m [(base m0 176, 176)]) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show ((m.regs.getXReg .X25).toBitVec == 0#64) = false
    have h25 : (m.regs.getXReg .X25).toBitVec.toNat = 395264 - 1544 * j := hi.x25
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    rw [e] at h25
    simp at h25
    omega
  simp only [PcOk] at hpc1
  rw [hc13] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1
  subst hpc1
  -- `b14`: the call's arguments.
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hf1.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hf1.sp
  refine exec_then hk14 run_b14 hwf hm fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hf2, hd2⟩ := frBlock hf1 hS (by decide) (by decide) hm2 rfl rfl (by decide) (by decide)
  have hx21 : d1.regs.getXReg .X21 = w.toUInt64 := (he1 .X21).trans hi.x21
  have hx0 : st2.data.regs.X0.toBitVec = base m0 176 + BitVec.ofNat 64 48 := by
    rw [show st2.data.regs.X0 = st2.data.regs.getXReg .X0 from rfl, hm2.regs .X0 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hx1 : st2.data.regs.X1.toNat = w := by
    have e : st2.data.regs.getXReg .X1 = d1.regs.getXReg .X21 :=
      UInt64.toBitVec_inj.mp ((hm2.regs .X1 _ rfl).trans rfl)
    rw [show st2.data.regs.X1 = st2.data.regs.getXReg .X1 from rfl, e, hx21, hwn]
  have hx4 : st2.data.regs.X4.toNat = w := by
    have e : st2.data.regs.getXReg .X4 = d1.regs.getXReg .X21 :=
      UInt64.toBitVec_inj.mp ((hm2.regs .X4 _ rfl).trans rfl)
    rw [show st2.data.regs.X4 = st2.data.regs.getXReg .X4 from rfl, e, hx21, hwn]
  have hl8 : (Env.ofMachine d1 [(base m0 176, 176)]).load 0 8 8 = (8 * w).toUInt64.toBitVec :=
    load_word (by show NativeRustcVm.WordAt d1.dmem _ _; rw [hd1]; exact hi.w8)
  have hx2 : st2.data.regs.X2.toNat = 8 * w := by
    show (st2.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm2.regs .X2 _ rfl]
    show ((Env.ofMachine d1 [(base m0 176, 176)]).load 0 8 8).toNat = _
    rw [hl8]
    simp [Nat.toUInt64]
    omega
  have hx3 : st2.data.regs.X3.toBitVec = phO m0 + BitVec.ofNat 64 (1544 * j + 32) := by
    rw [show st2.data.regs.X3 = st2.data.regs.getXReg .X3 from rfl, hm2.regs .X3 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
    show (d1.regs.getXReg .X20).toBitVec + BitVec.ofInt 64 32 = _
    rw [he1, hi.x20, show BitVec.ofInt 64 32 = BitVec.ofNat 64 32 from rfl,
      NativeRustcVm.addr_add_add]
  have hc : 1544 * j + 32 < 8 * phaseWords := by rw [hpw]; omega
  have hcn : 1544 * j + 32 + 8 * w ≤ 8 * phaseWords := by rw [hpw]; omega
  have hkpre : Keccak256WordsHashPre st2.data := by
    refine ⟨stackOk hpre hf2 (by decide), rcAt hpre hf2 (by decide), by rw [hx1, hx4],
      by rw [hx2, hx4], ?_, ?_, ?_, ?_, fun _ ↦ ?_, ?_, ?_⟩
    · rw [hx3, hx4]; exact ph_mapped hpre hf2 hcn
    · rw [hx3, hx4]; exact ph_noWrap hpre hcn
    · rw [hx0]; exact fr_mapped hpre hf2 (by omega)
    · rw [hx0]; exact fr_noWrap hpre (by omega)
    · rw [hx3, hx4]; exact ph_apart_callee hpre hf2 hc hcn (by decide)
    · rw [hx0]; exact fr_apart_callee hpre hf2 (by omega) (by decide)
    · rw [hx0]; exact local_rc hpre (by omega)
  have hleaf : NativeRustcVm.WordsAt st2.data.dmem st2.data.regs.X3.toBitVec
      (P[j]'hlt).leaf.toList := by
    have ho := hph.2.2.2.2.2.2 j hlt
    have := ho.2.2.2.2.1
    rw [off_off, off, show 8 * (3 + j * openingWords) + 8 = 1544 * j + 32 by rw [how]; ring]
      at this
    rw [hx3]
    exact ph_keep hpre hf2 hc hcn (le_of_eq (by
      rw [NativeRustcVm.length_wordsBytes, Array.length_toList, ho.1])) this
  refine call_then hpc2 hkh hkpre fun st3 hpc3 hpost3 ↦ ?_
  obtain ⟨hw3, hs3, hsv3⟩ := hpost3
  rw [hx0] at hs3
  obtain ⟨hf3, hk3⟩ := afterCall hpre hf2 (N' := keccak256WordsStack) (o := 48) (by decide)
    (by omega) hsv3 hs3
  have hr3 : ∀ r, calleeSaved r = true → st3.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    rw [hsv3.1 r hr, ← he1 r]
    cases r <;> first
      | exact absurd hr (by decide)
      | exact UInt64.toBitVec_inj.mp ((hm2.regs _ _ rfl).trans rfl)
  have hh := hw3 (P[j]'hlt).leaf.toList (by rw [Array.length_toList, (hph.2.2.2.2.2.2 j hlt).1, hx4])
    hleaf
  rw [hx0] at hh
  refine Eventually.done _ ⟨hpc3, hi.keep hf3 hr3 fun hob h ↦ hk3 (by omega) (.inl (by omega))
    (by rw [hd2, hd1]; exact h), ?_⟩
  simpa only [Array.toArray_toList] using hh

end

end NativeRustcVmArm.Sumcheck.OpenPhase
