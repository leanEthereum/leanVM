module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Hash

/-!
# `open_phase`: a climb's path

At `b15` (`Hashed`), `b15` calls `climb` on the hashed leaf at the frame's `48`, opening `j`'s leaf
index and path: at `b16`, the path's top at the frame's `16` (`Climbed`, `path_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

@[expose] public section

/-- At `b16`: opening `j`'s path climbed from its hashed leaf, at the frame's `16`. -/
structure Climbed [Labels] (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64)
    (R : Digest) (h w j : Nat) (m : MachineData) : Prop where
  inv : CInv m0 P Q R h w j m
  top : NativeRustcVm.WordsAt m.dmem (base m0 176 + BitVec.ofNat 64 16)
    (climb (hashWords (P[j]'inv.lt).leaf) (P[j]'inv.lt).leafIndex (P[j]'inv.lt).path).toList

end

public section

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- **A climb's path**: from `b15`, `b16` with opening `j`'s path climbed. -/
theorem path_spec (hp : Placed code k)
    (hcl : ∀ N P, Spec (Labels.label NativeRustcVmArm.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P))
    (hpre : OpenPhasePre P R Q m0) {h w : Nat} (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat}
    {m : MachineData} (hi : Hashed m0 P Q R h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b16Offset) ∧ Climbed m0 P Q R h w j st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b15Offset)⟩ := by
  have hS := hpre.1
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b15Offset) := b15_in_code.trans hp.1 (by simp [b15])
  have hc := hi.inv
  have hlt := hc.lt
  have ho := hph.2.2.2.2.2.2 j hlt
  have how : openingWords = 193 := rfl
  have hpw : phaseWords = 49411 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hh32 : h ≤ 32 := hph.1
  have hx20 : (m.regs.getXReg .X20).toBitVec = phO m0 + BitVec.ofNat 64 (1544 * j) := hc.x20
  obtain ⟨-, -, -, -, -, -, hmp, -⟩ := id hpre
  -- `b15`: the call's arguments, from the frame and opening `j`'s first 32 bytes.
  have hrd : Readable m0 (m.regs.getXReg .X20).toBitVec 32 := by
    rw [hx20]
    exact ⟨fun i hi ↦ by rw [NativeRustcVm.addr_add_add]; exact hmp _ (by rw [hpw]; omega),
      ph_noWrap hpre (by rw [hpw]; omega)⟩
  have hwf := Bus.wf_frame2 (F := 176) hS (by decide) hc.fr.kept hrd
    (by rw [hx20]; exact ph_apart hpre (by rw [hpw]; omega) (by rw [hpw]; omega))
  have hm := Bus.match_frame2 (r := .X20) (n := 32) hS (by decide) (by decide) hc.fr.sp
  refine exec_then hk15 run_b15 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hm1A : Match (Env.ofMachine m [(base m0 176, 176), ((m.regs.getXReg .X20).toBitVec, 32)])
      (after b15 opS) st1.data := by rw [after_eq run_b15]; exact hm1
  have hf1 : FrO m0 st1.data :=
    Bus.Fr.block (F := 176) hc.fr (hN hpre) (by decide) hm1A hwf (by rw [after_eq run_b15])
      (by rw [after_eq run_b15]; decide +kernel) (fun r hr ↦ nomatch hr) (by decide)
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have h20 : st1.data.regs.getXReg .X20 = m.regs.getXReg .X20 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans (by simp [Sym.eval, Env.base,
      Env.ofMachine]))
  have hr1 : ∀ r, calleeSaved r = true → st1.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    cases r <;> first
      | exact absurd hr (by decide)
      | exact h20
      | exact UInt64.toBitVec_inj.mp ((hm1.regs _ _ rfl).trans rfl)
  have hx0 : st1.data.regs.X0.toBitVec = base m0 176 + BitVec.ofNat 64 16 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hx1 : st1.data.regs.X1.toBitVec = base m0 176 + BitVec.ofNat 64 48 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hidx : NativeRustcVm.WordAt m.dmem (phO m0 + BitVec.ofNat 64 (1544 * j + 24))
      (P[j]'hlt).leafIndex := by
    have := ho.2.2.2.1
    rw [off, show 8 * (3 + j * openingWords) = 1544 * j + 24 by rw [how]; ring] at this
    exact ph_keep hpre hc.fr (n := 8) (by rw [hpw]; omega) (by rw [hpw]; omega)
      (by simp [NativeRustcVm.length_wordBytes]) this
  have hx2 : st1.data.regs.X2 = (P[j]'hlt).leafIndex := by
    apply UInt64.toBitVec_inj.mp
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl]
    refine load_word ?_
    show NativeRustcVm.WordAt m.dmem ((m.regs.getXReg .X20).toBitVec + BitVec.ofNat 64 24) _
    rw [hx20, NativeRustcVm.addr_add_add]
    exact hidx
  have hx3 : st1.data.regs.X3.toBitVec = phO m0 + BitVec.ofNat 64 (1544 * j + 544) := by
    rw [show st1.data.regs.X3 = st1.data.regs.getXReg .X3 from rfl, hm1.regs .X3 _ rfl]
    show (m.regs.getXReg .X20).toBitVec + BitVec.ofInt 64 544 = _
    rw [hx20, show BitVec.ofInt 64 544 = BitVec.ofNat 64 544 from rfl,
      NativeRustcVm.addr_add_add]
  have hx4 : st1.data.regs.X4.toNat = h := by
    have e : st1.data.regs.getXReg .X4 = m.regs.getXReg .X22 :=
      UInt64.toBitVec_inj.mp ((hm1.regs .X4 _ rfl).trans rfl)
    rw [show st1.data.regs.X4 = st1.data.regs.getXReg .X4 from rfl, e, hc.x22]
    simp [Nat.toUInt64]
    omega
  have hpl : (pathWords (P[j]'hlt).path).length = 4 * h := by
    have hl : ∀ xs : List Digest, (xs.flatMap (·.toList)).length = 4 * xs.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih =>
        simp only [List.flatMap_cons, List.length_append, Vector.length_toList, ih,
          List.length_cons]
        omega
    unfold pathWords
    rw [hl, Array.length_toList, ho.2.1]
  have hc544 : 1544 * j + 544 < 8 * phaseWords := by rw [hpw]; omega
  have hcn : 1544 * j + 544 + 32 * h ≤ 8 * phaseWords := by rw [hpw]; omega
  have hpath : NativeRustcVm.WordsAt st1.data.dmem (phO m0 + BitVec.ofNat 64 (1544 * j + 544))
      (pathWords (P[j]'hlt).path) := by
    have := ho.2.2.2.2.2
    rw [off_off, off, show 8 * (3 + j * openingWords) + 8 * (1 + wireMaxLeafWords) =
      1544 * j + 544 by rw [how, hml]; ring] at this
    exact ph_keep hpre hf1 hc544 hcn (by rw [NativeRustcVm.length_wordsBytes, hpl]; omega) this
  have hclpre : ClimbPre (hashWords (P[j]'hlt).leaf) (P[j]'hlt).path st1.data := by
    refine ⟨stackOk hpre hf1 (by decide), rcAt hpre hf1 (by decide), by rw [hx4, hmh]; exact hh32,
      by rw [hx4]; exact ho.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx1, hd1]; exact hi.hash
    · rw [hx3]; exact hpath
    · rw [hx1]; exact fr_noWrap hpre (by omega)
    · rw [hx3, hx4]; exact ph_noWrap hpre hcn
    · rw [hx0]; exact fr_mapped hpre hf1 (by omega)
    · rw [hx0]; exact fr_noWrap hpre (by omega)
    · rw [hx1]; exact fr_apart_callee hpre hf1 (by omega) (by decide)
    · rw [hx3, hx4]; exact ph_apart_callee hpre hf1 hc544 hcn (by decide)
    · rw [hx0]; exact fr_apart_callee hpre hf1 (by omega) (by decide)
    · rw [hx0]; exact local_rc hpre (by omega)
  refine call_then hpc1 (hcl _ _) hclpre fun st2 hpc2 hpost2 ↦ ?_
  obtain ⟨hcl2, hs2, hsv2⟩ := hpost2
  rw [hx0] at hs2
  obtain ⟨hf2, hk2⟩ := afterCall hpre hf1 (N' := climbStack) (o := 16) (by decide) (by omega)
    hsv2 hs2
  rw [hx0, hx2] at hcl2
  exact Eventually.done _ ⟨hpc2, hc.keep hf2 (fun r hr ↦ (hsv2.1 r hr).trans (hr1 r hr))
    fun hob h ↦ hk2 (by omega) (.inl (by omega)) (by rw [hd1]; exact h), hcl2⟩

end

end NativeRustcVmArm.Sumcheck.OpenPhase
