module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Wire.ClimbLevel.Store

/-!
# `climb_level`'s parent hashed

A call of `hash_pair` from the frame into SP+96 (`hash_call`); node `i` first (`b14`, `b15`,
`hash14_spec`: an even key, or a carried sibling) or its sibling first (`b2`, `b3`,
`hash2_spec`: an odd key, its sibling read), then the parent stored.
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- An argument of `hash_pair`: 32 mapped bytes apart from its stack (below the frame). -/
def HashArg (m0 m : MachineData) (a : BitVec 64) : Prop :=
  NativeRustcVm.Mapped m.dmem a 32 ∧ a.toNat + 32 ≤ 2 ^ 64 ∧
    (a.toNat + 32 ≤ m0.regs.SP.toNat - climbLevelStack ∨ m0.regs.SP.toNat - 224 ≤ a.toNat)

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

theorem Geo.hashArg_frame [Labels] (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {o : Nat}
    (ho : o + 32 ≤ 224) : HashArg m0 m (base m0 224 + BitVec.ofNat 64 o) := by
  have hsp := G.sp
  have hb := G.bF
  unfold climbLevelStack at hsp
  refine ⟨fun t ht ↦ ?_, by rw [toNat_off (by omega), hb]; omega,
    .inr (by rw [toNat_off (by omega), hb]; omega)⟩
  rw [NativeRustcVm.addr_add_add]
  exact hfr.kept _ (Ring.frame_mapped G.g.st (by decide) _ (by omega))

theorem Geo.hashArg_node [Labels] (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {i : Nat}
    (hi : i < cnt m0) : HashArg m0 m (nd m0 i + BitVec.ofNat 64 8) := by
  have hsp := G.sp
  have := G.ndNw
  have := G.nS
  refine ⟨fun t ht ↦ ?_, by rw [G.nd_toNat (by omega)]; omega,
    by rw [G.nd_toNat (by omega)]; unfold climbLevelStack at *; omega⟩
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
  exact hfr.kept _ (G.ndMap _ (by omega))

variable [Host] {k : Nat}

/-- **A call of `hash_pair`** from the frame, into SP+96: the hash there, memory changed only
in the stack. -/
theorem hash_call (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost) {st : MachineState}
    {next : Int64} {R : MachineState → Prop} (hfr : Frm m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 96) {l r : BitVec 64}
    (hx1 : st.data.regs.X1.toBitVec = l) (hx2 : st.data.regs.X2.toBitVec = r)
    (hl : HashArg m0 st.data l) (hr : HashArg m0 st.data r) {L Rd : Digest}
    (hL : WordsAt st.data.dmem l L.toList) (hR : WordsAt st.data.dmem r Rd.toList)
    (cont : ∀ m2, Frm m0 m2 →
      WordsAt m2.dmem (base m0 224 + BitVec.ofNat 64 96) (NativeVm.Model.hashPair L Rd).toList →
      SameOutside st.data.dmem m2.dmem (fun a ↦ Keep m0 256 256 a ∧
        ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 a) →
      (∀ x, calleeSaved x = true → m2.regs.getXReg x = st.data.regs.getXReg x) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hsp := G.sp
  have hN := G.g.st.2.1
  have hbF := G.bF
  have hsb : stackBelow st.data hashPairStack = base m0 climbLevelStack :=
    Ring.stackBelow_eq hfr.sp (show 224 + hashPairStack ≤ m0.regs.SP.toNat from hN)
  have hsbN : (stackBelow st.data hashPairStack).toNat = m0.regs.SP.toNat - climbLevelStack := by
    rw [hsb, G.bN]
  have hout := G.hashArg_frame hfr (o := 96) (by omega)
  have hrc := G.rc_frm hfr (n' := hashPairStack) (by decide)
  have hrc0 := G.rc.2.2
  have hrcN : rcAddr.toNat + 192 ≤ m0.regs.SP.toNat - climbLevelStack ∨
      m0.regs.SP.toNat ≤ rcAddr.toNat := by
    have h : _ ∨ _ := hrc0
    rw [show (stackBelow m0 climbLevelStack).toNat = _ from G.bN] at h
    unfold climbLevelStack at h ⊢
    omega
  have hap : ∀ {a : BitVec 64}, HashArg m0 st.data a →
      NativeRustcVm.Apart a 32 (stackBelow st.data hashPairStack) hashPairStack := by
    intro a ha
    unfold NativeRustcVm.Apart
    rw [hsbN]
    have := ha.2.2
    unfold climbLevelStack hashPairStack keccak256WordsStack keccakFStack at *
    omega
  have hP : HashPairPre st.data := by
    refine ⟨hfr.stackOk G.g.st (by decide) (by decide), hrc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx1]; exact hl.1
    · rw [hx1]; exact hl.2.1
    · rw [hx2]; exact hr.1
    · rw [hx2]; exact hr.2.1
    · rw [hx0]; exact hout.1
    · rw [hx0]; exact hout.2.1
    · rw [hx1]; exact hap hl
    · rw [hx2]; exact hap hr
    · rw [hx0]; exact hap hout
    · rw [hx0]
      have := hout.2.2
      show _ ∨ _
      rw [toNat_off (by omega), hbF]
      rw [toNat_off (by omega), hbF] at this
      unfold climbLevelStack at *
      omega
  refine Fr.leafIn (lo := 96) (n := 32) (N' := hashPairStack) hfr hN (by decide) (by decide)
    (by simp) (by decide) (fun q hq ↦ G.g.not_frame (by decide) hq)
    (Spec.carry hh fun m ↦ m.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 96 ∧
      m.regs.X1.toBitVec = l ∧ m.regs.X2.toBitVec = r)
    hpc ⟨hP, hx0, hx1, hx2⟩ (fun m' ⟨⟨_, hs, hsv⟩, h0, _, _⟩ ↦ ⟨?_, hsv⟩) ?_
  · refine NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_
    rcases hq with hq | hq
    · exact .inr (.inl (by rw [← h0]; exact hq))
    · exact .inl hq
  · intro m2 hfr2 ⟨⟨hpost, hs2, _⟩, h0, h1, h2⟩ hcs
    refine cont m2 hfr2 ?_ ?_ hcs
    · have := hpost L Rd (by rw [h1]; exact hL) (by rw [h2]; exact hR)
      rw [h0] at this
      exact this
    · refine NativeRustcVm.SameOutside.mono hs2 fun q hq ↦ ?_
      rcases hq with hq | hq
      · rw [h0] at hq
        refine G.stk ?_ 256 256
        have := hout.2.1
        rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN]
        rw [Sym.inRange_iff (by omega), toNat_off (by omega), hbF] at hq
        unfold climbLevelStack at *
        omega
      · rw [hsb] at hq
        exact G.stk (show (q - base m0 climbLevelStack).toNat < climbLevelStack from
          Nat.lt_of_lt_of_le hq (by decide)) 256 256

end

end NativeRustcVmArm.Wire.ClimbLevel
