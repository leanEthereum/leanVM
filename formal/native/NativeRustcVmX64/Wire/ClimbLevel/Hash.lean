module

public import NativeRustcVmX64.Wire.ClimbLevel.Scan
public import NativeRustcVmX64.Code.Vm.HashPair.Names

/-!
# `climb_level`'s calls of `hash_pair` (x86-64)

`hash_pair`'s arguments: the sibling's digest in the frame at `8` or node `i`'s at its offset 8
(`Arg`); the call from a block ending in it (`hash_call`): its output at the frame's `88`, the
frame kept, what it changed.
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv Frame.of_block Frame.call_slots stackOk_callee
  stackBelow_callee RcAt.callee after after_eq MidOk sameOutside_low)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- An argument of `hash_pair`: the frame's `8`, or 32 bytes of the nodes. -/
def Arg (m0 : MachineData) (a : BitVec 64) : Prop :=
  a = off (fb m0) 8 ∨ ∃ o, o + 32 ≤ 40 * cnt m0 ∧ a = off (nodes m0) o

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

section
variable [Labels]

/-- An argument's bytes, as numbers: mapped, not wrapping, beside the callee's stack. -/
theorem Geo.arg (g : Geo m0 bp B.length) {m : MachineData} {o' : Nat}
    (hf : Frame m0 208 slots o' m) {a : BitVec 64} (h : Arg m0 a) :
    NativeRustcVm.Mapped m.dmem a 32 ∧ a.toNat + 32 ≤ 2 ^ 64 ∧
      (a.toNat + 32 ≤ sp m0 - 1056 ∨ sp m0 - 200 ≤ a.toNat) ∧
      (a.toNat + 32 ≤ sp m0 - 120 ∨ sp m0 - 88 ≤ a.toNat) := by
  have h0 := g.s0
  rcases h with rfl | ⟨o, ho, rfl⟩
  · have ht := g.fo (o := 8) (by omega)
    refine ⟨fun i hi ↦ ?_, by rw [ht]; omega, by rw [ht]; omega, by rw [ht]; omega⟩
    rw [off_add]
    exact hf.kept _ (NativeRustcVmX64.Transcript.frame_mapped g.g.st (by decide) _ (by omega))
  · obtain ⟨hm, hn, hs⟩ := g.nd_area hf (o := o) (n := 32) ho (by omega)
    have ht := g.nd_toNat (o := o) (by omega)
    have := g.nS
    rw [ht] at hn hs ⊢
    exact ⟨hm, hn, by omega, by omega⟩

end

variable [Host] {k : Nat}

/-- **A call of `hash_pair`** from a block (at `j`, from `frS`) ending in it, its output at the
frame's `88`, its arguments `al`, `ar` holding `L`, `R`: back after the call in the frame, the
callee-saved registers the block's, memory changed at most in the output, the callee's stack and
the return address's slot; the output `hashPair L R`. -/
theorem hash_call (hp : Placed code k)
    (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (g : Geo m0 bp B.length) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ [])
    (hrun : exec bj frS = some (after bj frS,
      .call NativeRustcVmX64.Vm.HashPair.entryLabel))
    (hok : MidOk 208 0 slots (after bj frS) = true)
    (hlow : ∀ w ∈ (after bj frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8)
    (hrdi : (after bj frS).reg .rdi = some (.ptr 0 88))
    {vsi vdx : Sym} (hsi : (after bj frS).reg .rsi = some vsi)
    (hdx : (after bj frS).reg .rdx = some vdx)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 208 slots 8 st.data)
    (hchg : Chg m0 st.data.dmem) {al ar : BitVec 64} (hal : Arg m0 al) (har : Arg m0 ar)
    (hvsi : vsi.eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0)
      (Host.addrOf (k + j + bj.length)).toBitVec) = al)
    (hvdx : vdx.eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0)
      (Host.addrOf (k + j + bj.length)).toBitVec) = ar)
    {L R : Digest} (hL : WordsAt st.data.dmem al L.toList) (hR : WordsAt st.data.dmem ar R.toList)
    {Q : MachineState → Prop}
    (cont : ∀ m2, Frame m0 208 slots 8 m2 →
      (∀ r v, (after bj frS).reg r = some v → calleeSaved r = true →
        reg m2 r = v.eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0)
          (Host.addrOf (k + j + bj.length)).toBitVec)) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0 - 200) ∨
        (sp m0 - 120 ≤ q.toNat ∧ q.toNat < sp m0 - 88)) →
      WordsAt m2.dmem (off (fb m0) 88) (NativeVm.Model.hashPair L R).toList →
      Eventually (step1 Host.exe) Q ⟨m2, Host.addrOf (k + j + bj.length)⟩) :
    Eventually (step1 Host.exe) Q st := by
  have h0 := g.s0
  have hspe := sp_eq m0
  have hfb := g.fb_toNat
  let ret := (Host.addrOf (k + j + bj.length)).toBitVec
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := ret)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := ret)
  refine exec_at (Wire.infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : Frame m0 208 slots 0 st1.data := Frame.of_block hf hwf hm1 hok slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 208) 8) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hlow
  have hs1n : ∀ q, NativeRustcVm.InRange (stackBelow m0 208) 8 q →
      sp m0 - 208 ≤ q.toNat ∧ q.toNat < sp m0 - 200 := fun q hq ↦ by
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hfb]; omega), hfb] at hq
    omega
  have hsp : rspOf st1.data = stackBelow m0 208 := by rw [hf1.sp, off_zero]
  have hcb : stackBelow st1.data hashPairStack = stackBelow m0 1056 := by
    rw [stackBelow_callee hsp (by rw [hps_eq]; omega), hps_eq]
  have hcbn : (stackBelow m0 1056).toNat = sp m0 - 1056 := NativeRustcVmX64.stackBelow_toNat h0.1
  have hdi : reg st1.data .rdi = off (fb m0) 88 := (hm1.regs .rdi _ hrdi).trans rfl
  have hsi' : reg st1.data .rsi = al := (hm1.regs .rsi _ hsi).trans hvsi
  have hdx' : reg st1.data .rdx = ar := (hm1.regs .rdx _ hdx).trans hvdx
  obtain ⟨hlm, hln, hlS, hlO⟩ := g.arg hf1 hal
  obtain ⟨hrm, hrn, hrS, hrO⟩ := g.arg hf1 har
  have ho88 := g.fo (o := 88) (by omega)
  have hchg1 : Chg m0 st1.data.dmem := chg_trans hchg hs1 fun q hq ↦ .inl (by
    have := hs1n q hq; omega)
  have hrc := g.rc
  rw [stack_eq] at hrc
  have hrcA := hrc.2.2
  unfold NativeRustcVm.Apart at hrcA
  rw [hcbn] at hrcA
  have hrcN := hrc.2.1
  unfold NativeRustcVm.NoWrap at hrcN
  have hP : HashPairPre st1.data := by
    unfold HashPairPre
    rw [hdi, hsi', hdx']
    refine ⟨stackOk_callee g.g.st hf1.kept hsp (by rw [stack_eq, hps_eq]),
      RcAt.callee g.rc (g.rc_keep hchg1) hsp g.g.st.1 (by rw [stack_eq, hps_eq]),
      hlm, hln, hrm, hrn, fun i hi ↦ ?_, by unfold NativeRustcX64.NoWrap; rw [ho88]; omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [off_add]
      exact hf1.kept _ (NativeRustcVmX64.Transcript.frame_mapped g.g.st (by decide) _ (by omega))
    · unfold NativeRustcX64.Apart; rw [hcb, hcbn, hps_eq]; omega
    · unfold NativeRustcX64.Apart; rw [hcb, hcbn, hps_eq]; omega
    · unfold NativeRustcX64.Apart; rw [hcb, hcbn, hps_eq, ho88]; omega
    · unfold NativeRustcX64.Apart; rw [ho88]; omega
    · refine g.got.transport (g.got_keep hchg1) ?_ ?_
      · intro l hl
        have hs := (g.got.1 l hl).2.2.1
        change Apart (gotAddr l) 8 (stackBelow m0 1056) 1064 at hs
        change Apart (gotAddr l) 8 (stackBelow st1.data hashPairStack) (hashPairStack + 8)
        rw [hcb, hps_eq]
        unfold Apart at hs ⊢
        omega
      · intro l hl a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have hs := (g.got.1 l hl).2.2.1
          change Apart (gotAddr l) 8 (stackBelow m0 1056) 1064 at hs
          change Apart (gotAddr l) 8 (off (fb m0) 88) 32
          unfold Apart at hs ⊢
          rw [hcbn] at hs
          rw [ho88]
          omega
        · exact (g.got.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine NativeRustcX64.Sym.call_then hpc1 hh hP fun st' hpc' hrsp' ⟨hpost, hso, hsv⟩ ↦ ?_
  rw [hdi] at hpost hso
  rw [hsi', hdx'] at hpost
  have hRn : ∀ q, (NativeRustcVm.InRange (off (fb m0) 88) 32 q ∨
      NativeRustcVm.InRange (stackBelow st1.data hashPairStack) hashPairStack q) →
      (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0 - 208) ∨
      (sp m0 - 120 ≤ q.toNat ∧ q.toNat < sp m0 - 88) := by
    intro q hq
    rcases hq with hq | hq
    · right
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [ho88]; omega), ho88] at hq
      omega
    · left
      rw [hcb, hps_eq, NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hcbn]; omega),
        hcbn] at hq
      omega
  have hf' : Frame m0 208 slots 8 st'.data := by
    refine Frame.call_slots hf1 hsv hrsp' hso (fun p hp i hi hq ↦ ?_) (fun i hi hq ↦ ?_)
    · have := hRn _ hq
      have hp' := slots_le p hp
      have hp'' : 160 ≤ p.1 := by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [g.fo (by omega)] at this
      omega
    · have := hRn _ hq
      rw [g.fo (by omega)] at this
      omega
  obtain ⟨m2, pc2⟩ := st'
  simp only at hpc'
  subst hpc'
  refine cont m2 hf' (fun r v hr hcs ↦ (hsv.1 r hcs).trans (hm1.regs r v hr)) ?_
    (hpost L R (wordsAt_keep hL (by simp; omega) hs1 fun q hq ↦ by
      have := hs1n q hq; simp only [Vector.length_toList]; omega)
      (wordsAt_keep hR (by simp; omega) hs1 fun q hq ↦ by
      have := hs1n q hq; simp only [Vector.length_toList]; omega))
  intro q hq
  rw [← hs1 q fun h ↦ hq (.inl (by have := hs1n q h; omega))]
  exact hso q fun h ↦ hq (by rcases hRn q h with h' | h' <;> [exact .inl (by omega); exact .inr h'])

end

end NativeRustcVmX64.Wire.ClimbLevel
