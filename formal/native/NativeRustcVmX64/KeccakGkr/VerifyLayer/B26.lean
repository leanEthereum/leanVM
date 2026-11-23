module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Iota1

/-!
# `verify_layer` on x86-64: into ι's first loop

`b26` (from `SG`, after the segment kernel) spills the bit weights' and the point's addresses,
loads `KECCAK_RC[11 - step]` into R9 and the first segment's weight into RDI, RSI, clears the
sum and enters `NativeRustcVmX64.Vm.VerifyLayer.label_21` with no bit summed (`IA 0`): `b26Run`. Tools: an element of
the frame loaded (`frLoad`), the step's low word (`stepLoad`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

public section

/-- **An element of the frame's elements** at `o`, its two words loaded. -/
theorem frLoad [Labels] {m0 : MachineData} {xs : Array EW} {d : MachineData}
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    (h : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) o) xs.toList) {j : Nat}
    (hj : j < xs.size) :
    ewArg ((envB m0 d ex vars ret).load 0 (o + 16 * j) 8)
      ((envB m0 d ex vars ret).load 0 (o + 8 + 16 * j) 8) = xs.getD j 0 := by
  have := h.getElem (i := j) (by rw [Array.length_toList]; exact hj)
  rw [NativeRustcVm.ewAt_iff, Array.getElem_toList] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
  have hb0 : (envB m0 d ex vars ret).base 0 = stackBelow m0 2016 := rfl
  have l0 : (envB m0 d ex vars ret).load 0 (o + 16 * j) 8 = xs[j].c0.toBitVec := by
    apply load_of_wordAt
    rw [hb0, show stackBelow m0 2016 + BitVec.ofNat 64 (o + 16 * j) =
      off (stackBelow m0 2016) o + BitVec.ofNat 64 (16 * j) by unfold off; bv_omega]
    exact this.1
  have l1 : (envB m0 d ex vars ret).load 0 (o + 8 + 16 * j) 8 = xs[j].c1.toBitVec := by
    apply load_of_wordAt
    rw [hb0, show stackBelow m0 2016 + BitVec.ofNat 64 (o + 8 + 16 * j) =
      off (stackBelow m0 2016) o + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8 by
        unfold off; bv_omega]
    exact this.2
  rw [l0, l1, ewArg_ew]

/-- **The step**, the low word of the frame's word at `56`. -/
theorem stepLoad [Labels] {m0 d : MachineData} {ex : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hst : stepN m0 < 12)
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 56) (.ofBitVec (reg m0 .rdx))) :
    (envB m0 d ex vars ret).load 0 56 4 = BitVec.ofNat 64 (stepN m0) := by
  rw [ofBitVec_eq] at h
  exact load4_small hst h

/-- `8 (b - step)`, the step at the frame's `56`. -/
theorem idxLoad [Labels] {m0 d : MachineData} {ex : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hst : stepN m0 < 12)
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 56) (.ofBitVec (reg m0 .rdx)))
    {b : Nat} (hb1 : 11 ≤ b) (hb2 : b < 2 ^ 28) :
    (Sym.bin .shl .W32 (.bin .sub .W32 (.lit b) (.load 0 56 4)) (.lit 3)).eval
      (envB m0 d ex vars ret) = BitVec.ofNat 64 (8 * (b - stepN m0)) := by
  simp only [Sym.eval]
  rw [stepLoad hst h]
  exact idx8 b _ (by omega) hb2

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState}

/-- **Into ι's first loop**: `b26`. -/
theorem b26Run (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : SG m0 a c p s1 d) {R : MachineState → Prop}
    (cont : ∀ d', IA m0 a c p s1 0 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b30Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b26Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hst : stepN m0 < 12 := pre_step hpre
  have hwf : (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).WF :=
    wfR hpre h.body (r := rcRegion) (by simp)
  have h56 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 56) (.ofBitVec (reg m0 .rdx)) :=
    h.sp (56, _) (by simp [spills2])
  have h80 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 80) (.ofBitVec (sA m0)) :=
    h.sp (80, _) (by simp [spills2])
  have hi : i11.eval (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0) =
      BitVec.ofNat 64 (8 * (11 - stepN m0)) := idxLoad hst h56 (by decide) (by decide)
  have hm : Match (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0) (fr 24 [192] [(rcL, 1)] [(i11, 89)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ ⟨rfl, trivial⟩
      ⟨by show (i11.eval (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0)).toNat < 89
          rw [hi, BitVec.toNat_ofNat]; omega, trivial⟩ trivial
  refine Body.blk (o' := 24) g h.body hwf (blk hp b26_in_code (by simp [b26])) e26 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  simp only [PcOk] at hpc1
  rw [lbl hp b30_in_code rfl] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hm1 hb1
  subst hpc1
  have e : ∀ r, (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  have hl80 : (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).load 0 80 8 = sA m0 := fload8 h80
  have hfrA := frSame_blk (o := 136) (n := 1880) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hfrB := frSame_blk (o := 24) (n := 96) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hkr : ∀ r ∈ [Reg64.r12, .r13], reg d1 r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hw120 := fwW (o := 120) hm1 rfl rfl (by decide) (by decide +kernel)
    (w := .ofBitVec (sA m0 + 25600#64)) (by simp only [Sym.eval, hl80, add64])
  have hw128 := fwW (o := 128) hm1 rfl rfl (by decide) (by decide +kernel)
    (w := .ofBitVec (cA m0 + 280#64)) (by simp only [Sym.eval, e, h.r14, add64])
  have hsp3 : FWs m0 d1.dmem (spills3 m0 c) := by
    have h3 := spills3_sub h.sp
    intro q hq
    simp only [spills3, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hfrB.sub (o' := 32) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrB.sub (o' := 40) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrB.sub (o' := 48) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrB.sub (o' := 56) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrB.sub (o' := 64) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrB.sub (o' := 80) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrB.sub (o' := 96) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
    · exact (hfrA.sub (o' := 224) (n' := 8) (by decide) (by decide)).word
        (h3 _ (by simp [spills3])) (by decide)
  refine cont d1 ⟨⟨hb1, ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts, ?_, ?_,
    ?_, ?_, h.psize, h.ssize⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · exact (hfrA.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews h.prod
      (by rw [Array.length_toList, h.psize])
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hsp3 q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hw120
      · exact hw128
  · exact (hfrA.sub (o' := 232) (n' := 64) (by decide) (by decide)).ews h.seg
      (by rw [Array.length_toList]; have := segK_le4 (pre_seg hpre); omega)
  · rw [hkr .r12 (by simp), hkr .r13 (by simp)]; exact h.acc
  · rw [show reg d1 .rcx = _ from hm1.regs .rcx _ rfl]; rfl
  · rw [show reg d1 .r10 = _ from hm1.regs .r10 _ rfl]
    simp only [Sym.eval, hl80, add64]
  · rw [show reg d1 .r9 = _ from hm1.regs .r9 _ rfl]
    change (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).load 1 (0 + (i11.eval (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0)).toNat) 8 = _
    rw [hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.zero_add]
    exact rcLoad hpre hWo h.body (by omega)
  · rw [show reg d1 .rdx = _ from hm1.regs .rdx _ rfl, show reg d1 .rax = _ from hm1.regs .rax _ rfl]
    rfl
  · rw [show reg d1 .rdi = _ from hm1.regs .rdi _ rfl, show reg d1 .rsi = _ from hm1.regs .rsi _ rfl]
    exact frLoad (o := 232) (j := 0) h.seg (by have := h.ssize; omega)
  · rw [show reg d1 .r15 = _ from hm1.regs .r15 _ rfl]
    exact hl80
  · rw [show reg d1 .r8 = _ from hm1.regs .r8 _ rfl]
    rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
