module

public import NativeRustcVmArm.Wire.ClimbLevel.Found
public import NativeRustcVmArm.Transcript.Glue

/-!
# `climb_level`'s sibling read

No node of key `k ^^^ 1`: `Reader::digest` into SP+24 (`b11`), its tag (`b12`): `None`, or the
digest node `i`'s sibling (`b13`, and at SP+64), then the parent hashed, node `i`'s digest first
(an even key, `b14`) or the sibling's (`b2`): `carry_spec`.
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

/-- A range inside the stack's bytes. -/
theorem Geo.inStack [Labels] (G : Geo m0 bp B) {a q : BitVec 64} {n : Nat}
    (h1 : m0.regs.SP.toNat - climbLevelStack ≤ a.toNat) (h2 : a.toNat + n ≤ m0.regs.SP.toNat)
    (hq : InRange a n q) : InRange (base m0 climbLevelStack) climbLevelStack q := by
  have hsp := G.sp
  rw [Sym.inRange_iff (by omega)] at hq
  rw [Sym.inRange_iff (by rw [G.bN]; omega), G.bN]
  omega

theorem Geo.out24 [Labels] (G : Geo m0 bp B) :
    (base m0 224 + BitVec.ofNat 64 24).toNat = m0.regs.SP.toNat - 200 := by
  have hsp := G.sp
  have := stack224
  rw [toNat_off (by rw [G.bF]; omega), G.bF]
  omega

theorem cls_eq : climbLevelStack = 992 := rfl
theorem rds_eq : readerDigestStack = 48 := rfl

/-- **`Reader::digest`'s precondition** from the frame, into SP+24. -/
theorem Geo.digest_pre [Labels] (G : Geo m0 bp B) {s : MachineData} (hfr : Frm m0 s)
    (hx0 : s.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 24)
    (hx1 : s.regs.X1.toBitVec = rdr m0) {ci : Nat} (hR : ReaderAt s.dmem (rdr m0) bp B ci) :
    ReaderDigestPre s := by
  have hsp := G.sp
  have hN := G.g.st.2.1
  rw [cls_eq] at hsp hN
  have hsb : (stackBelow s readerDigestStack).toNat = m0.regs.SP.toNat - 272 := by
    rw [Ring.stackBelow_eq hfr.sp (show 224 + readerDigestStack ≤ m0.regs.SP.toNat by
      rw [rds_eq]; omega)]
    exact Ring.base_toNat (by rw [rds_eq]; omega)
  have ho := G.out24
  have hsr : _ ∨ _ := G.g.sr
  have hsbp : _ ∨ _ := G.g.sb
  have hrb : _ ∨ _ := G.g.rb
  rw [G.bN, cls_eq] at hsr hsbp
  have := G.rNw
  have := G.g.bpNw
  refine ⟨hfr.stackOk G.g.st (by decide) (by decide), ⟨fun t ht ↦ ?_, ?_⟩, bp, B, ci,
    by rw [hx1]; exact hR, ?_⟩
  · change t < 40 at ht
    show (s.dmem.get? (s.regs.X0.toBitVec + BitVec.ofNat 64 t)).isSome
    rw [hx0, NativeRustcVm.addr_add_add]
    exact hfr.kept _ (Ring.frame_mapped G.g.st (by decide) _ (by omega))
  · show s.regs.X0.toBitVec.toNat + 40 ≤ 2 ^ 64
    rw [hx0, ho]; omega
  · rw [hx0, hx1]
    simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, NativeRustcVm.Apart,
      stackR, ho, rds_eq]
    have hsb' : (stackBelow s 48).toNat = m0.regs.SP.toNat - 272 := hsb
    rw [hsb']
    simp only [false_implies, implies_true, and_true]
    omega

/-- **What `Reader::digest` into SP+24 changes**: within `Keep`. -/
theorem Geo.digest_same [Labels] (G : Geo m0 bp B) {s m2 : MachineData} (hfr : Frm m0 s)
    (hs : SameOutside s.dmem m2.dmem (InAny [⟨base m0 224 + BitVec.ofNat 64 24, 40⟩,
      curRegion (rdr m0), stackR s readerDigestStack])) :
    SameOutside s.dmem m2.dmem (Keep m0 256 256) := by
  have hsp := G.sp
  have hN := G.g.st.2.1
  rw [cls_eq] at hsp hN
  have ho := G.out24
  have hsb : (stackBelow s readerDigestStack).toNat = m0.regs.SP.toNat - 272 := by
    rw [Ring.stackBelow_eq hfr.sp (show 224 + readerDigestStack ≤ m0.regs.SP.toNat by
      rw [rds_eq]; omega)]
    exact Ring.base_toNat (by rw [rds_eq]; omega)
  refine NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, h⟩ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (G.inStack (a := base m0 224 + BitVec.ofNat 64 24) (n := 40)
      (by rw [ho, cls_eq]; omega) (by rw [ho]; omega) h)
  · exact .inr (.inl h)
  · exact .inl (G.inStack (a := stackBelow s readerDigestStack) (n := readerDigestStack)
      (by rw [hsb, cls_eq]; omega) (by rw [hsb, rds_eq]; omega) h)

/-- The memory after the nodes before `i`, kept by a change within `Keep m0 i 256`. -/
theorem Done.keep [Labels] (G : Geo m0 bp B) {i : Nat} {sl : List (Nat × Digest × Bool)}
    {ci : Nat} {d d' : Mem 64} (h : Done m0 bp B c ns i sl ci d) (hi : i ≤ 256)
    (hlt : i < ns.length)
    (hs : SameOutside d d' fun a ↦ Keep m0 i 256 a ∧ ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 a) :
    Done m0 bp B c ns i sl ci d' := by
  have hsl : sl.length = i := by rw [sibsM_length B ns _ c h.hs, List.length_take]; omega
  have hk := NativeRustcVm.SameOutside.mono hs fun _ h ↦ h.1
  exact ⟨h.hs, G.keep_reader hi (le_refl _) hs (fun _ h ↦ h) h.rd,
    G.keep_sibs hi (le_refl _) hk (by simp [hsl]) h.sb,
    G.keep_nxt hi (le_refl _) hk
      (by have := parentsOf_length_le (ns.take i) sl; have := List.length_take_le i ns; omega)
      h.nx⟩

end

end NativeRustcVmArm.Wire.ClimbLevel
