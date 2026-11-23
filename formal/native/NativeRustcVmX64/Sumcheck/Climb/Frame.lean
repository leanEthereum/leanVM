module

public import NativeRustcVmX64.Sumcheck.Climb.Exec
public import NativeRustcVmX64.Spec.Sumcheck

/-!
# `climb`'s frame (x86-64)

The frame (`fa`, 160 bytes below the entry's RSP, `Frame` with RSP at offset `8`): the
accumulator at `8`, the sibling at `40`, the output's address at `72`, `hash_pair`'s output at
`80`, the pushed registers from `112`. `Fr m0 D m`: the frame with the accumulator `D` and the
output's address, memory changed only in `climb`'s stack. `Inv`: the loop head at level `l`;
`Called`: after a level's `hash_pair`, its output `D` at `80`, the head's registers kept.

The geometry (`Geo`): the entry's RSP, the frame, the stack as numbers.
-/

namespace NativeRustcVmX64.Sumcheck.Climb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Climb NativeRustcVmX64.Transcript
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck NativeRustcVm.Transcript

@[expose] public section

/-- The frame: 160 bytes below the entry's RSP. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 160

/-- The position at the entry (RDX). -/
abbrev q0 (m0 : MachineData) : UInt64 := .ofBitVec (reg m0 .rdx)

/-- The frame with the accumulator `D`. -/
structure Fr (m0 : MachineData) (D : Digest) (m : MachineData) : Prop where
  frame : Frame m0 160 slots 8 m
  acc : NativeRustcVm.WordsAt m.dmem (off (fa m0) 8) D.toList
  out : NativeRustcVm.WordAt m.dmem (off (fa m0) 72) (.ofBitVec (reg m0 .rdi))
  same : NativeRustcVm.SameOutside m0.dmem m.dmem
    (NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack)

/-- **The loop head** at level `l`. -/
structure Inv (m0 : MachineData) (N : Digest) (P : Array Digest) (l : Nat) (m : MachineData) :
    Prop where
  st : Fr m0 (climbTo N (q0 m0) P l).1 m
  lt : l < P.size
  r12 : reg m .r12 = (climbTo N (q0 m0) P l).2.toBitVec
  r13 : (reg m .r13).toNat = 4 * l
  r14 : (reg m .r14).toNat = P.size - l
  r15 : reg m .r15 = reg m0 .rcx
  rbp : reg m .rbp = off (fa m0) 8
  rbx : reg m .rbx = off (fa m0) 40

/-- **After `hash_pair`**: its output `D`, the registers of the head `mh`. -/
structure Called (m0 mh : MachineData) (D : Digest) (m : MachineData) : Prop where
  frame : Frame m0 160 slots 8 m
  hashed : NativeRustcVm.WordsAt m.dmem (off (fa m0) 80) D.toList
  out : NativeRustcVm.WordAt m.dmem (off (fa m0) 72) (.ofBitVec (reg m0 .rdi))
  same : NativeRustcVm.SameOutside m0.dmem m.dmem
    (NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack)
  regs : ∀ r, calleeSaved r = true → reg m r = reg mh r

/-- The geometry of the entry's RSP. -/
structure Geo (m0 : MachineData) : Prop where
  le : 1008 ≤ (rspOf m0).toNat
  lt : (rspOf m0).toNat + 8 ≤ 2 ^ 64

end

public section

theorem climbStack_eq : climbStack = 1008 := rfl
theorem hashPairStack_eq : hashPairStack = 848 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 112 ≤ p.1 := by decide

variable {m0 : MachineData}

theorem Geo.fa_toNat (g : Geo m0) : (fa m0).toNat = (rspOf m0).toNat - 160 :=
  stackBelow_toNat (by have := g.le; omega)

theorem Geo.stk (g : Geo m0) :
    (stackBelow m0 climbStack).toNat = (rspOf m0).toNat - 1008 :=
  stackBelow_toNat (by have := g.le; rw [climbStack_eq]; omega)

theorem Geo.off_toNat (g : Geo m0) {o : Nat} (ho : o < 168) :
    (off (fa m0) o).toNat = (rspOf m0).toNat - 160 + o := by
  have := g.le; have := g.lt
  rw [toNat_off (by rw [g.fa_toNat]; omega), g.fa_toNat]

theorem Geo.noWrap (g : Geo m0) {o n : Nat} (h : o + n ≤ 168) (ho : o < 168) :
    NativeRustcVm.NoWrap (off (fa m0) o) n := by
  have := g.le; have := g.lt
  unfold NativeRustcVm.NoWrap
  rw [g.off_toNat ho]
  omega

/-- The callee's stack, below the frame. -/
theorem Geo.callee (g : Geo m0) {d : MachineData} (hsp : rspOf d = fa m0) :
    (stackBelow d hashPairStack).toNat = (rspOf m0).toNat - 1008 := by
  have := g.le
  rw [stackBelow_callee hsp (by rw [hashPairStack_eq]; omega), stackBelow_toNat (by
    rw [hashPairStack_eq]; omega), hashPairStack_eq]

theorem Geo.of_pre {N : Digest} {P : Array Digest} [Labels] (h : ClimbPre N P m0) : Geo m0 :=
  ⟨by have := h.1.1; rw [climbStack_eq] at this; exact this, h.1.2.1⟩

/-- The frame's bytes from `o` are apart from the callee's stack. -/
theorem Geo.apart_callee (g : Geo m0) {d : MachineData} (hsp : rspOf d = fa m0) {o n : Nat}
    (ho : 8 ≤ o) (ho' : o < 168) :
    NativeRustcVm.Apart (off (fa m0) o) n (stackBelow d hashPairStack) (hashPairStack + 8) := by
  have := g.le
  unfold NativeRustcVm.Apart
  rw [g.off_toNat (by omega), g.callee hsp, hashPairStack_eq]
  omega

/-- What is apart from `climb`'s stack is apart from the frame's bytes from `o`. -/
theorem Geo.apart_of_stack (g : Geo m0) {a : BitVec 64} {n o k : Nat}
    (h : NativeRustcVm.Apart a n (stackBelow m0 climbStack) (climbStack + 8)) (hk : o + k ≤ 168)
    (ho : o < 168) :
    NativeRustcVm.Apart a n (off (fa m0) o) k := by
  have := g.le
  unfold NativeRustcVm.Apart at h ⊢
  rw [g.stk, climbStack_eq] at h
  rw [g.off_toNat (by omega)]
  omega

/-- The frame below its return address is in `climb`'s stack. -/
theorem Geo.inRange_stack (g : Geo m0) {q : BitVec 64}
    (h : NativeRustcVm.InRange (fa m0) 160 q) :
    NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack q :=
  inRange_frame_stack g.lt (by rw [climbStack_eq]; exact g.le) (by rw [climbStack_eq]; omega) h

/-- `hash_pair`'s output and stack miss the frame's bytes at `j` outside its output. -/
theorem Geo.notR (g : Geo m0) {d : MachineData} (hsp : rspOf d = fa m0) {j : Nat}
    (hj : 8 ≤ j ∧ j < 80 ∨ 112 ≤ j ∧ j < 168) :
    ¬ (NativeRustcVm.InRange (off (fa m0) 80) 32 (off (fa m0) j) ∨
      NativeRustcVm.InRange (stackBelow d hashPairStack) hashPairStack (off (fa m0) j)) := by
  have := g.le; have := g.lt
  have hs := g.callee hsp
  rw [inRange_iff' (g.noWrap (by omega) (by omega)), inRange_iff' (by
      unfold NativeRustcVm.NoWrap; rw [hs, hashPairStack_eq]; omega),
    g.off_toNat (by omega), g.off_toNat (by omega), hs, hashPairStack_eq]
  omega

/-- `hash_pair`'s stack is in `climb`'s. -/
theorem Geo.callee_in (g : Geo m0) {d : MachineData} (hsp : rspOf d = fa m0) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d hashPairStack) hashPairStack q) :
    NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack q :=
  (inRange_callee hsp g.lt (by rw [climbStack_eq]; exact g.le)
    (by rw [climbStack_eq, hashPairStack_eq]) h).1

/-- `hash_pair`'s output in the frame is in `climb`'s stack. -/
theorem Geo.out_in (g : Geo m0) {q : BitVec 64}
    (h : NativeRustcVm.InRange (off (fa m0) 80) 32 q) :
    NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack q := by
  have := g.le; have := g.lt
  rw [inRange_iff' (g.noWrap (by omega) (by omega)), g.off_toNat (by omega)] at h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [g.stk, climbStack_eq]; omega), g.stk,
    climbStack_eq]
  omega

/-- Digest `l` of a path's words. -/
theorem wordsAt_path {d : Mem 64} {a : BitVec 64} {P : Array Digest}
    (h : NativeRustcVm.WordsAt d a (pathWords P)) {l : Nat} (hl : l < P.size) :
    NativeRustcVm.WordsAt d (off a (32 * l)) P[l].toList := by
  unfold NativeRustcVm.WordsAt pathWords at *
  rw [List.flatMap_assoc] at h
  have := NativeRustcVm.BytesAt.flatMap_getElem
    (f := fun D : Digest ↦ D.toList.flatMap NativeRustcVm.wordBytes) (k := 32)
    (fun D ↦ by rw [NativeRustcVm.length_wordsBytes]; simp) h (i := l) (by simpa using hl)
  simpa using this

end

end NativeRustcVmX64.Sumcheck.Climb
