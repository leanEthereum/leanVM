module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Step
public import NativeRustcVmX64.Sumcheck.Common

/-!
# `verify_stacked_opening`: the frame's words (x86-64)

`FW d m0 L` (`Basic`): the frame holds word `v` at offset `o` for each `(o, v)` of `L`. Kept by a
call (`FW.call`, the frame's bytes unchanged) and by a block whose writes miss the words
(`FW.block`, checked by `missAll`); a block's write (`fw_write`); read back by a block
(`fw_load`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir

@[expose] public section

/-- No write of `S` into region 0 overlaps the words at the offsets `os`, each below `520`. -/
def missAll (os : List Nat) (S : SState) : Bool :=
  os.all fun o ↦ decide (o + 8 ≤ 520) &&
    S.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + 8 ≤ w.off)

end

public section

variable {m0 : MachineData}

theorem FW.nil (d : Mem 64) (m0 : MachineData) : FW d m0 [] := fun _ h ↦ by cases h

theorem FW.cons {d : Mem 64} {o : Nat} {v : UInt64} {L : List (Nat × UInt64)}
    (h : NativeRustcVm.WordAt d (off (stackBelow m0 512) o) v) (hL : FW d m0 L) :
    FW d m0 ((o, v) :: L) := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst hp; exact h
  · exact hL p hp

theorem FW.get {d : Mem 64} {L : List (Nat × UInt64)} (h : FW d m0 L) {o : Nat} {v : UInt64}
    (hp : (o, v) ∈ L) : NativeRustcVm.WordAt d (off (stackBelow m0 512) o) v := by
  have := h (o, v) hp
  exact this

theorem FW.sub {d : Mem 64} {L L' : List (Nat × UInt64)} (h : FW d m0 L) (hs : ∀ p ∈ L', p ∈ L) :
    FW d m0 L' := fun p hp ↦ h p (hs p hp)

/-- **Across a call** keeping the frame's bytes. -/
theorem FW.call {d d' : Mem 64} {L : List (Nat × UInt64)} (h : FW d m0 L)
    (hfs : FrameSame m0 d d') (hL : ∀ p ∈ L, p.1 + 8 ≤ 520) : FW d' m0 L := fun p hp ↦ by
  refine NativeRustcVm.BytesAt.of_sameOutside (R := fun q ↦ ¬ NativeRustcVm.InRange
    (stackBelow m0 512) 520 q) (h p hp) (fun q hq ↦ hfs q (Classical.not_not.mp hq)) fun i hi hq ↦
      hq ?_
  rw [NativeRustcVm.length_wordBytes] at hi
  have := hL p hp
  rw [off_add]
  exact inRange_off_self (by omega) (by omega)

theorem missAll_spec {os : List Nat} {S : SState} (h : missAll os S = true) {o : Nat}
    (ho : o ∈ os) : o + 8 ≤ 520 ∧ ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + 8 ≤ w.off := by
  unfold missAll at h
  rw [List.all_eq_true] at h
  have := h o ho
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at this
  refine ⟨this.1, fun w hw hr ↦ ?_⟩
  rcases this.2 w hw with (h1 | h1) | h1
  · exact absurd hr h1
  · exact .inl h1
  · exact .inr h1

/-- **Across a block** whose writes miss the words. -/
theorem FW.block [Labels] {st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 st 512 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') (hin : writesIn S = true)
    {L : List (Nat × UInt64)} (h : FW st.dmem m0 L) (hmiss : missAll (L.map (·.1)) S = true) :
    FW st'.dmem m0 L := fun p hp ↦ by
  obtain ⟨h1, h2⟩ := missAll_spec hmiss (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact NativeRustcVmX64.Sumcheck.keepW hwf hm hin (by omega) h2 (h p hp)

/-- **Across a block** whose writes miss the words at the offsets `os` (`L`'s, given
explicitly so that `missAll` is decided on literals). -/
theorem FW.block_os [Labels] {st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 st 512 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') (hin : writesIn S = true)
    {L : List (Nat × UInt64)} (h : FW st.dmem m0 L) (os : List Nat) (hos : L.map (·.1) = os)
    (hmiss : missAll os S = true) : FW st'.dmem m0 L :=
  FW.block hwf hm hin h (hos ▸ hmiss)

/-- The words' offsets in the frame, checked on literals. -/
theorem le_of_map {L : List (Nat × UInt64)} (os : List Nat) (hos : L.map (·.1) = os)
    (h : ∀ o ∈ os, o + 8 ≤ 520) : ∀ p ∈ L, p.1 + 8 ≤ 520 := fun p hp ↦
  h p.1 (hos ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- A register a block keeps: its value in the block's start state. -/
theorem regKeep [Labels] {d m : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine d rs vs ret) S m) (r : Reg64)
    (h : S.reg r = some (.reg r)) : reg m r = reg d r :=
  hm.regs r _ h

/-- **A block's write** of `v` at offset `o` of the frame. -/
theorem fw_write [Labels] {st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') {o : Nat} (ho : o + 8 ≤ 520) {v : Sym}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt st'.dmem (off (stackBelow m0 512) o)
      (UInt64.ofBitVec (v.eval (frameEnv m0 st 512 rest vars ret))) :=
  wordAt_write hm (r := 0) rfl ho hw

/-- **A word read back** by a block of the frame. -/
theorem fw_load {st : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {L : List (Nat × UInt64)} (h : FW st.dmem m0 L) {o : Nat} {v : UInt64}
    (hp : (o, v) ∈ L) : (frameEnv m0 st 512 rest vars ret).load 0 o 8 = v.toBitVec :=
  load_ofMachine (r := 0) rfl (h.get hp)

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
