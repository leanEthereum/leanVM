module

public import NativeRustcArm.SphincsVerify.Parse.Turn
public import NativeRustc.Sphincs.ParseMem

/-!
# The openings' loop: its invariant

FORS opening `c`'s bytes in rustc's layout (`ParseMem.obytesB`, `openings_eq`); the loop's
invariant at `b3` (`AtOpen c`: the frame, the key at `448`, the randomizer at `20048`, the first
`c` openings at `8640`, and the registers `OpenRegs c`), kept by changes in the frame's bytes from
`480` to `20048` past the openings written (`OpenMem.keep`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcArm.Sym
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The bytes the openings' loop keeps and builds: the key, the randomizer, the first `c`
openings. -/
def OpenMem (r : Run) (c : Nat) (d : DataMem) : Prop :=
  BytesAt d (r.off 448) r.pkBytes ∧ BytesAt d (r.off 20048) r.sig.randomizer ∧
    BytesAt d (r.off 8640) ((List.range c).map (obytesB r.sigBytes)).flatten

/-- The loop's registers at turn `c`. -/
def OpenRegs (r : Run) (c : Nat) (m : MachineData) : Prop :=
  Run.RegIs m .X19 r.sigPtr ∧ Run.RegIs m .X20 (r.off 448) ∧ Run.RegIs m .X21 r.msgPtr ∧
    Run.RegIs m .X22 (r.off 484) ∧ Run.RegIs m .X23 (r.sigPtr + BitVec.ofNat 64 96) ∧
    Run.RegIs m .X24 (BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * c)) ∧
    Run.RegIs m .X25 (r.off 8640) ∧ Run.RegIs m .X26 (BitVec.ofNat 64 4224) ∧
    Run.RegIs m .X27 (r.off 19008)

/-- **At `b3`, turn `c`**. -/
def AtOpen (r : Run) (c : Nat) (m : MachineData) : Prop :=
  r.Frame m ∧ OpenMem r c m.dmem ∧ OpenRegs r c m

/-- The registers `OpenRegs` speaks of and X29. -/
abbrev openRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29]

end

public section

theorem fors_fromBytes (b : List UInt8) : (Signature.fromBytes b).fors =
    (List.range 24).map fun c ↦ ⟨slice b (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice b (32 + 176 * c + 16 * z) 16⟩ := rfl

theorem randomizer_fromBytes (b : List UInt8) : (Signature.fromBytes b).randomizer = slice b 0 16 :=
  rfl

/-- **The openings in rustc's layout** are the `obytesB`. -/
theorem openings_eq (r : Run) :
    (r.sig.fors.map openingMem).flatten = ((List.range 24).map (obytesB r.sigBytes)).flatten := by
  unfold Run.sig
  rw [fors_fromBytes, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp, openingMem, obytesB]
  rw [flatten_slices]

theorem length_slice_sigB (r : Run) {a n : Nat} (h : a + n ≤ 7740) :
    (slice r.sigBytes a n).length = n := by
  simp [slice, r.hsig]; omega

variable (r : Run) [Labels]

omit [Labels] in
theorem OpenRegs.of_eq {c : Nat} {m m' : MachineData}
    (h : ∀ x ∈ openRegs, m'.regs.getXReg x = m.regs.getXReg x) (hr : OpenRegs r c m) :
    OpenRegs r c m' := by
  obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hr
  have e : ∀ x ∈ openRegs, ∀ v, Run.RegIs m x v → Run.RegIs m' x v := fun x hx v h' => by
    unfold Run.RegIs at *
    rw [h x hx]
    exact h'
  exact ⟨e .X19 (by simp) _ h19, e .X20 (by simp) _ h20, e .X21 (by simp) _ h21,
    e .X22 (by simp) _ h22, e .X23 (by simp) _ h23, e .X24 (by simp) _ h24, e .X25 (by simp) _ h25,
    e .X26 (by simp) _ h26, e .X27 (by simp) _ h27⟩

omit [Labels] in
theorem OpenRegs.of_saved {c : Nat} {m m' : MachineData} (hS : Saved m m') (hr : OpenRegs r c m) :
    OpenRegs r c m' :=
  OpenRegs.of_eq r (fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hS.1 _ rfl) hr

/-- **The bytes kept** by a change in the frame's bytes `a .. a + n` from `480` to `20048`, past
the first `c` openings. -/
theorem OpenMem.keep (hpre : r.Pre) {c : Nat} (hc : c ≤ 24) {d d' : DataMem} (h : OpenMem r c d)
    {a n : Nat} (hs : SameOutside d d' (InRange (r.off a) n)) (ha : 480 ≤ a) (hn : a + n ≤ 20048)
    (ho : 8640 + 176 * c ≤ a ∨ a + n ≤ 8640) : OpenMem r c d' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨Parse.keep r hpre h1 hs r.hpk (by left; omega) (by decide) (by omega),
    Parse.keep r hpre h2 hs (L := 16)
      (by rw [Run.sig, randomizer_fromBytes]; exact length_slice_sigB r (by decide))
      (by right; omega) (by decide) (by omega),
    Parse.keep r hpre h3 hs (length_openingsB r.hsig hc) (by omega) (by omega) (by omega)⟩

end

end NativeRustcArm.SphincsVerifyProof.Parse
