module

public import NativeRustcArm.SphincsVerify.Parse.WordsC

/-!
# The openings' loop: its invariant

The raw signature (`sigBytes_pre10`, `length_sigBytes`); FORS opening `c`'s bytes in rustc's
layout, its path then its secret (`obytes`, `openings_eq`); the loop's invariant at `b12`
(`AtOpen c`: the frame, the message, the raw signature, the key, the randomizer, the first `c`
openings at `16400`, and the registers `OpenRegs c`), kept by changes in the frame's bytes from
`8240` to `27808` past the openings written (`OpenMem.keep`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- FORS opening `c`'s bytes in rustc's layout: its path, then its secret. -/
def obytes (w : Nat → UInt64) (c : Nat) : List UInt8 :=
  slice (sigBytes w) (32 + 176 * c) 160 ++ slice (sigBytes w) (16 + 176 * c) 16

/-- The bytes the openings' loop keeps and builds: the message, the raw signature, the key, the
randomizer, the first `c` openings. -/
def OpenMem (r : Run) (c : Nat) (d : DataMem) : Prop :=
  BytesAt d (r.off 432) r.msg ∧ BytesAt d (r.off 468) (sigBytes r.w) ∧
    BytesAt d (r.off 8208) (pkBytes r.w) ∧ BytesAt d (r.off 27808) r.sig.randomizer ∧
    BytesAt d (r.off 16400) ((List.range c).map (obytes r.w)).flatten

/-- The loop's registers at turn `c`. -/
def OpenRegs (r : Run) (c : Nat) (m : MachineData) : Prop :=
  Run.RegIs m .X19 (r.off 8208) ∧ Run.RegIs m .X20 (r.off 468) ∧ Run.RegIs m .X21 (r.off 26768) ∧
    Run.RegIs m .X22 (r.off 8244) ∧ Run.RegIs m .X23 (r.off 564) ∧
    Run.RegIs m .X24 (BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * c)) ∧
    Run.RegIs m .X25 (r.off 16400) ∧ Run.RegIs m .X26 (BitVec.ofNat 64 4224)

/-- **At `b12`, turn `c`**. -/
def AtOpen (r : Run) (c : Nat) (m : MachineData) : Prop :=
  r.Frame m ∧ OpenMem r c m.dmem ∧ OpenRegs r c m

/-- The registers `OpenRegs` speaks of and X29. -/
abbrev openRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29]

end

public section

theorem sigBytes_pre10 (w : Nat → UInt64) : sigBytes w = pre10 w ++ wb w 973 4 := by
  rw [sigBytes_pieces]
  simp only [pre10, pre9, pre7, pre5, List.append_assoc]

theorem length_sigBytes (w : Nat → UInt64) : (sigBytes w).length = 7740 := by
  rw [sigBytes_pre10, List.length_append, length_pre10, length_wb]

theorem length_slice_sig (w : Nat → UInt64) {a n : Nat} (h : a + n ≤ 7740) :
    (slice (sigBytes w) a n).length = n := by
  simp [slice, length_sigBytes]; omega

theorem length_obytes (w : Nat → UInt64) {c : Nat} (hc : c < 24) : (obytes w c).length = 176 := by
  rw [obytes, List.length_append, length_slice_sig w (by omega), length_slice_sig w (by omega)]

theorem length_openings (w : Nat → UInt64) : ∀ {c : Nat}, c ≤ 24 →
    ((List.range c).map (obytes w)).flatten.length = 176 * c
  | 0, _ => rfl
  | c + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      length_openings w (by omega)]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      length_obytes w (show c < 24 by omega)]
    omega

theorem fors_fromBytes (b : List UInt8) : (Signature.fromBytes b).fors =
    (List.range 24).map fun c ↦ ⟨slice b (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice b (32 + 176 * c + 16 * z) 16⟩ := rfl

theorem randomizer_fromBytes (b : List UInt8) : (Signature.fromBytes b).randomizer = slice b 0 16 :=
  rfl

/-- **The openings in rustc's layout** are the `obytes`. -/
theorem openings_eq (r : Run) :
    (r.sig.fors.map openingMem).flatten = ((List.range 24).map (obytes r.w)).flatten := by
  unfold Run.sig
  rw [fors_fromBytes, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp, openingMem, obytes]
  rw [flatten_slices]

theorem randomizer_eq (r : Run) : r.sig.randomizer = slice (pre10 r.w) 0 16 := by
  unfold Run.sig
  rw [randomizer_fromBytes, sigBytes_pre10]
  simp only [slice, List.drop_zero]
  rw [List.take_append_of_le_length (by rw [length_pre10]; decide)]

variable (r : Run) [Labels]

omit [Labels] in
theorem OpenRegs.of_eq {c : Nat} {m m' : MachineData}
    (h : ∀ x ∈ openRegs, m'.regs.getXReg x = m.regs.getXReg x) (hr : OpenRegs r c m) :
    OpenRegs r c m' := by
  obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26⟩ := hr
  have e : ∀ x ∈ openRegs, ∀ v, Run.RegIs m x v → Run.RegIs m' x v := fun x hx v h' => by
    unfold Run.RegIs at *
    rw [h x hx]
    exact h'
  exact ⟨e .X19 (by simp) _ h19, e .X20 (by simp) _ h20, e .X21 (by simp) _ h21,
    e .X22 (by simp) _ h22, e .X23 (by simp) _ h23, e .X24 (by simp) _ h24, e .X25 (by simp) _ h25,
    e .X26 (by simp) _ h26⟩

omit [Labels] in
theorem OpenRegs.of_saved {c : Nat} {m m' : MachineData} (hS : Saved m m') (hr : OpenRegs r c m) :
    OpenRegs r c m' :=
  OpenRegs.of_eq r (fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hS.1 _ rfl) hr

/-- **The bytes kept** by a change in the frame's bytes `a .. a + n` from `8240` to `27808`, past
the first `c` openings. -/
theorem OpenMem.keep (hpre : r.Pre) {c : Nat} (hc : c ≤ 24) {d d' : DataMem} (h : OpenMem r c d)
    {a n : Nat} (hs : SameOutside d d' (InRange (r.off a) n)) (ha : 8240 ≤ a) (hn : a + n ≤ 27808)
    (ho : 16400 + 176 * c ≤ a ∨ a + n ≤ 16400) : OpenMem r c d' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨Parse.keep r hpre h1 hs (length_wb r.w 4 4) (by left; omega) (by decide) (by omega),
    Parse.keep r hpre h2 hs (length_sigBytes r.w) (by left; omega) (by decide) (by omega),
    Parse.keep r hpre h3 hs (length_wb r.w 0 4) (by left; omega) (by decide)
      (by omega),
    Parse.keep r hpre h4 hs (L := 16)
      (by rw [randomizer_eq, slice]; simp [length_pre10]) (by right; omega)
      (by decide) (by omega),
    Parse.keep r hpre h5 hs (length_openings r.w hc) (by omega) (by omega) (by omega)⟩

end

end NativeRustcArm.SphincsVerifyProof.Parse
