module

public import NativeRustcArm.Sym
public import NativeRustcArm.Spec.Mem

/-!
# What `memcpy`'s and `memset`'s proofs share

The alignment tests' meaning (`align_or3`, `align_or2`: the length's low three bits are zero where
the test passes); a loop iteration extending the bytes written so far (`extend`); mapped bytes
staying mapped (`Mapped.of_kept`); a register-offset address (`idx`, `eval_idx`) and address
arithmetic.
-/

namespace NativeRustcArm.Mem

open NativeRustcArm.Sym

public section

theorem mod8_of_bits (x : BitVec 64) (h0 : x.getLsbD 0 = false) (h1 : x.getLsbD 1 = false)
    (h2 : x.getLsbD 2 = false) : x.toNat % 8 = 0 := by
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not] at h0 h1 h2
  omega

section
variable [Labels] {env : Env}

/-- `memcpy`'s test `orr w8, w1, w0; orr w8, w8, w2; tst x8, #7`: where it is zero, so are the
third operand's low three bits. -/
theorem align_or3 {A B C : Sym}
    (h : (SBool.cmp .eq .W64 (.bin .and .W64 (.bin .orr .W32 (.bin .orr .W32 A (.un .trunc .W32 B))
      (.un .trunc .W32 C)) (.lit 7)) (.lit 0)).eval env = true) :
    (C.eval env).toNat % 8 = 0 := by
  sym_simp at h
  simp only [beq_iff_eq] at h
  apply mod8_of_bits
  · have := congrArg (fun x : BitVec 64 => x.getLsbD 0) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.2
  · have := congrArg (fun x : BitVec 64 => x.getLsbD 1) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.2
  · have := congrArg (fun x : BitVec 64 => x.getLsbD 2) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.2

/-- `memset`'s test `orr w8, w2, w0; tst x8, #7`: where it is zero, so are the first operand's low
three bits. -/
theorem align_or2 {A B : Sym}
    (h : (SBool.cmp .eq .W64 (.bin .and .W64 (.bin .orr .W32 A (.un .trunc .W32 B)) (.lit 7))
      (.lit 0)).eval env = true) :
    (A.eval env).toNat % 8 = 0 := by
  sym_simp at h
  simp only [beq_iff_eq] at h
  apply mod8_of_bits
  · have := congrArg (fun x : BitVec 64 => x.getLsbD 0) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.1
  · have := congrArg (fun x : BitVec 64 => x.getLsbD 1) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.1
  · have := congrArg (fun x : BitVec 64 => x.getLsbD 2) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.1

end

/-- The address `[b, i]` (`ldr`/`str` with a register offset), as the executor builds it. -/
@[expose] def idx (b i : XReg) : Sym :=
  .bin .add .W64 (.reg b) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg i))

theorem eval_idx [Labels] (env : Env) (b i : XReg) :
    (idx b i).eval env = env.regs b + env.regs i := by
  simp [idx, Sym.eval, BinOp.apply, UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned]

theorem addr_add3 (a : BitVec 64) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 0 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc a, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    Nat.add_zero]

theorem add_ofInt_one (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofInt 64 1 = a + BitVec.ofNat 64 (i + 1) := by
  rw [show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytesAt_nil (d : DataMem) (a : BitVec 64) : BytesAt d a [] := fun _ h => absurd h (by simp)

theorem sameOutside_of_eq {d d' : DataMem} (h : d' = d) (R : BitVec 64 → Prop) :
    SameOutside d d' R := fun _ _ => by rw [h]

/-- Mapped bytes of a memory are mapped in one that keeps it. -/
theorem Mapped.of_kept {d d' : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n)
    (hk : Kept d d') : Mapped d' a n :=
  fun i hi => hk _ (h i hi)

/-- **One iteration of a loop writing `f`'s bytes**: from the bytes `f 0 … f (i-1)` at `d` (memory
otherwise `m₀`'s), a step writing `f i … f (i+w-1)` after them and nothing else gives the bytes
`f 0 … f (i+w-1)` at `d`, memory otherwise `m₀`'s. -/
theorem extend {m₀ st st' : DataMem} {d : BitVec 64} {i w n : Nat} {f : Nat → UInt8}
    (hnw : NoWrap d n) (hle : i + w ≤ n)
    (hc : BytesAt st d ((List.range i).map f)) (hs : SameOutside m₀ st (InRange d i))
    (hw : ∀ j < w, st'.get? (d + BitVec.ofNat 64 (i + j)) = some (f (i + j)))
    (hout : ∀ a : BitVec 64, ¬(d.toNat + i ≤ a.toNat ∧ a.toNat < d.toNat + i + w) →
      st'.get? a = st.get? a) :
    BytesAt st' d ((List.range (i + w)).map f) ∧ SameOutside m₀ st' (InRange d (i + w)) := by
  unfold NoWrap at hnw
  constructor
  · intro j hj
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    by_cases hji : j < i
    · rw [hout _ (by rw [toNat_add_ofNat d j (by omega)]; omega)]
      have := hc j (by simp; omega)
      simpa using this
    · have := hw (j - i) (by omega)
      rw [show i + (j - i) = j by omega] at this
      exact this
  · intro a ha
    rw [inRange_iff (by omega)] at ha
    rw [hout a (by omega), hs a (by rw [inRange_iff (by omega)]; omega)]

end

end NativeRustcArm.Mem
