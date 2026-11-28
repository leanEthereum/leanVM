module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Infix
public import NativeRustcArm.Hasher.Bytes
public import NativeRustc.Bytes
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Wire.Rep

/-!
# Helpers of the wire decoder's proofs

What the executor loads (`load_word`, `load_byte`), what a write of a word stores
(`bytesAt_write_word`), `or`s and shifts of disjoint bits as sums (`toNat_or_add`, `toNat_shl`),
`ubfm` as a shift, and a block of a placed function in the program (`infix_of`).
-/

namespace NativeRustcVmArm.Wire

open NativeRustcArm NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [hw, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- **A word at a region's offset** is what the environment loads there. -/
theorem load_word {env : Env} {r off : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) v) :
    env.load r off 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (NativeRustcVm.length_wordBytes v) h, ofInt_ofBytes_wordBytes]

theorem load_byte {env : Env} {r off : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r + BitVec.ofNat 64 off) = some b) :
    (env.load r off 1).toNat = b.toNat := by
  have hl := Env.load_of_bytesAt (env := env) (r := r) (off := off) (bs := [b]) (n := 1) rfl
    (fun i hi ↦ by
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi
      simpa using h)
  rw [hl, ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  show (0 * 256 + b.toNat) % 2 ^ 64 = b.toNat
  have := b.toNat_lt
  omega

/-- The bytes of a 64-bit value: the word's. -/
theorem byteOf_range (x : BitVec 64) : (List.range 8).map (byteOf x) = wordBytes (UInt64.ofBitVec x) :=
  (Hasher.wordBytes_ofBitVec x).symm

/-- An `or` of a small value and a multiple of `2 ^ k` is their sum. -/
theorem toNat_or_add {a b : BitVec 64} {k : Nat} (ha : a.toNat < 2 ^ k) (hb : 2 ^ k ∣ b.toNat) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_or, NativeRustc.lor_eq_add ha hb]

/-- A shift without overflow is a product. -/
theorem toNat_shl {x : BitVec 64} {k : Nat} (h : x.toNat * 2 ^ k < 2 ^ 64) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsl x, #8` (`ubfm x, #56, #55`). -/
theorem ubfm_lsl8 (x : BitVec 64) : UnOp.apply (.ubfm 56 55) .W64 x = x <<< 8 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `lsl x, #3` (`ubfm x, #61, #60`). -/
theorem ubfm_lsl3 (x : BitVec 64) : UnOp.apply (.ubfm 61 60) .W64 x = x <<< 3 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem ult_apply (a b : BitVec 64) : CmpOp.apply .ult .W64 a b = decide (a.toNat < b.toNat) := by
  simp [CmpOp.apply, Sym.low_W64, BitVec.ult]

theorem eq_apply (a b : BitVec 64) : CmpOp.apply .eq .W64 a b = decide (a.toNat = b.toNat) := by
  simp only [CmpOp.apply, Sym.low_W64]
  by_cases h : a = b
  · subst h; simp
  · rw [show (a == b) = false from beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem toNat_add_one {v : BitVec 64} (h : v.toNat < 256) :
    (v + BitVec.ofNat 64 1).toNat = v.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem toNat_sub_one {v : BitVec 64} (h : 0 < v.toNat) :
    (v - BitVec.ofNat 64 1).toNat = v.toNat - 1 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := v.isLt; omega

/-- **The writes of a block** all within bytes `o` to `o + n` of region `r0`: memory changed only
there. -/
theorem Match.sameOutside_in [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) (hwf : env.WF) {r0 : Nat} {b : BitVec 64} {sz o n : Nat}
    (hb : env.regions[r0]? = some (b, sz)) (hon : o + n ≤ sz)
    (hw : ∀ w ∈ S.mem, w.r = r0 ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n) :
    SameOutside env.mem0 m.dmem (InRange (b + BitVec.ofNat 64 o) n) := by
  intro p hp
  refine hm.get?_mem0 hwf fun ⟨w, hwS, b', sz', hb', h1, h2⟩ ↦ hp ?_
  obtain ⟨hr, ho, hn⟩ := hw w hwS
  rw [hr, hb] at hb'
  cases hb'
  have hnw := hwf.noWrap r0 b sz hb
  have ho' : (b + BitVec.ofNat 64 o).toNat = b.toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [inRange_iff (by omega), ho']
  omega

variable [NativeRustcArm.Host]

/-- A block of a placed function is in the program. -/
theorem infix_of {F b : List Directive} {k j : Nat} (hb : b.IsInfixAt F j) (hne : b ≠ [])
    (hp : Placed F k) : b.IsInfixAt NativeRustcArm.Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- A contract with a fact of the entry state carried to the exit. -/
theorem Spec.carry {entry : Int64} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (h : Spec entry P Q) (C : MachineData → Prop) :
    Spec entry (fun m ↦ P m ∧ C m) (fun m m' ↦ Q m m' ∧ C m) := fun m ⟨hP, hC⟩ ↦
  Eventually.mono (h m hP) fun _ ⟨hpc, hQ⟩ ↦ ⟨hpc, hQ, hC⟩

end

end NativeRustcVmArm.Wire
