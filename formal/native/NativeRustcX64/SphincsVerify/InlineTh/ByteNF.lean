module

public import NativeRustcX64.Sym
public import NativeRustcX64.Hasher.Bytes

/-!
# The bytes of symbolic values, as XORs of memory bytes (x86-64)

A byte `XB` as the executor's values often give it: a constant XOR some bytes of the
environment's memory (`env.mem0`), each a region and an offset. `symByte f v t` reads byte `t` of
the symbolic value `v` in that form, where it can: a literal, a load's byte, a byte of an `XOR` of
two such (64, 32 or 8 bits), a byte of the executor's assembly of bytes (`assemble`: a byte plus
the rest shifted left by 8), a byte of `bytes s n`. It is sound: the byte of `v`'s value is the
form's (`byteOf_eval_of_symByte`). On the literal post-states of blocks, kernel evaluation of
`symByte` checks what each written byte is.
-/

namespace NativeRustcX64.SphincsVerifyProof.InlineTh

open NativeRustcX64.Sym

@[expose] public section

/-- A byte: the constant `cst` XOR the bytes of `env.mem0` at the offsets `bytes` of regions. -/
structure XB where
  cst : UInt8
  bytes : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- The XOR of two such bytes. -/
def XB.xor (a b : XB) : XB := ⟨a.cst ^^^ b.cst, a.bytes ++ b.bytes⟩

/-- `env.mem0`'s byte at offset `i` of region `r`. -/
def memAt (env : Env) (r i : Nat) : UInt8 := (env.mem0.get? (env.base r + BitVec.ofNat 64 i)).getD 0

/-- The XOR of `env.mem0`'s bytes at the offsets. -/
def xorAll (env : Env) : List (Nat × Nat) → UInt8
  | [] => 0
  | ri :: l => memAt env ri.1 ri.2 ^^^ xorAll env l

/-- The byte's value. -/
def XB.eval (env : Env) (x : XB) : UInt8 := x.cst ^^^ xorAll env x.bytes

/-- A value below 256 by its form. -/
def isByte : Sym → Bool
  | .load _ _ n => n == 1
  | .un (.bytes _ n) _ _ => n == 1
  | .lit n => decide (n < 256)
  | _ => false

/-- **Byte `t` of `v`** as an `XB`, where its form gives it (at most `f` nested operations). -/
def symByte : Nat → Sym → Nat → Option XB
  | 0, _, _ => none
  | f + 1, v, t =>
    match v with
    | .lit n => some ⟨byteOf (BitVec.ofNat 64 n) t, []⟩
    | .load r off n => if t < n ∧ n ≤ 8 then some ⟨0, [(r, off + t)]⟩ else none
    | .bin .xor w a b =>
      if t < w.bytes then
        match symByte f a t, symByte f b t with
        | some x, some y => some (x.xor y)
        | _, _ => none
      else none
    | .bin .add .W64 a (.bin .shl .W64 b (.lit 8)) =>
      if isByte a then
        if t = 0 then symByte f a 0 else if t < 8 then symByte f b (t - 1) else none
      else none
    | .un (.bytes s n) _ a => if t < n ∧ s + t < 8 then symByte f a (s + t) else none
    | _ => none

end

public section

theorem xorAll_append (env : Env) : ∀ l l' : List (Nat × Nat),
    xorAll env (l ++ l') = xorAll env l ^^^ xorAll env l'
  | [], l' => by simp [xorAll]
  | ri :: l, l' => by
    rw [List.cons_append, xorAll, xorAll, xorAll_append env l l', UInt8.xor_assoc]

theorem XB.eval_xor (env : Env) (a b : XB) : (a.xor b).eval env = a.eval env ^^^ b.eval env := by
  simp only [XB.eval, XB.xor, xorAll_append]
  rw [UInt8.xor_assoc, UInt8.xor_assoc, ← UInt8.xor_assoc b.cst, UInt8.xor_comm b.cst,
    UInt8.xor_assoc]

/-- A byte below the width of a value truncated to it. -/
theorem byteOf_ext_low (w : Width) (x : BitVec 64) {t : Nat} (ht : t < w.bytes) :
    byteOf (ext w (low w x)) t = byteOf x t := by
  have hb := bits_eq w
  have hle := bytes_le w
  apply UInt8.toNat_inj.mp
  rw [byteOf, byteOf, UInt8.toNat_ofNat', UInt8.toNat_ofNat', toNat_ext, toNat_low]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp [hj, show j + 8 * t < w.bits by omega]
  · simp [hj]

theorem low_xor (w : Width) (x y : BitVec 64) : low w x ^^^ low w y = low w (x ^^^ y) := by
  simp only [low, BitVec.setWidth_xor]

theorem lt256_of_isByte [Labels] {env : Env} {a : Sym} (h : isByte a = true) :
    (a.eval env).toNat < 256 := by
  match a, h with
  | .load r off n, h =>
    simp only [isByte, beq_iff_eq] at h
    subst h
    show (env.load r off 1).toNat < 256
    unfold Env.load
    rw [ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    have := natOfBytes_lt ((List.range 1).map fun i =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i))).getD 0)
    simp only [List.length_map, List.length_range] at this
    omega
  | .un (.bytes s n) w v, h =>
    simp only [isByte, beq_iff_eq] at h
    subst h
    show (UnOp.apply (.bytes s 1) w (v.eval env)).toNat < 256
    simp only [UnOp.apply, Sym.bytesOf, BitVec.toNat_ofNat]
    omega
  | .lit n, h =>
    simp only [isByte, decide_eq_true_eq] at h
    show (BitVec.ofNat 64 n).toNat < 256
    rw [BitVec.toNat_ofNat]
    omega

theorem byteOf_add_shift (a b : BitVec 64) (ha : a.toNat < 256) {t : Nat} (ht : t < 8) :
    byteOf (a + b <<< 8) t = if t = 0 then byteOf a 0 else byteOf b (t - 1) := by
  apply UInt8.toNat_inj.mp
  have hb := b.isLt
  split
  · subst t
    rw [byteOf, byteOf, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  · rw [byteOf, byteOf, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hu : u < 7 := by omega
    interval_cases u <;> simp <;> omega

theorem byteOf_bytesOf (x : BitVec 64) {s n t : Nat} (ht : t < n) (hst : s + t < 8) :
    byteOf (Sym.bytesOf x s n) t = byteOf x (s + t) := by
  apply UInt8.toNat_inj.mp
  rw [byteOf, byteOf, UInt8.toNat_ofNat', UInt8.toNat_ofNat', Sym.bytesOf]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and, show j + 8 * t < 64 by omega,
      show j + 8 * t < 8 * n by omega]
    congr 1
    omega
  · simp [hj]

/-- **`symByte` is sound**: byte `t` of `v`'s value is the form's. -/
theorem byteOf_eval_of_symByte [Labels] {env : Env} :
    ∀ (f : Nat) (v : Sym) (t : Nat) (x : XB), symByte f v t = some x →
      byteOf (v.eval env) t = x.eval env
  | 0, _, _, _, h => by simp [symByte] at h
  | f + 1, v, t, x, h => by
    match v, h with
    | .lit n, hv =>
      simp only [symByte, Option.some.injEq] at hv
      subst hv
      simp [XB.eval, xorAll, Sym.eval]
    | .load r off n, hv =>
      simp only [symByte] at hv
      split at hv
      · rename_i hc
        simp only [Option.some.injEq] at hv
        subst hv
        show byteOf (env.load r off n) t = 0 ^^^ (memAt env r (off + t) ^^^ 0)
        rw [byteOf_load hc.1 hc.2, UInt8.zero_xor, UInt8.xor_zero]
        rfl
      · cases hv
    | .bin .xor w a b, hv =>
      simp only [symByte] at hv
      split at hv
      · rename_i ht
        split at hv
        · rename_i xa xb ha hb
          simp only [Option.some.injEq] at hv
          subst hv
          show byteOf (BinOp.apply .xor w (a.eval env) (b.eval env)) t = _
          simp only [BinOp.apply]
          rw [low_xor, byteOf_ext_low w _ ht, Hasher.byteOf_xor, byteOf_eval_of_symByte f a t xa ha,
            byteOf_eval_of_symByte f b t xb hb, XB.eval_xor]
        · cases hv
      · cases hv
    | .bin .add .W64 a (.bin .shl .W64 b (.lit 8)), hv =>
      simp only [symByte] at hv
      split at hv
      · rename_i hab
        show byteOf (BinOp.apply .add .W64 (a.eval env)
          (BinOp.apply .shl .W64 (b.eval env) (BitVec.ofNat 64 8))) t = _
        simp only [BinOp.apply, low_W64, ext_W64, shiftCount_8]
        split at hv
        · subst t
          rw [byteOf_add_shift _ _ (lt256_of_isByte hab) (by omega), Hasher.ite_pos' rfl]
          exact byteOf_eval_of_symByte f a 0 x hv
        · split at hv
          · rename_i h0 ht
            rw [byteOf_add_shift _ _ (lt256_of_isByte hab) ht, Hasher.ite_neg' h0]
            exact byteOf_eval_of_symByte f b (t - 1) x hv
          · cases hv
      · cases hv
    | .un (.bytes s n) w a, hv =>
      simp only [symByte] at hv
      split at hv
      · rename_i hc
        show byteOf (UnOp.apply (.bytes s n) w (a.eval env)) t = _
        simp only [UnOp.apply]
        rw [byteOf_bytesOf _ hc.1 hc.2]
        exact byteOf_eval_of_symByte f a (s + t) x hv
      · cases hv

end

end NativeRustcX64.SphincsVerifyProof.InlineTh
