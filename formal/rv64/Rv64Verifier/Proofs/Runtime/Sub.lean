import Rv64Verifier.Proofs.Runtime.Step

/-!
# The bytes of sub-doubleword accesses and of shifted doublewords

What the symbolic executor's sub-doubleword operations at any address compute (`Sym.BinOp.ldx`,
`Sym.E.stx`), byte by byte: a load's bytes are the doubleword's from its byte position on
(`extractByte_fromWord`), a store replaces the bytes from its position (`extractByte_merge`). And
the doubleword `memcpy` and `memmove` build from two aligned ones, `(x >>> 8a) ||| (y <<< (64 - 8a))`
(`extractByte_shift`).
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64

theorem getLsbD_extractByte (w : Word) (p j : Nat) :
    (extractByte w p).getLsbD j = (decide (j < 8) && w.getLsbD (p * 8 + j)) := by
  simp [extractByte, BitVec.truncate_eq_setWidth]

theorem extractByte_eq {x y : Word} {p q : Nat}
    (h : ∀ j < 8, x.getLsbD (p * 8 + j) = y.getLsbD (q * 8 + j)) :
    extractByte x p = extractByte y q := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_extractByte, getLsbD_extractByte, h j hj]

theorem getLsbD_ones (m i : Nat) (hm : m ≤ 64) :
    (BitVec.ofNat 64 (2 ^ m - 1)).getLsbD i = decide (i < m) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : i < m
  · simp [h, show i < 64 by omega]
  · simp [h]

/-- The byte at `q` of `old` with the `m` bits of `v` put in at bit `sh`. -/
theorem extractByte_insert (old : Word) {m : Nat} (v : BitVec m) {sh q : Nat} (hm : m ≤ 64)
    (hsh : sh % 8 = 0) (hm8 : m % 8 = 0) (hq : q < 8) :
    extractByte ((old &&& ~~~(BitVec.ofNat 64 (2 ^ m - 1) <<< sh)) ||| (v.zeroExtend 64 <<< sh)) q =
      if sh ≤ q * 8 ∧ q * 8 < sh + m then extractByte (v.zeroExtend 64) (q - sh / 8)
      else extractByte old q := by
  split
  · rename_i hin
    apply extractByte_eq
    intro j hj
    have e : q * 8 + j - sh = (q - sh / 8) * 8 + j := by omega
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      getLsbD_ones m _ hm, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
    have h1 : q * 8 + j < 64 := by omega
    have h2 : ¬ q * 8 + j < sh := by omega
    have h3 : (q - sh / 8) * 8 + j < m := by omega
    simp [h1, h2, e, h3, show (q - sh / 8) * 8 + j < 64 by omega]
  · rename_i hin
    apply extractByte_eq
    intro j hj
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      getLsbD_ones m _ hm, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
    have h1 : q * 8 + j < 64 := by omega
    by_cases h2 : q * 8 + j < sh
    · simp [h1, h2]
    · have h3 : ¬ q * 8 + j - sh < m := by omega
      simp [h1, h2, h3, BitVec.getLsbD_of_ge v _ (Nat.le_of_not_lt h3)]

theorem extractByte_zeroExtend {m : Nat} (v : Word) {i : Nat} (hi : i * 8 + 8 ≤ m) (hm : m ≤ 64) :
    extractByte ((v.truncate m).zeroExtend 64) i = extractByte v i := by
  apply extractByte_eq
  intro j hj
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
  have : i * 8 + j < m := by omega
  simp [this, show i * 8 + j < 64 by omega]

/-- A sub-doubleword store at byte position `bo` replaces the bytes from `bo` on. -/
theorem extractByte_merge (k : Sym.StoreKind) (old v : Word) {bo q : Nat}
    (hbo : bo % k.width = 0) (hb : bo < 8) (hq : q < 8) :
    extractByte (k.merge old bo v) q =
      if bo ≤ q ∧ q < bo + k.width then extractByte v (q - bo) else extractByte old q := by
  cases k with
  | d =>
    simp only [Sym.StoreKind.width] at hbo
    have : bo = 0 := by omega
    subst this
    simp [Sym.StoreKind.merge, Sym.StoreKind.width, hq]
  | w =>
    have hw : Sym.StoreKind.w.width = 4 := rfl
    rw [hw] at hbo
    rw [Sym.StoreKind.merge, replaceWord32,
      show (0xFFFFFFFF#64) = BitVec.ofNat 64 (2 ^ 32 - 1) from rfl,
      extractByte_insert _ _ (by decide) (by omega) (by decide) hq]
    split <;> split
    · rw [extractByte_zeroExtend _ (by omega) (by decide)]
      congr 1; omega
    · exfalso; omega
    · exfalso; omega
    · rfl
  | h =>
    have hw : Sym.StoreKind.h.width = 2 := rfl
    rw [hw] at hbo
    rw [Sym.StoreKind.merge, replaceHalfword,
      show (0xFFFF#64) = BitVec.ofNat 64 (2 ^ 16 - 1) from rfl,
      extractByte_insert _ _ (by decide) (by omega) (by decide) hq]
    split <;> split
    · rw [extractByte_zeroExtend _ (by omega) (by decide)]
      congr 1; omega
    · exfalso; omega
    · exfalso; omega
    · rfl
  | b =>
    have hw : Sym.StoreKind.b.width = 1 := rfl
    rw [hw] at hbo
    rw [Sym.StoreKind.merge, replaceByte,
      show (0xFF#64) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      extractByte_insert _ _ (by decide) (by omega) (by decide) hq]
    split <;> split
    · rw [extractByte_zeroExtend _ (by omega) (by decide)]
      congr 1; omega
    · exfalso; omega
    · exfalso; omega
    · rfl

/-- A sub-doubleword load at byte position `bo` reads the bytes from `bo` on. -/
theorem extractByte_fromWord (k : Sym.LoadKind) (x : Word) {bo j : Nat} (hbo : bo % k.width = 0)
    (hb : bo < 8) (hj : j < k.width) : extractByte (k.fromWord x bo) j = extractByte x (bo + j) := by
  apply extractByte_eq
  intro i hi
  cases k <;> simp only [Sym.LoadKind.width] at hbo hj
  · simp only [Sym.LoadKind.fromWord]
    have : bo = 0 := by omega
    subst this
    simp
  all_goals
    simp only [Sym.LoadKind.fromWord, extractWord32, extractHalfword, extractByte,
      BitVec.getLsbD_signExtend, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    first
      | (have e1 : j * 8 + i < 32 := by omega
         have e2 : bo / 4 * 32 + (j * 8 + i) = (bo + j) * 8 + i := by omega
         simp [e1, e2, show j * 8 + i < 64 by omega])
      | (have e1 : j * 8 + i < 16 := by omega
         have e2 : bo / 2 * 16 + (j * 8 + i) = (bo + j) * 8 + i := by omega
         simp [e1, e2, show j * 8 + i < 64 by omega])
      | (have e1 : j * 8 + i < 8 := by omega
         have e2 : bo * 8 + (j * 8 + i) = (bo + j) * 8 + i := by omega
         simp [e1, e2, show j * 8 + i < 64 by omega])

/-- The doubleword of `x`'s bytes from `a` on, then `y`'s. -/
theorem extractByte_shift (x y : Word) {a i : Nat} (ha1 : 0 < a) (ha : a < 8) (hi : i < 8) :
    extractByte ((x >>> (8 * a)) ||| (y <<< (64 - 8 * a))) i =
      if i + a < 8 then extractByte x (i + a) else extractByte y (i + a - 8) := by
  split
  · apply extractByte_eq
    intro j hj
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    have h1 : i * 8 + j < 64 - 8 * a := by omega
    simp [h1, show 8 * a + (i * 8 + j) = (i + a) * 8 + j by omega]
  · apply extractByte_eq
    intro j hj
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    have h0 : 64 ≤ 8 * a + (i * 8 + j) := by omega
    simp [BitVec.getLsbD_of_ge x _ h0, show ¬ i * 8 + j < 64 - 8 * a by omega,
      show i * 8 + j - (64 - 8 * a) = (i + a - 8) * 8 + j by omega, show i * 8 + j < 64 by omega]

/-- `x ||| y` is `x + y` for an 8-aligned `x` and `y < 8`. -/
theorem or_eq_add {x y : Word} (hx : x.toNat % 8 = 0) (hy : y.toNat < 8) : x ||| y = x + y := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, Bool.and_eq_false_iff]
  by_cases h3 : i < 3
  · left
    rw [← BitVec.testBit_toNat, show x.toNat = 8 * (x.toNat / 8) by omega,
      show (8 : Nat) = 2 ^ 3 from rfl, Nat.mul_comm, Nat.testBit_mul_two_pow]
    simp [h3]
  · right
    rw [← BitVec.testBit_toNat]
    apply Nat.testBit_lt_two_pow
    calc y.toNat < 2 ^ 3 := hy
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)

theorem mask_eq : (0xfffffffffffffff8 : Word) = ~~~7#64 := by decide

/-- `p + j` lies in `p`'s doubleword while `p`'s byte position plus `j` stays below 8. -/
theorem alignDown_add {p : Word} {j : Nat} (h : p.toNat % 8 + j < 8) :
    (p + BitVec.ofNat 64 j) &&& ~~~7#64 = p &&& ~~~7#64 ∧
      (p + BitVec.ofNat 64 j).toNat = p.toNat + j := by
  have hl := p.isLt
  have hp : (p + BitVec.ofNat 64 j).toNat = p.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨BitVec.eq_of_toNat_eq ?_, hp⟩
  rw [toNat_alignDown, toNat_alignDown, hp]
  omega

/-- What a sub-doubleword load at `p` puts in its register, byte by byte: the bytes from `p`. -/
theorem extractByte_load (k : Sym.LoadKind) (u : MachineState) {p : Word}
    (hp : p.toNat % k.width = 0) {j : Nat} (hj : j < k.width) :
    extractByte (k.fromWord (u.getMem (p &&& 0xfffffffffffffff8)) (p &&& 7).toNat) j =
      byteAt u (p + BitVec.ofNat 64 j) := by
  rw [show (7 : Word) = 7#64 from rfl, toNat_and7, mask_eq]
  have hw : (k.width = 1 ∨ k.width = 2 ∨ k.width = 4 ∨ k.width = 8) := by
    cases k <;> simp [Sym.LoadKind.width]
  have h8 : p.toNat % 8 + j < 8 := by rcases hw with hw | hw | hw | hw <;> rw [hw] at hp hj <;> omega
  rw [extractByte_fromWord k _ (by rcases hw with hw | hw | hw | hw <;> rw [hw] at hp ⊢ <;> omega)
    (Nat.mod_lt _ (by decide)) hj, byteAt_eq, (alignDown_add h8).1, (alignDown_add h8).2]
  congr 1
  omega

/-- The doubleword a sub-doubleword store of `v` at `q` leaves, byte by byte. -/
theorem extractByte_store (k : Sym.StoreKind) (old v : Word) {q : Word} (hq : q.toNat % k.width = 0)
    {i : Nat} (hi : i < 8) :
    extractByte (k.merge old (q &&& 7).toNat v) i =
      if q.toNat % 8 ≤ i ∧ i < q.toNat % 8 + k.width then extractByte v (i - q.toNat % 8)
      else extractByte old i := by
  rw [show (7 : Word) = 7#64 from rfl, toNat_and7]
  have hw : (k.width = 1 ∨ k.width = 2 ∨ k.width = 4 ∨ k.width = 8) := by
    cases k <;> simp [Sym.StoreKind.width]
  exact extractByte_merge k old v (by rcases hw with hw | hw | hw | hw <;> rw [hw] at hq ⊢ <;> omega)
    (Nat.mod_lt _ (by decide)) hi

/-- A load of `w` bytes at `p` stored at `q`: the bytes of `q`'s doubleword after. -/
theorem extractByte_copy (lk : Sym.LoadKind) (sk : Sym.StoreKind) (u : MachineState) (old : Word)
    {p q : Word} (hw : lk.width = sk.width) (hp : p.toNat % sk.width = 0)
    (hq : q.toNat % sk.width = 0) {i : Nat} (hi : i < 8) :
    extractByte (sk.merge old (q &&& 7).toNat
        (lk.fromWord (u.getMem (p &&& 0xfffffffffffffff8)) (p &&& 7).toNat)) i =
      if q.toNat % 8 ≤ i ∧ i < q.toNat % 8 + sk.width then
        byteAt u (p + BitVec.ofNat 64 (i - q.toNat % 8))
      else extractByte old i := by
  rw [extractByte_store sk old _ hq hi]
  split
  · exact extractByte_load lk u (hw ▸ hp) (by omega)
  · rfl

end Rv64Verifier.Runtime
