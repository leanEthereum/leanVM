import Rv64Verifier.Proofs.Common

/-!
# Bytes, the heap and `Vec`s

What the runtime's contracts (`Runtime/Contracts.lean`) are stated in.

* Bytes: memory is doublewords (`getMem`); the byte at `a` is byte `a % 8` of the doubleword at
  `a &&& ~~~7` (`byteAt`, riscv-zkvm's `getByte`, what `LB` reads and `SB` writes). `bytesAt` lists
  `n` of them. A doubleword is its eight bytes (`getMem_eq_of_bytes`), so `readWords` and
  `eListAt` follow from bytes (`readWords_eq_of_bytesAt`, `eListAt_eq_of_bytesAt`).
* Frames at byte granularity (`ByteFrame s t w`): `t`'s bytes outside `w` are `s`'s, and so are its
  doublewords at addresses that are not 8-aligned, which no store writes. A doubleword whose eight
  bytes miss `w` is unchanged (`ByteFrame.getMem`).
* The heap: the guest's bump allocator keeps the next free byte in `NEXT` (`nextAddr`), between
  `heapStart` and `heapEnd` (`HeapOk`). An allocation takes bytes from `NEXT` on (`Fresh`); what was
  allocated before lies below `NEXT` (`Buf`).
* `Vec<T>`: capacity, pointer and length at `+0`, `+8`, `+16` (`vecCap`, `vecPtr`, `vecLen`; a
  `RawVec` is the first two), its buffer allocated (`RawVecOk`, `VecOk`), its elements as bytes
  (`vecBytes`), doublewords (`vecWords`) or `E`s (`vecEs`).
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64 LeanVM.Parameters

/-- A callee-saved register is in every list that has them all. -/
theorem mem_of_calleeSaved {r : Reg} (h : r ∈ calleeSaved) (l : List Reg)
    (hl : ∀ r ∈ calleeSaved, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- A register of one list is in another that has them all. -/
theorem mem_of_mem {l₁ : List Reg} {r : Reg} (h : r ∈ l₁) (l₂ : List Reg)
    (hl : ∀ x ∈ l₁, x ∈ l₂ := by decide) : r ∈ l₂ :=
  hl r h

/-- The two ways a branch's target can go. -/
theorem eq_ite_cases {α : Type} {c : Prop} [Decidable c] {x a b : α}
    (h : x = if c then a else b) : (c ∧ x = a) ∨ (¬ c ∧ x = b) := by
  by_cases hc : c
  · exact Or.inl ⟨hc, by simp only [h, hc, ↓reduceIte]⟩
  · exact Or.inr ⟨hc, by simp only [h, hc, ↓reduceIte]⟩

/-! ## Bytes -/

/-- The byte at `a`. -/
def byteAt (s : MachineState) (a : Word) : BitVec 8 := s.getByte a

/-- The `n` bytes from `a`. -/
def bytesAt (s : MachineState) (a : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i ↦ byteAt s (a + BitVec.ofNat 64 i)

theorem bytesAt_length (s : MachineState) (a : Word) (n : Nat) : (bytesAt s a n).length = n := by
  simp [bytesAt]

theorem bytesAt_getElem (s : MachineState) (a : Word) (n i : Nat) (h : i < (bytesAt s a n).length) :
    (bytesAt s a n)[i] = byteAt s (a + BitVec.ofNat 64 i) := by
  simp [bytesAt]

theorem bytesAt_eq_iff {s t : MachineState} {a b : Word} {n : Nat} :
    bytesAt t a n = bytesAt s b n ↔
      ∀ i < n, byteAt t (a + BitVec.ofNat 64 i) = byteAt s (b + BitVec.ofNat 64 i) := by
  constructor
  · intro h i hi
    have := congrArg (fun l ↦ l[i]?) h
    simpa [bytesAt, hi] using this
  · intro h
    apply List.ext_getElem (by simp [bytesAt_length])
    intro i h1 h2
    rw [bytesAt_getElem, bytesAt_getElem]
    exact h i (by rw [bytesAt_length] at h1; exact h1)

theorem toNat_and7 (x : Word) : (x &&& 7#64).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 3

theorem and_not_add (x m : Word) : x = (x &&& ~~~m) + (x &&& m) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases x[i] <;> cases m[i] <;> rfl
  · ext i
    simp only [BitVec.getElem_zero, BitVec.getElem_and, BitVec.getElem_not]
    cases x[i] <;> cases m[i] <;> rfl

/-- `a &&& ~~~7` is `a` rounded down to a multiple of 8. -/
theorem toNat_alignDown (x : Word) : (x &&& ~~~7#64).toNat = x.toNat - x.toNat % 8 := by
  have h := congrArg BitVec.toNat (and_not_add x 7#64)
  rw [BitVec.toNat_add, toNat_and7] at h
  have := (x &&& ~~~7#64).isLt
  omega

theorem byteAt_eq (s : MachineState) (a : Word) :
    byteAt s a = extractByte (s.getMem (a &&& ~~~7#64)) (a.toNat % 8) := by
  simp only [byteAt, MachineState.getByte, alignToDword, byteOffset, toNat_and7]

/-- The doubleword `a &&& ~~~7` of a byte `a` of the aligned doubleword at `b` is `b`. -/
theorem alignDown_of_within {a b : Word} (hb : b.toNat % 8 = 0) (h1 : b.toNat ≤ a.toNat)
    (h2 : a.toNat < b.toNat + 8) : a &&& ~~~7#64 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_alignDown]
  omega

/-- Byte `i` of the aligned doubleword at `b`. -/
theorem byteAt_of_within {s : MachineState} {a b : Word} (hb : b.toNat % 8 = 0)
    (h1 : b.toNat ≤ a.toNat) (h2 : a.toNat < b.toNat + 8) :
    byteAt s a = extractByte (s.getMem b) (a.toNat - b.toNat) := by
  rw [byteAt_eq, alignDown_of_within hb h1 h2]
  congr 1
  omega

theorem toNat_add_lt8 {b : Word} (hb : b.toNat % 8 = 0) {i : Nat} (hi : i < 8) :
    (b + BitVec.ofNat 64 i).toNat = b.toNat + i := by
  have := b.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem byteAt_add {s : MachineState} {b : Word} (hb : b.toNat % 8 = 0) {i : Nat} (hi : i < 8) :
    byteAt s (b + BitVec.ofNat 64 i) = extractByte (s.getMem b) i := by
  rw [byteAt_of_within hb (by rw [toNat_add_lt8 hb hi]; omega) (by rw [toNat_add_lt8 hb hi]; omega),
    toNat_add_lt8 hb hi, Nat.add_sub_cancel_left]

/-- A doubleword is its eight bytes. -/
theorem eq_of_extractByte {x y : Word} (h : ∀ i < 8, extractByte x i = extractByte y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb := congrArg (fun b : BitVec 8 ↦ b.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight] at hb
  have h1 : j % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [h1, decide_true, Bool.true_and] at hb
  rwa [show j / 8 * 8 + j % 8 = j by omega] at hb

/-- Two aligned doublewords with the same bytes are equal. -/
theorem getMem_eq_of_bytes {s t : MachineState} {a b : Word} (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0)
    (h : ∀ i < 8, byteAt t (a + BitVec.ofNat 64 i) = byteAt s (b + BitVec.ofNat 64 i)) :
    t.getMem a = s.getMem b :=
  eq_of_extractByte fun i hi ↦ by rw [← byteAt_add ha hi, ← byteAt_add hb hi]; exact h i hi

theorem getLsbD_255 (i : Nat) : (255#64).getLsbD i = decide (i < 8) := by
  rw [BitVec.getLsbD_ofNat, show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 8 <;> simp [h]; omega

theorem extractByte_replaceByte (w : Word) {p q : Nat} (b : BitVec 8) (hp : p < 8) (hq : q < 8) :
    extractByte (replaceByte w p b) q = if p = q then b else extractByte w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h64 : q * 8 + k < 64 := by omega
  simp only [extractByte, replaceByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hk, h64, decide_true, Bool.true_and, getLsbD_255]
  split
  · subst p
    simp [hk, show k < 64 by omega]
  · by_cases h1 : q * 8 + k < p * 8
    · simp [h1, hk]
    · have h2 : ¬ (q * 8 + k - p * 8 < 8) := by omega
      simp [h1, h2, hk, BitVec.getLsbD_of_ge b _ (Nat.le_of_not_lt h2)]

/-- The doubleword at offset `k` of two byte ranges with equal bytes, both aligned. -/
theorem getMem_eq_of_bytesAt {s t : MachineState} {a b : Word} {N : Nat}
    (h : bytesAt t a N = bytesAt s b N) (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0) {k : Nat}
    (hk : k % 8 = 0) (hkN : k + 8 ≤ N) :
    t.getMem (a + BitVec.ofNat 64 k) = s.getMem (b + BitVec.ofNat 64 k) := by
  have hal : ∀ x : Word, x.toNat % 8 = 0 → (x + BitVec.ofNat 64 k).toNat % 8 = 0 := by
    intro x hx
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine getMem_eq_of_bytes (hal a ha) (hal b hb) fun i hi ↦ ?_
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact bytesAt_eq_iff.mp h (k + i) (by omega)

theorem readWords_eq_map (s : MachineState) :
    ∀ (n : Nat) (a : Word),
      s.readWords a n = (List.range n).map fun i ↦ s.getMem (a + BitVec.ofNat 64 (8 * i)) := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    rw [MachineState.readWords, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, BitVec.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    congr 1
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : Word).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Aligned byte ranges with equal bytes hold equal doubleword lists. -/
theorem readWords_eq_of_bytesAt {s t : MachineState} {a b : Word} {n : Nat}
    (h : bytesAt t a (8 * n) = bytesAt s b (8 * n)) (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0) : t.readWords a n = s.readWords b n := by
  rw [readWords_eq_map, readWords_eq_map]
  apply List.map_congr_left
  intro i hi
  exact getMem_eq_of_bytesAt h ha hb (by omega) (by simp at hi; omega)

/-- Aligned byte ranges with equal bytes hold equal lists of `E`. -/
theorem eListAt_eq_of_bytesAt {s t : MachineState} {a b : Word} {n : Nat}
    (h : bytesAt t a (24 * n) = bytesAt s b (24 * n)) (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0) : eListAt t a n = eListAt s b n := by
  unfold eListAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have e (c : Word) (j : Nat) (hj : j < 3) (hc : c.toNat = 8 * j) :
      t.getMem (a + BitVec.ofNat 64 (24 * i) + c) = s.getMem (b + BitVec.ofNat 64 (24 * i) + c) := by
    rw [show c = BitVec.ofNat 64 (8 * j) from BitVec.eq_of_toNat_eq (by simp [hc]; omega),
      BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact getMem_eq_of_bytesAt h ha hb (by omega) (by omega)
  have e0 : t.getMem (a + BitVec.ofNat 64 (24 * i)) = s.getMem (b + BitVec.ofNat 64 (24 * i)) :=
    getMem_eq_of_bytesAt h ha hb (by omega) (by omega)
  unfold eAt
  rw [e0, e 8 1 (by decide) rfl, e 16 2 (by decide) rfl]

/-! ## Byte frames -/

/-- `t`'s memory is `s`'s but for the bytes `w` covers: every other byte agrees, and so does every
doubleword at an address that is not 8-aligned (no store writes one). -/
structure ByteFrame (s t : MachineState) (w : Word → Prop) : Prop where
  byte : ∀ a, ¬ w a → byteAt t a = byteAt s a
  unaligned : ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = s.getMem a

theorem ByteFrame.refl (s : MachineState) (w : Word → Prop) : ByteFrame s s w :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem ByteFrame.mono {s t : MachineState} {w w' : Word → Prop} (h : ByteFrame s t w)
    (hw : ∀ a, w a → w' a) : ByteFrame s t w' :=
  ⟨fun a ha ↦ h.byte a fun h' ↦ ha (hw a h'), h.unaligned⟩

theorem ByteFrame.trans {s t u : MachineState} {w w' : Word → Prop} (h₁ : ByteFrame s t w)
    (h₂ : ByteFrame t u w') (hw : ∀ a, w' a → w a) : ByteFrame s u w :=
  ⟨fun a ha ↦ (h₂.byte a fun h' ↦ ha (hw a h')).trans (h₁.byte a ha),
    fun a ha ↦ (h₂.unaligned a ha).trans (h₁.unaligned a ha)⟩

/-- A doubleword whose eight bytes miss the frame's range is unchanged. -/
theorem ByteFrame.getMem {s t : MachineState} {w : Word → Prop} (h : ByteFrame s t w) {a : Word}
    (ha : ∀ i < 8, ¬ w (a + BitVec.ofNat 64 i)) : t.getMem a = s.getMem a := by
  by_cases h8 : a.toNat % 8 = 0
  · exact getMem_eq_of_bytes h8 h8 fun i hi ↦ h.byte _ (ha i hi)
  · exact h.unaligned a h8

/-- Bytes outside a frame's range are unchanged. -/
theorem ByteFrame.bytesAt {s t : MachineState} {w : Word → Prop} (h : ByteFrame s t w) {p : Word}
    {n : Nat} (hp : ∀ i < n, ¬ w (p + BitVec.ofNat 64 i)) : bytesAt t p n = bytesAt s p n :=
  bytesAt_eq_iff.mpr fun i hi ↦ h.byte _ (hp i hi)

/-- Bytes below a doubleword frame's range are unchanged. -/
theorem bytesAt_of_below {s t : MachineState} {lo : Word} {N : Nat}
    (h : ∀ a, ¬ Within a lo N → t.getMem a = s.getMem a) {p : Word} {n : Nat}
    (hp : p.toNat + n ≤ lo.toNat) : bytesAt t p n = bytesAt s p n := by
  refine bytesAt_eq_iff.mpr fun i hi ↦ ?_
  rw [byteAt_eq, byteAt_eq, h]
  have h1 := toNat_alignDown (p + BitVec.ofNat 64 i)
  have h2 : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := lo.isLt
    omega
  simp only [Within]
  omega

/-- A frame of aligned doublewords is a frame of their bytes, given that unaligned addresses keep
their doublewords. -/
theorem ByteFrame.of_memFrame {s t : MachineState} {lo : Word} {n : Nat} (h : MemFrame s t lo n)
    (hlo : lo.toNat % 8 = 0) (hn : n % 8 = 0)
    (hu : ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = s.getMem a) : ByteFrame s t (Within · lo n) := by
  refine ⟨fun a ha ↦ ?_, hu⟩
  rw [byteAt_eq, byteAt_eq, h]
  simp only [Within, toNat_alignDown] at ha ⊢
  omega

/-- A frame of doublewords is a frame of bytes, for a range that holds every byte of each aligned
doubleword it touches. -/
theorem ByteFrame.of_dwords {s t : MachineState} {w : Word → Prop}
    (h : ∀ a, a.toNat % 8 = 0 → ¬ w a → t.getMem a = s.getMem a)
    (hu : ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = s.getMem a)
    (hw : ∀ a, w (a &&& ~~~7#64) → w a) : ByteFrame s t w := by
  refine ⟨fun a ha ↦ ?_, hu⟩
  rw [byteAt_eq, byteAt_eq, h _ (by rw [toNat_alignDown]; omega) fun h' ↦ ha (hw a h')]

/-- A step that writes one aligned doubleword. -/
theorem ByteFrame.of_single {s t : MachineState} {k : Word} (hk : k.toNat % 8 = 0)
    (h : ∀ a, a ≠ k → t.getMem a = s.getMem a) : ByteFrame s t (Within · k 8) := by
  refine ByteFrame.of_dwords (fun a _ ha ↦ h a fun h' ↦ ha ?_) (fun a ha ↦ h a fun h' ↦ ha ?_)
    fun a ha ↦ ?_
  · rw [h']; simp only [Within]; omega
  · rw [h']; exact hk
  · simp only [Within, toNat_alignDown] at ha ⊢; omega

/-- An aligned range of whole doublewords holds every byte of each doubleword it touches. -/
theorem within_of_alignDown {a lo : Word} {n : Nat} (hlo : lo.toNat % 8 = 0) (hn : n % 8 = 0)
    (h : Within (a &&& ~~~7#64) lo n) : Within a lo n := by
  simp only [Within, toNat_alignDown] at h ⊢
  omega

/-- A block whose writes are all aligned leaves the doublewords at unaligned addresses alone. -/
theorem _root_.Rv64Verifier.Sym.Expect.Holds.unaligned {x : Sym.Expect} {s t : MachineState}
    (h : x.Holds s t) (hw : ∀ k ∈ x.writes, (k.eval s).toNat % 8 = 0) :
    ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = s.getMem a :=
  fun a ha ↦ h.frame a fun k hk heq ↦ ha (heq ▸ hw k hk)

/-! ## Multiplication overflow -/

theorem toNat_mulhu (a b : Word) : (rv64_mulhu a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by norm_num
  simp only [rv64_mulhu, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega))]

/-- `Layout::array`'s check as compiled: `size * n` fits in 64 bits (`mulhu` is zero) and in
`isize::MAX - (align - 1)` (`2^63 - align < size * n` is false). -/
theorem layout_ok {a b al : Word}
    (h : (((if BitVec.ult 0 (rv64_mulhu a b) = true then 1 else 0) |||
      if (9223372036854775808 - al).ult (a * b) = true then 1 else 0) == (0 : Word)) = true)
    (hal : al.toNat ≤ 2 ^ 63) :
    (a * b).toNat = a.toNat * b.toNat ∧ a.toNat * b.toNat ≤ 2 ^ 63 - al.toNat := by
  have h' : BitVec.ult 0 (rv64_mulhu a b) = false ∧
      (9223372036854775808 - al).ult (a * b) = false := by simpa using h
  obtain ⟨c1, c2⟩ := h'
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt, toNat_mulhu] at c1 c2
  have h0 : (0 : Word).toNat = 0 := rfl
  have hc : (9223372036854775808 : Word).toNat = 2 ^ 63 := rfl
  rw [h0, Nat.le_zero, Nat.div_eq_zero_iff_lt (by norm_num)] at c1
  have hmul : (a * b).toNat = a.toNat * b.toNat := by rw [BitVec.toNat_mul]; omega
  rw [BitVec.toNat_sub, hc, hmul] at c2
  refine ⟨hmul, ?_⟩
  omega

/-! ## The data windows -/

/-- The `n` bytes from `a` lie in one of the machine's data windows. -/
@[rv_addr] def Mapped (a : Word) (n : Nat) : Prop :=
  (0x20 ≤ a.toNat ∧ a.toNat + n ≤ 0x78000000) ∨ (0xa0000000 ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000)

/-! ## The heap -/

/-- `NEXT`, the bump allocator's next free byte (`guest/src/main.rs`). -/
@[rv_addr] def nextAddr : Word := 0xa0000f30

@[rv_addr] def heapStart : Nat := 0x20000000
@[rv_addr] def heapEnd : Nat := 0x78000000

/-- The value of `NEXT`. -/
@[rv_addr] def heapNext (s : MachineState) : Nat := (s.getMem nextAddr).toNat

/-- `NEXT` lies in the heap. -/
structure HeapOk (s : MachineState) : Prop where
  lo : heapStart ≤ heapNext s
  hi : heapNext s ≤ heapEnd

/-- Allocated from `s` on to `t`: between their `NEXT`s. -/
@[rv_addr] def Fresh (s t : MachineState) (a : Word) : Prop :=
  heapNext s ≤ a.toNat ∧ a.toNat < heapNext t

/-- The `n` bytes from `a` miss the free heap (from `NEXT` on) and `NEXT` itself: no allocation
writes them. -/
@[rv_addr] def Outside (s : MachineState) (a : Word) (n : Nat) : Prop :=
  (a.toNat + n ≤ heapNext s ∨ heapEnd ≤ a.toNat) ∧ Apart a n nextAddr 8

/-- The `.rodata` section, `[0xa0000000, 0xa0000f30)`: never written. `NEXT` is the `.data` word
right after it. -/
@[rv_addr] def rodataStart : Word := 0xa0000000
@[rv_addr] def rodataSize : Nat := 0xf30

/-- The `n` bytes below `sp` are valid, `sp` is 16-aligned, and the stack lies above the heap and
misses `NEXT` and `.rodata`. -/
structure RtStack (s : MachineState) (n : Nat) : Prop extends StackOk s n where
  above : heapEnd ≤ (stackLo s n).toNat
  next : Apart (stackLo s n) n nextAddr 8
  rodata : Apart (stackLo s n) n rodataStart rodataSize

/-- `n` bytes from `p`, aligned to `align`, allocated: below `NEXT`, in the heap, or none. -/
@[rv_addr] def Buf (s : MachineState) (p : Word) (n align : Nat) : Prop :=
  p.toNat % align = 0 ∧ (n = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + n ≤ heapNext s)

/-- `n` bytes from `p`, aligned to `align`, allocated from `s` on to `t`, or none. -/
@[rv_addr] def NewBuf (s t : MachineState) (p : Word) (n align : Nat) : Prop :=
  p.toNat % align = 0 ∧ (n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + n ≤ heapNext t)

/-- What an allocation writes, `NEXT` and the heap below `NEXT`, misses `.rodata` and every stack
above the heap. -/
theorem alloc_apart {s t : MachineState} (ht : HeapOk t) {a : Word}
    (ha : Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext t)) :
    ¬ Within a rodataStart rodataSize ∧ ∀ lo n, heapEnd ≤ lo.toNat → Apart lo n nextAddr 8 →
      ¬ Within a lo n := by
  have := ht.hi
  refine ⟨fun h ↦ ?_, fun lo n hlo hn h ↦ ?_⟩ <;> rcases ha with ha | ha
  · addr_omega [h, ha]
  · addr_omega [h, ha, this]
  · addr_omega [h, ha, hn]
  · addr_omega [h, ha, hlo, this]

theorem NewBuf.buf {s t : MachineState} {p : Word} {n align : Nat} (h : NewBuf s t p n align)
    (hs : HeapOk s) : Buf t p n align := by
  have := hs.lo
  simp only [NewBuf, Buf] at h ⊢
  omega

/-! ## `Vec` -/

/-- A `Vec<T>`'s capacity, pointer and length, at `a`; a `RawVec<T>` is the first two. -/
def vecCap (s : MachineState) (a : Word) : Word := s.getMem a
def vecPtr (s : MachineState) (a : Word) : Word := s.getMem (a + 8)
def vecLen (s : MachineState) (a : Word) : Word := s.getMem (a + 16)

/-- The buffer of the `RawVec` at `a`, of `size`-byte elements aligned to `align`, is allocated. -/
def RawVecOk (s : MachineState) (a : Word) (size align : Nat) : Prop :=
  Buf s (vecPtr s a) ((vecCap s a).toNat * size) align

/-- A `Vec` at `a`: its buffer allocated, its length within its capacity. -/
structure VecOk (s : MachineState) (a : Word) (size align : Nat) : Prop where
  raw : RawVecOk s a size align
  len : (vecLen s a).toNat ≤ (vecCap s a).toNat

/-- The bytes of the elements of the `Vec` at `a`, of `size`-byte elements. -/
def vecBytes (s : MachineState) (a : Word) (size : Nat) : List (BitVec 8) :=
  bytesAt s (vecPtr s a) ((vecLen s a).toNat * size)

/-- The elements of a `Vec` of doublewords (`u64`, `K`, ..). -/
def vecWords (s : MachineState) (a : Word) : List Word :=
  s.readWords (vecPtr s a) (vecLen s a).toNat

/-- The elements of a `Vec<E>`. -/
def vecEs (s : MachineState) (a : Word) : List E :=
  eListAt s (vecPtr s a) (vecLen s a).toNat

end Rv64Verifier.Runtime
