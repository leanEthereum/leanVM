module

public import NativeRustcVm.Mem
import all Kraken.Mem

/-!
# Facts about the memory vocabulary

What contracts and proofs of `rustc/vm`'s functions read `NativeRustcVm.Mem`'s predicates by:

- addresses: `a + i` as numbers (`toNat_add_ofNat`, `toNat_sub_ofNat`), `InRange` as an interval
  (`inRange_iff`), `NoWrap` and `Apart` of sub-ranges (`NoWrap.sub`, `Apart.mono`, `apart_of_le`);
- `SameOutside`: `refl`, `trans`, `mono`, and bytes outside the change kept
  (`BytesAt.of_sameOutside`, `BytesAt.of_sameOutside_apart`);
- `BytesAt`: concatenations, slices, an index, a write over part of it (`BytesAt.write`,
  `BytesAt.set`);
- arrays of fixed-size elements (`BytesAt d a (xs.flatMap f)`, each `f x` of `k` bytes): an
  element at `a + k i` (`BytesAt.flatMap_getElem`), from its elements
  (`bytesAt_flatMap_of_getElem`), one element written (`BytesAt.flatMap_set`); instantiated for
  words (`WordsAt`, eight bytes) and `E` elements (`EWsAt`, sixteen bytes);
- `Region`, `Disjoint`, `InAny` unfolded on lists;
- the word view: `wordView d a = some w` exactly where `WordAt d a.toBitVec w`
  (`wordView_eq_some_iff`).
-/

namespace NativeRustcVm

open NativeVm.Model

public section

/-! ## Addresses -/

theorem addr_add_add (a : BitVec 64) (o i : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem addr_add_zero (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := by
  simp

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_add_ofNat {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt h]

theorem toNat_sub_ofNat {b : BitVec 64} {n : Nat} (h : n ≤ b.toNat) :
    (b - BitVec.ofNat 64 n).toNat = b.toNat - n := by
  have := b.isLt
  rw [BitVec.toNat_sub, toNat_ofNat_of_lt (by omega),
    show 2 ^ 64 - n + b.toNat = (b.toNat - n) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- An address is the base plus its offset. -/
theorem add_sub_toNat (a p : BitVec 64) : a + BitVec.ofNat 64 (p - a).toNat = p := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-! ## `NoWrap`, `InRange`, `Apart` -/

theorem NoWrap.mono {a : BitVec 64} {n m : Nat} (h : NoWrap a n) (hm : m ≤ n) : NoWrap a m := by
  unfold NoWrap at *; omega

/-- A sub-range of a range that does not wrap does not wrap. -/
theorem NoWrap.sub {a : BitVec 64} {n o m : Nat} (h : NoWrap a n) (hm : o + m ≤ n) :
    NoWrap (a + BitVec.ofNat 64 o) m := by
  unfold NoWrap at *
  by_cases hm0 : m = 0
  · subst hm0; have := (a + BitVec.ofNat 64 o).isLt; omega
  · rw [toNat_add_ofNat (by omega)]; omega

theorem noWrap_zero (a : BitVec 64) : NoWrap a 0 := by
  unfold NoWrap; have := a.isLt; omega

/-- `InRange` of bytes that do not wrap is an interval of addresses. -/
theorem inRange_iff {x a : BitVec 64} {n : Nat} (hx : NoWrap x n) :
    InRange x n a ↔ x.toNat ≤ a.toNat ∧ a.toNat < x.toNat + n := by
  unfold InRange NoWrap at *
  rw [BitVec.toNat_sub]
  have := a.isLt
  have := x.isLt
  constructor
  · intro h
    by_cases hle : x.toNat ≤ a.toNat
    · rw [show 2 ^ 64 - x.toNat + a.toNat = (a.toNat - x.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - x.toNat + a.toNat = (a.toNat - x.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Byte `i` of `n` is in range. -/
theorem inRange_add {a : BitVec 64} {n i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    InRange a n (a + BitVec.ofNat 64 i) := by
  unfold InRange
  rw [BitVec.add_comm, BitVec.add_sub_cancel, toNat_ofNat_of_lt (by omega)]
  exact hi

theorem inRange_self {a : BitVec 64} {n : Nat} (hn : 0 < n) : InRange a n a := by
  unfold InRange; simpa using hn

/-- A byte in range is the base plus an offset below the size. -/
theorem InRange.exists {a p : BitVec 64} {n : Nat} (h : InRange a n p) :
    ∃ i < n, p = a + BitVec.ofNat 64 i :=
  ⟨_, h, (add_sub_toNat a p).symm⟩

/-- A byte of a range is a byte of a range that holds it. -/
theorem InRange.mono {a b p : BitVec 64} {n m : Nat} (h : InRange a n p) (ha : NoWrap a n)
    (hb : NoWrap b m) (h1 : b.toNat ≤ a.toNat) (h2 : a.toNat + n ≤ b.toNat + m) :
    InRange b m p := by
  rw [inRange_iff ha] at h; rw [inRange_iff hb]; omega

/-- A byte of the sub-range from offset `o` is a byte of the range. -/
theorem InRange.of_sub {a p : BitVec 64} {n o m : Nat} (h : InRange (a + BitVec.ofNat 64 o) m p)
    (ha : NoWrap a n) (hm : o + m ≤ n) : InRange a n p := by
  by_cases hm0 : m = 0
  · subst hm0; exact absurd h (by unfold InRange; omega)
  · have := ha.sub hm
    unfold NoWrap at ha
    exact h.mono this ha (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)

theorem Apart.symm {a b : BitVec 64} {n m : Nat} (h : Apart a n b m) : Apart b m a n := by
  unfold Apart at *; omega

/-- Ranges inside apart ranges are apart. -/
theorem Apart.mono {a b a' b' : BitVec 64} {n m n' m' : Nat} (h : Apart a n b m)
    (ha1 : a.toNat ≤ a'.toNat) (ha2 : a'.toNat + n' ≤ a.toNat + n)
    (hb1 : b.toNat ≤ b'.toNat) (hb2 : b'.toNat + m' ≤ b.toNat + m) : Apart a' n' b' m' := by
  unfold Apart at *; omega

/-- A range apart from another is apart from a range inside it. -/
theorem Apart.mono_right {a x y : BitVec 64} {n N n' : Nat} (h : Apart a n x N)
    (h1 : x.toNat ≤ y.toNat) (h2 : y.toNat + n' ≤ x.toNat + N) : Apart a n y n' :=
  h.mono (Nat.le_refl _) (Nat.le_refl _) h1 h2

/-- `a + i` as a number, for `i` up to the end of a range that does not wrap: `a.toNat + i`, or
`0` at the very end of the address space. -/
theorem toNat_add_ofNat_le {a : BitVec 64} {i : Nat} (h : a.toNat + i ≤ 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i ∨
      ((a + BitVec.ofNat 64 i).toNat = 0 ∧ a.toNat + i = 2 ^ 64) := by
  rcases Nat.lt_or_ge (a.toNat + i) (2 ^ 64) with hlt | hge
  · exact .inl (toNat_add_ofNat hlt)
  · refine .inr ⟨?_, by omega⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, show a.toNat + i = 2 ^ 64 by omega,
      Nat.mod_self]

/-- Sub-ranges `o, n` and `o', n'` of one range are apart where they do not overlap. -/
theorem apart_of_le {a : BitVec 64} {N o n o' n' : Nat} (hN : NoWrap a N) (h : o + n ≤ N)
    (h' : o' + n' ≤ N) (hle : o + n ≤ o' ∨ o' + n' ≤ o) :
    Apart (a + BitVec.ofNat 64 o) n (a + BitVec.ofNat 64 o') n' := by
  unfold NoWrap at hN
  unfold Apart
  have h1 := toNat_add_ofNat_le (a := a) (i := o) (by omega)
  have h2 := toNat_add_ofNat_le (a := a) (i := o') (by omega)
  omega

/-- Byte `i` of a range is not in its sub-range `o, m` if not between `o` and `o + m`. -/
theorem not_inRange_sub {a : BitVec 64} {N o m i : Nat} (hN : NoWrap a N) (hm : o + m ≤ N)
    (hi : i < N) (hio : i < o ∨ o + m ≤ i) :
    ¬InRange (a + BitVec.ofNat 64 o) m (a + BitVec.ofNat 64 i) := by
  by_cases hm0 : m = 0
  · subst hm0; unfold InRange; omega
  · unfold NoWrap at hN
    rw [inRange_iff (hx := ?_), toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    · omega
    · unfold NoWrap; rw [toNat_add_ofNat (by omega)]; omega

/-- No byte of a range is a byte of a range apart from it. -/
theorem Apart.not_inRange {a b p : BitVec 64} {n m : Nat} (h : Apart a n b m) (ha : NoWrap a n)
    (hb : NoWrap b m) (hp : InRange a n p) : ¬InRange b m p := by
  rw [inRange_iff ha] at hp; rw [inRange_iff hb]; unfold Apart at h; omega

/-- Byte `i` of a range is not a byte of a range apart from it. -/
theorem Apart.not_inRange_add {a b : BitVec 64} {n m i : Nat} (h : Apart a n b m)
    (ha : NoWrap a n) (hb : NoWrap b m) (hi : i < n) : ¬InRange b m (a + BitVec.ofNat 64 i) :=
  h.not_inRange ha hb (inRange_add hi (by unfold NoWrap at ha; omega))

/-! ## `SameOutside` -/

theorem SameOutside.refl (d : Mem 64) (R : BitVec 64 → Prop) : SameOutside d d R :=
  fun _ _ ↦ rfl

theorem SameOutside.of_eq {d d' : Mem 64} (h : d' = d) (R : BitVec 64 → Prop) :
    SameOutside d d' R := fun _ _ ↦ by rw [h]

theorem SameOutside.mono {d d' : Mem 64} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (hR : ∀ p, R p → R' p) : SameOutside d d' R' :=
  fun p hp ↦ h p fun h' ↦ hp (hR p h')

theorem SameOutside.trans {d d' d'' : Mem 64} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (h' : SameOutside d' d'' R') : SameOutside d d'' fun p ↦ R p ∨ R' p :=
  fun p hp ↦ (h' p fun h ↦ hp (.inr h)).trans (h p fun h ↦ hp (.inl h))

/-- Two changes inside one set of addresses are one. -/
theorem SameOutside.trans' {d d' d'' : Mem 64} {R : BitVec 64 → Prop} (h : SameOutside d d' R)
    (h' : SameOutside d' d'' R) : SameOutside d d'' R :=
  (h.trans h').mono fun _ h ↦ h.elim id id

theorem SameOutside.symm {d d' : Mem 64} {R : BitVec 64 → Prop} (h : SameOutside d d' R) :
    SameOutside d' d R := fun p hp ↦ (h p hp).symm

/-! ## `BytesAt` -/

theorem BytesAt.nil (d : Mem 64) (a : BitVec 64) : BytesAt d a [] := fun _ h ↦ absurd h (by simp)

theorem BytesAt.get {d : Mem 64} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) {i : Nat}
    (hi : i < bs.length) : d.get? (a + BitVec.ofNat 64 i) = some bs[i] := h i hi

theorem BytesAt.mapped {d : Mem 64} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    Mapped d a bs.length := fun i hi ↦ by rw [h i hi]; rfl

theorem bytesAt_singleton_iff {d : Mem 64} {a : BitVec 64} {b : UInt8} :
    BytesAt d a [b] ↔ d.get? a = some b := by
  constructor
  · intro h; simpa using h 0 (by simp)
  · intro h i hi
    obtain rfl : i = 0 := by simpa using hi
    simpa using h

theorem bytesAt_append_iff {d : Mem 64} {a : BitVec 64} {bs cs : List UInt8} :
    BytesAt d a (bs ++ cs) ↔ BytesAt d a bs ∧ BytesAt d (a + BitVec.ofNat 64 bs.length) cs := by
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · rw [addr_add_add, h _ (by simp; omega), List.getElem_append_right (by omega)]
      simp
  · intro ⟨h₁, h₂⟩ i hi
    by_cases h : i < bs.length
    · rw [List.getElem_append_left h]
      exact h₁ i h
    · rw [List.getElem_append_right (by omega)]
      have := h₂ (i - bs.length) (by simp at hi; omega)
      rwa [addr_add_add, show bs.length + (i - bs.length) = i by omega] at this

theorem BytesAt.append {d : Mem 64} {a : BitVec 64} {bs cs : List UInt8} (h₁ : BytesAt d a bs)
    (h₂ : BytesAt d (a + BitVec.ofNat 64 bs.length) cs) : BytesAt d a (bs ++ cs) :=
  bytesAt_append_iff.mpr ⟨h₁, h₂⟩

theorem BytesAt.left {d : Mem 64} {a : BitVec 64} {bs cs : List UInt8}
    (h : BytesAt d a (bs ++ cs)) : BytesAt d a bs := (bytesAt_append_iff.mp h).1

theorem BytesAt.right {d : Mem 64} {a : BitVec 64} {bs cs : List UInt8}
    (h : BytesAt d a (bs ++ cs)) : BytesAt d (a + BitVec.ofNat 64 bs.length) cs :=
  (bytesAt_append_iff.mp h).2

theorem bytesAt_cons_iff {d : Mem 64} {a : BitVec 64} {b : UInt8} {bs : List UInt8} :
    BytesAt d a (b :: bs) ↔ d.get? a = some b ∧ BytesAt d (a + BitVec.ofNat 64 1) bs := by
  rw [show b :: bs = [b] ++ bs from rfl, bytesAt_append_iff, bytesAt_singleton_iff]; rfl

theorem BytesAt.take {d : Mem 64} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) (n : Nat) :
    BytesAt d a (bs.take n) := (List.take_append_drop n bs ▸ h).left

theorem BytesAt.drop {d : Mem 64} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) (o : Nat) :
    BytesAt d (a + BitVec.ofNat 64 o) (bs.drop o) := by
  intro i hi
  simp only [List.length_drop] at hi
  rw [addr_add_add, h (o + i) (by omega)]
  simp

theorem BytesAt.slice {d : Mem 64} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (o n : Nat) : BytesAt d (a + BitVec.ofNat 64 o) ((bs.drop o).take n) := (h.drop o).take n

/-- Two byte strings of one length at one address are equal. -/
theorem BytesAt.unique {d : Mem 64} {a : BitVec 64} {bs cs : List UInt8} (h : BytesAt d a bs)
    (h' : BytesAt d a cs) (hl : bs.length = cs.length) : bs = cs :=
  List.ext_getElem hl fun i hi hi' ↦ Option.some.inj ((h i hi).symm.trans (h' i hi'))

theorem BytesAt.congr {d : Mem 64} {a : BitVec 64} {bs cs : List UInt8} (h : BytesAt d a bs)
    (he : bs = cs) : BytesAt d a cs := he ▸ h

/-- Bytes no change touches are kept. -/
theorem BytesAt.of_sameOutside {d d' : Mem 64} {a : BitVec 64} {bs : List UInt8}
    {R : BitVec 64 → Prop} (h : BytesAt d a bs) (hs : SameOutside d d' R)
    (hR : ∀ i < bs.length, ¬R (a + BitVec.ofNat 64 i)) : BytesAt d' a bs := fun i hi ↦ by
  rw [hs _ (hR i hi)]
  exact h i hi

/-- Bytes apart from a changed range are kept. -/
theorem BytesAt.of_sameOutside_apart {d d' : Mem 64} {a b : BitVec 64} {bs : List UInt8} {m : Nat}
    (h : BytesAt d a bs) (hs : SameOutside d d' (InRange b m)) (hap : Apart a bs.length b m)
    (ha : NoWrap a bs.length) (hb : NoWrap b m) : BytesAt d' a bs :=
  h.of_sameOutside hs fun _ hi ↦ hap.not_inRange_add ha hb hi

/-- Bytes apart from changed regions are kept. -/
theorem BytesAt.of_sameOutside_inAny {d d' : Mem 64} {a : BitVec 64} {bs : List UInt8}
    {rs : List Region} (h : BytesAt d a bs) (hs : SameOutside d d' (InAny rs))
    (hap : ∀ r ∈ rs, Apart a bs.length r.addr r.size ∧ NoWrap r.addr r.size)
    (ha : NoWrap a bs.length) : BytesAt d' a bs :=
  h.of_sameOutside hs fun _ hi ⟨r, hr, hp⟩ ↦
    (hap r hr).1.not_inRange_add ha (hap r hr).2 hi hp

/-- **A write over part of the bytes**: the bytes from `a` with `cs` from offset `o` on. -/
theorem BytesAt.write {d d' : Mem 64} {a : BitVec 64} {bs cs : List UInt8} {o : Nat}
    (h : BytesAt d a bs) (hc : BytesAt d' (a + BitVec.ofNat 64 o) cs)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 o) cs.length))
    (ho : o + cs.length ≤ bs.length) (ha : NoWrap a bs.length) :
    BytesAt d' a (bs.take o ++ cs ++ bs.drop (o + cs.length)) := by
  have hmo : o ≤ bs.length := by omega
  refine BytesAt.append (BytesAt.append ?_ ?_) ?_
  · refine (h.take o).of_sameOutside hs fun i hi ↦ ?_
    simp only [List.length_take, Nat.min_eq_left hmo] at hi
    exact not_inRange_sub ha ho (by omega) (.inl hi)
  · simpa [List.length_take, Nat.min_eq_left hmo] using hc
  · simp only [List.length_append, List.length_take, Nat.min_eq_left hmo]
    refine (h.drop (o + cs.length)).of_sameOutside hs fun i hi ↦ ?_
    simp only [List.length_drop] at hi
    rw [addr_add_add]
    exact not_inRange_sub ha ho (by omega) (.inr (by omega))

/-- **A one-byte store** into the bytes from `a`. -/
theorem BytesAt.set {d d' : Mem 64} {a : BitVec 64} {bs : List UInt8} {i : Nat} {b : UInt8}
    (h : BytesAt d a bs) (hb : d'.get? (a + BitVec.ofNat 64 i) = some b)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 i) 1)) (hi : i < bs.length)
    (ha : NoWrap a bs.length) : BytesAt d' a (bs.set i b) := by
  have := h.write (cs := [b]) (bytesAt_singleton_iff.mpr hb) hs (by simpa using hi) ha
  refine this.congr ?_
  simp [List.set_eq_take_append_cons_drop, hi]

/-! ## `Mapped` -/

theorem Mapped.mono {d : Mem 64} {a : BitVec 64} {n m : Nat} (h : Mapped d a n) (hm : m ≤ n) :
    Mapped d a m := fun i hi ↦ h i (by omega)

theorem Mapped.sub {d : Mem 64} {a : BitVec 64} {n o m : Nat} (h : Mapped d a n)
    (hm : o + m ≤ n) : Mapped d (a + BitVec.ofNat 64 o) m := fun i hi ↦ by
  rw [addr_add_add]; exact h _ (by omega)

theorem mapped_append_iff {d : Mem 64} {a : BitVec 64} {n m : Nat} :
    Mapped d a (n + m) ↔ Mapped d a n ∧ Mapped d (a + BitVec.ofNat 64 n) m := by
  refine ⟨fun h ↦ ⟨h.mono (by omega), h.sub (by omega)⟩, fun ⟨h₁, h₂⟩ i hi ↦ ?_⟩
  by_cases hin : i < n
  · exact h₁ i hin
  · have := h₂ (i - n) (by omega)
    rwa [addr_add_add, show n + (i - n) = i by omega] at this

/-- Mapped bytes stay mapped where a change keeps them. -/
theorem Mapped.of_sameOutside {d d' : Mem 64} {a : BitVec 64} {n : Nat} {R : BitVec 64 → Prop}
    (h : Mapped d a n) (hs : SameOutside d d' R) (hR : ∀ i < n, ¬R (a + BitVec.ofNat 64 i)) :
    Mapped d' a n := fun i hi ↦ by rw [hs _ (hR i hi)]; exact h i hi

/-! ## Arrays of fixed-size elements -/

section Arrays

variable {α : Type} {f : α → List UInt8} {k : Nat}

theorem length_flatMap_const (hf : ∀ x, (f x).length = k) (xs : List α) :
    (xs.flatMap f).length = k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, hf, ih, Nat.mul_succ, Nat.add_comm]

theorem take_flatMap_const (hf : ∀ x, (f x).length = k) :
    ∀ (xs : List α) (j : Nat), (xs.flatMap f).take (k * j) = (xs.take j).flatMap f
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: xs, j + 1 => by
    rw [show k * (j + 1) = (f x).length + k * j by rw [hf, Nat.mul_succ, Nat.add_comm],
      List.flatMap_cons, List.take_length_add_append, take_flatMap_const hf xs j,
      List.take_succ_cons, List.flatMap_cons]

theorem drop_flatMap_const (hf : ∀ x, (f x).length = k) :
    ∀ (xs : List α) (j : Nat), (xs.flatMap f).drop (k * j) = (xs.drop j).flatMap f
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: xs, j + 1 => by
    rw [show k * (j + 1) = (f x).length + k * j by rw [hf, Nat.mul_succ, Nat.add_comm],
      List.flatMap_cons, List.drop_length_add_append, drop_flatMap_const hf xs j,
      List.drop_succ_cons]

theorem bytesAt_flatMap_cons_iff {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k)
    {x : α} {xs : List α} :
    BytesAt d a ((x :: xs).flatMap f) ↔
      BytesAt d a (f x) ∧ BytesAt d (a + BitVec.ofNat 64 k) (xs.flatMap f) := by
  rw [List.flatMap_cons, bytesAt_append_iff, hf]

theorem bytesAt_flatMap_append_iff {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k)
    {xs ys : List α} :
    BytesAt d a ((xs ++ ys).flatMap f) ↔
      BytesAt d a (xs.flatMap f) ∧
        BytesAt d (a + BitVec.ofNat 64 (k * xs.length)) (ys.flatMap f) := by
  rw [List.flatMap_append, bytesAt_append_iff, length_flatMap_const hf]

/-- The elements from `j` on start `k j` bytes on. -/
theorem BytesAt.flatMap_drop {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k) {xs : List α}
    (h : BytesAt d a (xs.flatMap f)) (j : Nat) :
    BytesAt d (a + BitVec.ofNat 64 (k * j)) ((xs.drop j).flatMap f) := by
  rcases Nat.lt_or_ge xs.length j with hj | hj
  · rw [List.drop_of_length_le (by omega)]; exact BytesAt.nil _ _
  · have := (bytesAt_flatMap_append_iff hf (xs := xs.take j) (ys := xs.drop j)).mp
      (by rwa [List.take_append_drop])
    simpa [List.length_take, Nat.min_eq_left hj] using this.2

theorem BytesAt.flatMap_take {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k) {xs : List α}
    (h : BytesAt d a (xs.flatMap f)) (j : Nat) : BytesAt d a ((xs.take j).flatMap f) :=
  ((bytesAt_flatMap_append_iff hf).mp (by rwa [List.take_append_drop])).1

/-- **Element `i`** of an array is at `a + k i`. -/
theorem BytesAt.flatMap_getElem {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k)
    {xs : List α} (h : BytesAt d a (xs.flatMap f)) {i : Nat} (hi : i < xs.length) :
    BytesAt d (a + BitVec.ofNat 64 (k * i)) (f xs[i]) := by
  have := h.flatMap_drop hf i
  rw [List.drop_eq_getElem_cons hi] at this
  exact ((bytesAt_flatMap_cons_iff hf).mp this).1

/-- An array from its elements. -/
theorem bytesAt_flatMap_of_getElem {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k) :
    ∀ {xs : List α}, (∀ i (hi : i < xs.length), BytesAt d (a + BitVec.ofNat 64 (k * i)) (f xs[i])) →
      BytesAt d a (xs.flatMap f)
  | [], _ => BytesAt.nil _ _
  | x :: xs, h => by
    have h0 := h 0 (by simp)
    rw [List.getElem_cons_zero, Nat.mul_zero, addr_add_zero] at h0
    refine (bytesAt_flatMap_cons_iff hf).mpr ⟨h0, ?_⟩
    refine bytesAt_flatMap_of_getElem (a := a + BitVec.ofNat 64 k) hf fun i hi ↦ ?_
    have := h (i + 1) (by simp; omega)
    rwa [addr_add_add, show k + k * i = k * (i + 1) by rw [Nat.mul_succ]; omega]

theorem bytesAt_flatMap_iff {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k)
    {xs : List α} : BytesAt d a (xs.flatMap f) ↔
      ∀ i (hi : i < xs.length), BytesAt d (a + BitVec.ofNat 64 (k * i)) (f xs[i]) :=
  ⟨fun h _ hi ↦ h.flatMap_getElem hf hi, bytesAt_flatMap_of_getElem hf⟩

/-- **One element written**: element `i` replaced by what is now at `a + k i`. -/
theorem BytesAt.flatMap_set {d d' : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k)
    {xs : List α} {i : Nat} {y : α} (h : BytesAt d a (xs.flatMap f))
    (hy : BytesAt d' (a + BitVec.ofNat 64 (k * i)) (f y))
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (k * i)) k)) (hi : i < xs.length)
    (ha : NoWrap a (k * xs.length)) : BytesAt d' a ((xs.set i y).flatMap f) := by
  have hlen := length_flatMap_const hf xs
  have hk : k * i + k ≤ k * xs.length := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have := h.write (o := k * i) (cs := f y) hy (by rwa [hf]) (by rw [hf, hlen]; exact hk)
    (by rwa [hlen])
  refine this.congr ?_
  rw [take_flatMap_const hf, hf, show k * i + k = k * (i + 1) by rw [Nat.mul_succ],
    drop_flatMap_const hf]
  simp [List.set_eq_take_append_cons_drop, hi, List.flatMap_append]

theorem BytesAt.flatMap_mapped {d : Mem 64} {a : BitVec 64} (hf : ∀ x, (f x).length = k)
    {xs : List α} (h : BytesAt d a (xs.flatMap f)) : Mapped d a (k * xs.length) :=
  length_flatMap_const hf xs ▸ h.mapped

end Arrays

/-! ## Words and `E` elements -/

theorem length_wordBytes (w : UInt64) : (wordBytes w).length = 8 := by
  simp [wordBytes, LeanVM.Protocol.KeccakHash.wordBytes]

theorem length_ewBytes (x : EW) : (ewBytes x).length = 16 := by
  simp [ewBytes, length_wordBytes]

theorem length_wordsBytes (ws : List UInt64) : (ws.flatMap wordBytes).length = 8 * ws.length :=
  length_flatMap_const length_wordBytes ws

theorem length_ewsBytes (xs : List EW) : (xs.flatMap ewBytes).length = 16 * xs.length :=
  length_flatMap_const length_ewBytes xs

/-- The number of a word's bytes is the word. -/
theorem leNat_wordBytes (w : UInt64) : leNat (wordBytes w) = w.toNat := by
  have := w.toNat_lt
  simp only [leNat, wordBytes, LeanVM.Protocol.KeccakHash.wordBytes, List.range_succ,
    List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.foldr_append, List.foldr_cons, List.foldr_nil]
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem ofNat_leNat_wordBytes (w : UInt64) : UInt64.ofNat (leNat (wordBytes w)) = w := by
  rw [leNat_wordBytes]; exact UInt64.ofNat_toNat

/-- The bytes of the word of eight bytes are they. -/
theorem wordBytes_ofNat_leNat {bs : List UInt8} (h : bs.length = 8) :
    wordBytes (UInt64.ofNat (leNat bs)) = bs := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    simp only [leNat, wordBytes, LeanVM.Protocol.KeccakHash.wordBytes, List.range_succ,
      List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, List.cons_append, List.cons.injEq, and_true]
    simp only [← UInt8.toNat_inj]
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega

theorem WordAt.mapped {d : Mem 64} {a : BitVec 64} {w : UInt64} (h : WordAt d a w) :
    Mapped d a 8 := length_wordBytes w ▸ BytesAt.mapped h

theorem WordAt.unique {d : Mem 64} {a : BitVec 64} {w w' : UInt64} (h : WordAt d a w)
    (h' : WordAt d a w') : w = w' := by
  have := BytesAt.unique h h' (by rw [length_wordBytes, length_wordBytes])
  rw [← ofNat_leNat_wordBytes w, ← ofNat_leNat_wordBytes w', this]

theorem wordsAt_nil (d : Mem 64) (a : BitVec 64) : WordsAt d a [] := BytesAt.nil _ _

theorem wordsAt_cons_iff {d : Mem 64} {a : BitVec 64} {w : UInt64} {ws : List UInt64} :
    WordsAt d a (w :: ws) ↔ WordAt d a w ∧ WordsAt d (a + BitVec.ofNat 64 8) ws :=
  bytesAt_flatMap_cons_iff length_wordBytes

theorem wordsAt_append_iff {d : Mem 64} {a : BitVec 64} {ws vs : List UInt64} :
    WordsAt d (a) (ws ++ vs) ↔
      WordsAt d a ws ∧ WordsAt d (a + BitVec.ofNat 64 (8 * ws.length)) vs :=
  bytesAt_flatMap_append_iff length_wordBytes

theorem wordsAt_singleton_iff {d : Mem 64} {a : BitVec 64} {w : UInt64} :
    WordsAt d a [w] ↔ WordAt d a w := by
  simp [WordsAt, WordAt]

/-- **Word `i`** of the words from `a` is at `a + 8 i`. -/
theorem WordsAt.getElem {d : Mem 64} {a : BitVec 64} {ws : List UInt64} (h : WordsAt d a ws)
    {i : Nat} (hi : i < ws.length) : WordAt d (a + BitVec.ofNat 64 (8 * i)) ws[i] :=
  BytesAt.flatMap_getElem length_wordBytes h hi

theorem wordsAt_iff {d : Mem 64} {a : BitVec 64} {ws : List UInt64} :
    WordsAt d a ws ↔ ∀ i (hi : i < ws.length), WordAt d (a + BitVec.ofNat 64 (8 * i)) ws[i] :=
  bytesAt_flatMap_iff length_wordBytes

theorem WordsAt.take {d : Mem 64} {a : BitVec 64} {ws : List UInt64} (h : WordsAt d a ws)
    (j : Nat) : WordsAt d a (ws.take j) := BytesAt.flatMap_take length_wordBytes h j

theorem WordsAt.drop {d : Mem 64} {a : BitVec 64} {ws : List UInt64} (h : WordsAt d a ws)
    (j : Nat) : WordsAt d (a + BitVec.ofNat 64 (8 * j)) (ws.drop j) :=
  BytesAt.flatMap_drop length_wordBytes h j

theorem WordsAt.mapped {d : Mem 64} {a : BitVec 64} {ws : List UInt64} (h : WordsAt d a ws) :
    Mapped d a (8 * ws.length) := BytesAt.flatMap_mapped length_wordBytes h

/-- **A word stored** over word `i`. -/
theorem WordsAt.set {d d' : Mem 64} {a : BitVec 64} {ws : List UInt64} {i : Nat} {w : UInt64}
    (h : WordsAt d a ws) (hw : WordAt d' (a + BitVec.ofNat 64 (8 * i)) w)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (8 * i)) 8)) (hi : i < ws.length)
    (ha : NoWrap a (8 * ws.length)) : WordsAt d' a (ws.set i w) :=
  BytesAt.flatMap_set length_wordBytes h hw hs hi ha

theorem ewAt_iff {d : Mem 64} {a : BitVec 64} {x : EW} :
    EWAt d a x ↔ WordAt d a x.c0 ∧ WordAt d (a + BitVec.ofNat 64 8) x.c1 := by
  rw [EWAt, ewBytes, bytesAt_append_iff, length_wordBytes]; rfl

theorem EWAt.mapped {d : Mem 64} {a : BitVec 64} {x : EW} (h : EWAt d a x) :
    Mapped d a 16 := length_ewBytes x ▸ BytesAt.mapped h

theorem ewsAt_nil (d : Mem 64) (a : BitVec 64) : EWsAt d a [] := BytesAt.nil _ _

theorem ewsAt_cons_iff {d : Mem 64} {a : BitVec 64} {x : EW} {xs : List EW} :
    EWsAt d a (x :: xs) ↔ EWAt d a x ∧ EWsAt d (a + BitVec.ofNat 64 16) xs :=
  bytesAt_flatMap_cons_iff length_ewBytes

theorem ewsAt_append_iff {d : Mem 64} {a : BitVec 64} {xs ys : List EW} :
    EWsAt d a (xs ++ ys) ↔
      EWsAt d a xs ∧ EWsAt d (a + BitVec.ofNat 64 (16 * xs.length)) ys :=
  bytesAt_flatMap_append_iff length_ewBytes

theorem ewsAt_singleton_iff {d : Mem 64} {a : BitVec 64} {x : EW} :
    EWsAt d a [x] ↔ EWAt d a x := by
  simp [EWsAt, EWAt]

/-- **Element `i`** of the `E` elements from `a` is at `a + 16 i`. -/
theorem EWsAt.getElem {d : Mem 64} {a : BitVec 64} {xs : List EW} (h : EWsAt d a xs)
    {i : Nat} (hi : i < xs.length) : EWAt d (a + BitVec.ofNat 64 (16 * i)) xs[i] :=
  BytesAt.flatMap_getElem length_ewBytes h hi

theorem ewsAt_iff {d : Mem 64} {a : BitVec 64} {xs : List EW} :
    EWsAt d a xs ↔ ∀ i (hi : i < xs.length), EWAt d (a + BitVec.ofNat 64 (16 * i)) xs[i] :=
  bytesAt_flatMap_iff length_ewBytes

theorem EWsAt.take {d : Mem 64} {a : BitVec 64} {xs : List EW} (h : EWsAt d a xs)
    (j : Nat) : EWsAt d a (xs.take j) := BytesAt.flatMap_take length_ewBytes h j

theorem EWsAt.drop {d : Mem 64} {a : BitVec 64} {xs : List EW} (h : EWsAt d a xs)
    (j : Nat) : EWsAt d (a + BitVec.ofNat 64 (16 * j)) (xs.drop j) :=
  BytesAt.flatMap_drop length_ewBytes h j

theorem EWsAt.mapped {d : Mem 64} {a : BitVec 64} {xs : List EW} (h : EWsAt d a xs) :
    Mapped d a (16 * xs.length) := BytesAt.flatMap_mapped length_ewBytes h

/-- **An `E` element stored** over element `i`. -/
theorem EWsAt.set {d d' : Mem 64} {a : BitVec 64} {xs : List EW} {i : Nat} {x : EW}
    (h : EWsAt d a xs) (hx : EWAt d' (a + BitVec.ofNat 64 (16 * i)) x)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (16 * i)) 16)) (hi : i < xs.length)
    (ha : NoWrap a (16 * xs.length)) : EWsAt d' a (xs.set i x) :=
  BytesAt.flatMap_set length_ewBytes h hx hs hi ha

/-! ## Regions -/

theorem region_holds_iff {r : Region} {p : BitVec 64} (h : NoWrap r.addr r.size) :
    r.Holds p ↔ r.addr.toNat ≤ p.toNat ∧ p.toNat < r.addr.toNat + r.size := inRange_iff h

@[simp] theorem disjoint_nil : Disjoint [] := List.Pairwise.nil

@[simp] theorem disjoint_cons_iff {r : Region} {rs : List Region} :
    Disjoint (r :: rs) ↔ (∀ r' ∈ rs, Apart r.addr r.size r'.addr r'.size) ∧ Disjoint rs :=
  List.pairwise_cons

/-- Two regions of a disjoint list, at different indices, are apart. -/
theorem Disjoint.apart {rs : List Region} (h : Disjoint rs) {i j : Nat} (hi : i < rs.length)
    (hj : j < rs.length) (hij : i ≠ j) :
    Apart rs[i].addr rs[i].size rs[j].addr rs[j].size := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_getElem.mp h i j hi hj hlt
  · exact (List.pairwise_iff_getElem.mp h j i hj hi hlt).symm

@[simp] theorem inAny_nil (p : BitVec 64) : ¬InAny [] p := by
  simp [InAny]

@[simp] theorem inAny_cons_iff {r : Region} {rs : List Region} {p : BitVec 64} :
    InAny (r :: rs) p ↔ r.Holds p ∨ InAny rs p := by
  simp [InAny]

theorem InAny.of_mem {rs : List Region} {r : Region} (hr : r ∈ rs) {p : BitVec 64}
    (hp : r.Holds p) : InAny rs p := ⟨r, hr, hp⟩

/-- The regions of a sub-list hold fewer bytes. -/
theorem InAny.mono {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') {p : BitVec 64}
    (hp : InAny rs p) : InAny rs' p :=
  let ⟨r, hr, hp⟩ := hp; ⟨r, h r hr, hp⟩

/-- A byte of a range apart from each region is in none of them. -/
theorem not_inAny_of_apart {rs : List Region} {a p : BitVec 64} {n : Nat}
    (hap : ∀ r ∈ rs, Apart a n r.addr r.size ∧ NoWrap r.addr r.size) (ha : NoWrap a n)
    (hp : InRange a n p) : ¬InAny rs p := fun ⟨r, hr, h⟩ ↦
  (hap r hr).1.not_inRange ha (hap r hr).2 hp h

/-! ## The word view -/

theorem mapM_id_eq_some_iff {β : Type} :
    ∀ {l : List (Option β)} {bs : List β}, l.mapM id = some bs ↔ l = bs.map some
  | [], bs => by cases bs <;> simp
  | x :: l, bs => by
    cases x with
    | none => cases bs <;> simp
    | some b =>
      cases bs with
      | nil => simp [List.mapM_cons]; cases l.mapM id <;> simp
      | cons c cs =>
        simp only [List.mapM_cons, id, List.map_cons, List.cons.injEq, Option.some.injEq]
        rw [← mapM_id_eq_some_iff (l := l) (bs := cs)]
        cases l.mapM id <;> simp [eq_comm]

/-- The `bs.length` bytes from `a` load as `bs` exactly where they are `bs`. -/
theorem loadBytes_eq_some_iff {d : Mem 64} {a : BitVec 64} {bs : List UInt8} :
    d.loadBytes a bs.length = some bs ↔ BytesAt d a bs := by
  unfold Mem.loadBytes
  rw [mapM_id_eq_some_iff]
  constructor
  · intro h i hi
    have := congrArg (·[i]?) h
    simpa [hi] using this
  · intro h
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact h i (by simpa using h1)

theorem length_of_loadBytes {d : Mem 64} {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : d.loadBytes a n = some bs) : bs.length = n := by
  unfold Mem.loadBytes at h
  rw [mapM_id_eq_some_iff] at h
  simpa using (congrArg List.length h).symm

/-- **The word view** holds `w` at `a` exactly where the word at `a` is `w`. -/
theorem wordView_eq_some_iff {d : Mem 64} {a : UInt64} {w : UInt64} :
    wordView d a = some w ↔ WordAt d a.toBitVec w := by
  constructor
  · intro h
    obtain ⟨bs, hbs, hw⟩ := Option.map_eq_some_iff.mp h
    have hl := length_of_loadBytes hbs
    rw [← hl] at hbs
    have := loadBytes_eq_some_iff.mp hbs
    rw [WordAt, ← hw, wordBytes_ofNat_leNat hl]
    exact this
  · intro h
    have := loadBytes_eq_some_iff.mpr h
    rw [length_wordBytes] at this
    rw [wordView, this, Option.map_some, ofNat_leNat_wordBytes]

theorem WordAt.wordView {d : Mem 64} {a : UInt64} {w : UInt64} (h : WordAt d a.toBitVec w) :
    wordView d a = some w := wordView_eq_some_iff.mpr h

theorem wordAt_of_wordView {d : Mem 64} {a : UInt64} {w : UInt64} (h : wordView d a = some w) :
    WordAt d a.toBitVec w := wordView_eq_some_iff.mp h

end

end NativeRustcVm
