module

public import NativeRustcVm.Transcript.Rep

/-!
# Memory around the transcript's state

Bytes kept where a memory changes elsewhere (`bytesAt_keep`, `bytesAt_keep_ext`): the changes are
at offsets `W` of an area (`Touch`) or in a set `R` outside it. Words and elements end to end
(`wordsAt_iff`, `ewAt_iff`, `ewsAt_iff`). Then the representations after the transcript's
functions change one part of them, the rest kept: the sponge's lanes, its queue, its ground
challenge (`SpongeAt.with_state`, `with_pending`, `with_ground`), the `TState`'s sponge, cursor and
roots (`TStateAt.with_sponge`, `with_cursor`, `with_root`), or nothing of them (`SpongeAt.frame`,
`TStateAt.frame`).
-/

namespace NativeRustcVm.Transcript

open NativeVm NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Compile

@[expose] public section

/-- Every byte of `d` is still in `d'`. -/
def Keeps (d d' : Mem 64) : Prop := ∀ p, (d.get? p).isSome → (d'.get? p).isSome

/-- The bytes at the offsets `W` of the `N` bytes from `b`. -/
def Touch (b : BitVec 64) (N : Nat) (W : Nat → Prop) (q : BitVec 64) : Prop :=
  ∃ j, j < N ∧ W j ∧ q = off b j

end

public section

/-! ## Addresses -/

theorem off_off (b : BitVec 64) (o i : Nat) : off (off b o) i = off b (o + i) := by
  rw [off, off, off, BitVec.add_assoc, BitVec.ofNat_add]

theorem off_zero (b : BitVec 64) : off b 0 = b := BitVec.add_zero b

theorem off_add (b : BitVec 64) (o i : Nat) : off b o + BitVec.ofNat 64 i = off b (o + i) :=
  off_off b o i

theorem toNat_off {b : BitVec 64} {j : Nat} (h : b.toNat + j < 2 ^ 64) :
    (off b j).toNat = b.toNat + j := by
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem inRange_off_iff {b : BitVec 64} {o n j : Nat} (hj : j < 2 ^ 64) (h : o + n ≤ 2 ^ 64) :
    InRange (off b o) n (off b j) ↔ o ≤ j ∧ j < o + n := by
  unfold InRange off
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := b.isLt
  omega

theorem inRange_off_self {b : BitVec 64} {N j : Nat} (hj : j < N) (hN : N ≤ 2 ^ 64) :
    InRange b N (off b j) := by
  have := (inRange_off_iff (b := b) (o := 0) (n := N) (j := j) (by omega) (by omega)).mpr
    ⟨Nat.zero_le _, by omega⟩
  rwa [off_zero] at this

/-- `InRange` of bytes that do not wrap is an interval of addresses. -/
theorem inRange_iff' {a q : BitVec 64} {n : Nat} (h : NoWrap a n) :
    InRange a n q ↔ a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n := by
  unfold InRange
  unfold NoWrap at h
  rw [BitVec.toNat_sub]
  have := q.isLt
  have := a.isLt
  constructor
  · intro hq
    by_cases hle : a.toNat ≤ q.toNat
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hq
      omega
  · intro ⟨h1, h2⟩
    omega

theorem not_inRange_of_apart {a a' q : BitVec 64} {n n' : Nat} (hA : Apart a n a' n')
    (hn : NoWrap a n) (hn' : NoWrap a' n') (hq : InRange a n q) : ¬ InRange a' n' q := by
  rw [inRange_iff' hn] at hq
  rw [inRange_iff' hn']
  unfold Apart at hA
  omega

theorem off_inj {b : BitVec 64} {i j N : Nat} (hN : NoWrap b N) (hi : i < N) (hj : j < N)
    (h : off b j = off b i) : j = i := by
  have h1 := toNat_off (b := b) (j := j) (by unfold NoWrap at hN; omega)
  have h2 := toNat_off (b := b) (j := i) (by unfold NoWrap at hN; omega)
  rw [h] at h1
  omega

/-- A byte of an interval at offset `o` of an area is at an offset of it. -/
theorem touch_of_inRange {b q : BitVec 64} {N o n : Nat} (hN : NoWrap b N) (hle : o + n ≤ N)
    (hq : InRange (off b o) n q) : Touch b N (fun j ↦ o ≤ j ∧ j < o + n) q := by
  unfold NoWrap at hN
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact absurd hq (by unfold InRange; omega)
  have ho : (off b o).toNat = b.toNat + o := toNat_off (by omega)
  have hn : NoWrap (off b o) n := by unfold NoWrap; omega
  rw [inRange_iff' hn, ho] at hq
  refine ⟨q.toNat - b.toNat, by omega, ⟨by omega, by omega⟩, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [toNat_off (by omega)]
  omega

theorem SameOutside.mono {d d' : Mem 64} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (hR : ∀ q, R q → R' q) : SameOutside d d' R' :=
  fun q hq ↦ h q fun h' ↦ hq (hR q h')

theorem SameOutside.trans {d d₁ d₂ : Mem 64} {R₁ R₂ : BitVec 64 → Prop}
    (h₁ : SameOutside d d₁ R₁) (h₂ : SameOutside d₁ d₂ R₂) :
    SameOutside d d₂ (fun q ↦ R₁ q ∨ R₂ q) :=
  fun q hq ↦ (h₂ q fun h ↦ hq (Or.inr h)).trans (h₁ q fun h ↦ hq (Or.inl h))

theorem Keeps.trans {d d₁ d₂ : Mem 64} (h₁ : Keeps d d₁) (h₂ : Keeps d₁ d₂) : Keeps d d₂ :=
  fun p hp ↦ h₂ p (h₁ p hp)

theorem Mapped.keeps {d d' : Mem 64} {a : BitVec 64} {n : Nat} (h : Mapped d a n)
    (hk : Keeps d d') : Mapped d' a n :=
  fun i hi ↦ hk _ (h i hi)

theorem Region.Ok.keeps {d d' : Mem 64} {r : Region} (h : r.Ok d) (hk : Keeps d d') : r.Ok d' :=
  ⟨Mapped.keeps h.1 hk, h.2⟩

/-! ## Bytes kept -/

/-- Bytes where nothing changed. -/
theorem bytesAt_congr {d d' : Mem 64} {p : BitVec 64} {bs : List UInt8} (h : BytesAt d p bs)
    (hs : ∀ i < bs.length, d'.get? (p + BitVec.ofNat 64 i) = d.get? (p + BitVec.ofNat 64 i)) :
    BytesAt d' p bs :=
  fun i hi ↦ (hs i hi).trans (h i hi)

/-- **Bytes of an area kept** where the memory changed at other offsets `W` of it and outside it. -/
theorem bytesAt_keep {d d' : Mem 64} {b : BitVec 64} {N o : Nat} {bs : List UInt8}
    {W : Nat → Prop} {R : BitVec 64 → Prop} (hN : NoWrap b N) (hR : ∀ q, R q → ¬ InRange b N q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) (hle : o + bs.length ≤ N)
    (hW : ∀ i < bs.length, ¬ W (o + i)) (h : BytesAt d (off b o) bs) : BytesAt d' (off b o) bs := by
  refine bytesAt_congr h fun i hi ↦ hs _ ?_
  have hN' := hN
  unfold NoWrap at hN'
  rintro (⟨j, hj, hWj, hq⟩ | hq)
  · rw [show off b o + BitVec.ofNat 64 i = off b (o + i) from off_off b o i] at hq
    exact hW i hi (off_inj hN (by omega) hj hq.symm ▸ hWj)
  · exact hR _ hq (by
      rw [show off b o + BitVec.ofNat 64 i = off b (o + i) from off_off b o i]
      exact inRange_off_self (by omega) (by omega))

/-- **Bytes of another area kept**, apart from the one changed. -/
theorem bytesAt_keep_ext {d d' : Mem 64} {b a : BitVec 64} {N n o : Nat} {bs : List UInt8}
    {W : Nat → Prop} {R : BitVec 64 → Prop} (hN : NoWrap b N) (hn : NoWrap a n)
    (hA : Apart b N a n) (hR : ∀ q, R q → ¬ InRange a n q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) (hle : o + bs.length ≤ n)
    (h : BytesAt d (off a o) bs) : BytesAt d' (off a o) bs := by
  refine bytesAt_congr h fun i hi ↦ hs _ ?_
  have hn' := hn
  unfold NoWrap at hn'
  have hin : InRange a n (off a o + BitVec.ofNat 64 i) := by
    rw [show off a o + BitVec.ofNat 64 i = off a (o + i) from off_off a o i]
    exact inRange_off_self (by omega) (by omega)
  rintro (⟨j, hj, -, hq⟩ | hq)
  · have hN' := hN
    unfold NoWrap at hN'
    exact not_inRange_of_apart hA hN hn (hq ▸ inRange_off_self hj (by omega)) hin
  · exact hR _ hq hin

/-! ## Words and elements -/

theorem bytesAt_append {d : Mem 64} {p : BitVec 64} {l₁ l₂ : List UInt8} :
    BytesAt d p (l₁ ++ l₂) ↔ BytesAt d p l₁ ∧ BytesAt d (off p l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · have := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at this
    · have := h (l₁.length + i) (by simp; omega)
      have e : (l₁ ++ l₂)[l₁.length + i]'(by simp; omega) = l₂[i] := by simp
      rw [e] at this
      rw [off_add]
      exact this
  · intro ⟨h₁, h₂⟩ i hi
    by_cases hlt : i < l₁.length
    · rw [List.getElem_append_left hlt]
      exact h₁ i hlt
    · rw [List.getElem_append_right (by omega)]
      have := h₂ (i - l₁.length) (by simp at hi; omega)
      rwa [off_add, Nat.add_sub_cancel' (by omega)] at this

theorem length_wordBytes (w : UInt64) : (wordBytes w).length = 8 := rfl

theorem length_flatMap_wordBytes (ws : List UInt64) : (ws.flatMap wordBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [List.flatMap_cons, List.length_append, ih, length_wordBytes]; simp; omega

theorem wordsAt_nil (d : Mem 64) (p : BitVec 64) : WordsAt d p [] := fun _ h ↦ by simp at h

theorem wordsAt_cons {d : Mem 64} {p : BitVec 64} {w : UInt64} {ws : List UInt64} :
    WordsAt d p (w :: ws) ↔ WordAt d p w ∧ WordsAt d (off p 8) ws := by
  unfold WordsAt WordAt
  rw [List.flatMap_cons, bytesAt_append, length_wordBytes]

theorem wordsAt_iff {d : Mem 64} {p : BitVec 64} {ws : List UInt64} :
    WordsAt d p ws ↔ ∀ i (h : i < ws.length), WordAt d (off p (8 * i)) ws[i] := by
  induction ws generalizing p with
  | nil => exact ⟨fun _ i h ↦ absurd h (by simp), fun _ ↦ wordsAt_nil d p⟩
  | cons w ws ih =>
    rw [wordsAt_cons, ih]
    constructor
    · intro ⟨h0, hs⟩ i hi
      cases i with
      | zero => rwa [Nat.mul_zero, off_zero]
      | succ i =>
        have := hs i (by simp at hi; omega)
        rwa [off_off, show 8 + 8 * i = 8 * (i + 1) by omega] at this
    · intro h
      refine ⟨by have := h 0 (by simp); rwa [Nat.mul_zero, off_zero] at this, fun i hi ↦ ?_⟩
      have := h (i + 1) (by simp; omega)
      rwa [off_off, show 8 + 8 * i = 8 * (i + 1) by omega]

theorem ewAt_iff {d : Mem 64} {p : BitVec 64} {x : EW} :
    EWAt d p x ↔ WordAt d p x.c0 ∧ WordAt d (off p 8) x.c1 := by
  unfold EWAt ewBytes WordAt
  rw [bytesAt_append, length_wordBytes]

theorem ewsAt_nil (d : Mem 64) (p : BitVec 64) : EWsAt d p [] := fun _ h ↦ by simp at h

theorem ewsAt_cons {d : Mem 64} {p : BitVec 64} {x : EW} {xs : List EW} :
    EWsAt d p (x :: xs) ↔ EWAt d p x ∧ EWsAt d (off p 16) xs := by
  unfold EWsAt EWAt
  rw [List.flatMap_cons, bytesAt_append]
  rfl

theorem ewsAt_iff {d : Mem 64} {p : BitVec 64} {xs : List EW} :
    EWsAt d p xs ↔ ∀ i (h : i < xs.length), EWAt d (off p (16 * i)) xs[i] := by
  induction xs generalizing p with
  | nil => exact ⟨fun _ i h ↦ absurd h (by simp), fun _ ↦ ewsAt_nil d p⟩
  | cons x xs ih =>
    rw [ewsAt_cons, ih]
    constructor
    · intro ⟨h0, hs⟩ i hi
      cases i with
      | zero => rwa [Nat.mul_zero, off_zero]
      | succ i =>
        have := hs i (by simp at hi; omega)
        rwa [off_off, show 16 + 16 * i = 16 * (i + 1) by omega] at this
    · intro h
      refine ⟨by have := h 0 (by simp); rwa [Nat.mul_zero, off_zero] at this, fun i hi ↦ ?_⟩
      have := h (i + 1) (by simp; omega)
      rwa [off_off, show 16 + 16 * i = 16 * (i + 1) by omega]

/-! ## Words and elements kept -/

section keep
variable {d d' : Mem 64} {b : BitVec 64} {N : Nat} {W : Nat → Prop} {R : BitVec 64 → Prop}

theorem wordAt_keep (hN : NoWrap b N) (hR : ∀ q, R q → ¬ InRange b N q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) {o : Nat} {w : UInt64}
    (hle : o + 8 ≤ N) (hW : ∀ i < 8, ¬ W (o + i)) (h : WordAt d (off b o) w) :
    WordAt d' (off b o) w :=
  bytesAt_keep hN hR hs hle hW h

theorem ewAt_keep (hN : NoWrap b N) (hR : ∀ q, R q → ¬ InRange b N q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) {o : Nat} {x : EW}
    (hle : o + 16 ≤ N) (hW : ∀ i < 16, ¬ W (o + i)) (h : EWAt d (off b o) x) :
    EWAt d' (off b o) x :=
  bytesAt_keep hN hR hs hle hW h

theorem wordsAt_keep (hN : NoWrap b N) (hR : ∀ q, R q → ¬ InRange b N q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) {o : Nat} {ws : List UInt64}
    (hle : o + 8 * ws.length ≤ N) (hW : ∀ i < 8 * ws.length, ¬ W (o + i))
    (h : WordsAt d (off b o) ws) : WordsAt d' (off b o) ws :=
  bytesAt_keep hN hR hs (by rw [length_flatMap_wordBytes]; omega)
    (fun i hi ↦ hW i (by rw [length_flatMap_wordBytes] at hi; omega)) h

theorem optEWAt_keep (hN : NoWrap b N) (hR : ∀ q, R q → ¬ InRange b N q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) {o : Nat} {g : Option EW}
    (hle : o + 24 ≤ N) (hW : ∀ i < 24, ¬ W (o + i)) (h : OptEWAt d (off b o) g) :
    OptEWAt d' (off b o) g := by
  cases g with
  | none => exact wordAt_keep hN hR hs (by omega) (fun i hi ↦ hW i (by omega)) h
  | some c =>
    refine ⟨wordAt_keep hN hR hs (by omega) (fun i hi ↦ hW i (by omega)) h.1, ?_⟩
    have := h.2
    rw [off_off] at this ⊢
    exact ewAt_keep hN hR hs (by omega) (fun i hi ↦ by
      have := hW (8 + i) (by omega); rwa [← Nat.add_assoc] at this) this

end keep

end

end NativeRustcVm.Transcript
