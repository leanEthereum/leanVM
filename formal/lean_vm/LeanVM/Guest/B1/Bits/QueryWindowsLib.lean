/-
  LeanVM.Guest.B1.Bits.QueryWindowsLib

  Tiled sums of digits, and the atoms of `decode_query_windows`' template.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Common.Atoms

/-!
# Tiled sums, and the template's blocks

* `tS s v n = Σ_{t<n} 2^(s t)·v t`, the digits `v t < 2^(s (t+1) - s t)` on the tiles `[s t, s (t+1))`
  of a monotone `s`: `tS_lt` (below `2^(s n)`), `tS_mod` (a prefix is the sum modulo its tile's
  start), `tS_get` (each digit read back), `eOfNat192_tS` (the sum of the digits' words, shifted).
* `qwAH rd σ ss`: every atom of the block holds. Every block of `qwBody` is atoms only
  (`qwBody_atoms`), so its relation is that (`holdsList_atoms`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Tiled sums -/

/-- `Σ_{t<n} 2^(s t)·v t`. -/
def tS (s v : ℕ → ℕ) (n : ℕ) : ℕ := ∑ t ∈ Finset.range n, 2 ^ s t * v t

/-- The digits fit their tiles, of a monotone `s`, up to `m`. -/
def Tiled (s v : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ t < m, s t ≤ s (t + 1) ∧ v t < 2 ^ (s (t + 1) - s t)

theorem tS_succ (s v : ℕ → ℕ) (n : ℕ) : tS s v (n + 1) = tS s v n + 2 ^ s n * v n := by
  rw [tS, Finset.sum_range_succ]; rfl

theorem tS_lt {s v : ℕ → ℕ} {m : ℕ} (h : Tiled s v m) : ∀ n ≤ m, tS s v n < 2 ^ s n
  | 0, _ => by simp [tS]
  | n + 1, hn => by
    obtain ⟨hs, hv⟩ := h n (by omega)
    have ih := tS_lt h n (by omega)
    rw [tS_succ]
    have hp : 2 ^ s (n + 1) = 2 ^ s n * 2 ^ (s (n + 1) - s n) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hs]
    rw [hp]
    calc tS s v n + 2 ^ s n * v n < 2 ^ s n + 2 ^ s n * v n := by omega
      _ = 2 ^ s n * (v n + 1) := by ring
      _ ≤ 2 ^ s n * 2 ^ (s (n + 1) - s n) := Nat.mul_le_mul_left _ hv

theorem tS_mod {s v : ℕ → ℕ} {m : ℕ} (h : Tiled s v m) {n : ℕ} (hn : n ≤ m) :
    ∀ k, n + k ≤ m → tS s v (n + k) % 2 ^ s n = tS s v n
  | 0, _ => by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt (tS_lt h n hn)
  | k + 1, hk => by
    have ih := tS_mod h hn k (by omega)
    rw [← Nat.add_assoc, tS_succ]
    have hle : s n ≤ s (n + k) := by
      clear ih
      induction k with
      | zero => rfl
      | succ k ihk => exact le_trans (ihk (by omega)) ((h (n + k) (by omega)).1)
    have hd : 2 ^ s n ∣ 2 ^ s (n + k) := Nat.pow_dvd_pow 2 hle
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.mul_assoc, Nat.add_mul_mod_self_left, ih]

theorem tS_get {s v : ℕ → ℕ} {m : ℕ} (h : Tiled s v m) {i : ℕ} (hi : i < m) :
    tS s v m / 2 ^ s i % 2 ^ (s (i + 1) - s i) = v i := by
  obtain ⟨hs, hv⟩ := h i hi
  rw [← Nat.mod_mul_right_div_self, ← Nat.pow_add, Nat.add_sub_cancel' hs]
  have := tS_mod h (n := i + 1) (by omega) (m - (i + 1)) (by omega)
  rw [show i + 1 + (m - (i + 1)) = m by omega] at this
  rw [this, tS_succ, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (tS_lt h i (by omega)), Nat.zero_add]

/-- Two words of disjoint bits add as their integers: `a < 2^s`. -/
theorem eOfNat192_add_shift {a s b : ℕ} (ha : a < 2 ^ s) :
    eOfNat192 a + eOfNat192 (2 ^ s * b) = eOfNat192 (a + 2 ^ s * b) := by
  rw [← eOfNat192_xor, Nat.xor_comm, two_pow_mul_xor ha, Nat.add_comm]

theorem eOfNat192_tS {s v : ℕ → ℕ} {m : ℕ} (h : Tiled s v m) : ∀ n ≤ m,
    ∑ t ∈ Finset.range n, eOfNat192 (2 ^ s t * v t) = eOfNat192 (tS s v n)
  | 0, _ => by simp [tS, eOfNat192_zero]
  | n + 1, hn => by
    rw [Finset.sum_range_succ, eOfNat192_tS h n (by omega), eOfNat192_add_shift
      (tS_lt h n (by omega)), tS_succ]

/-! ## Values of optional sums -/

/-- The value of a running sum, `0` while the compiler folds it. -/
def qwOpt (σ : Val) : Option V → E
  | none => 0
  | some v => σ v

/-! ## Atom blocks -/

/-- Every atom of the block holds. -/
def qwAH (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ a, Stmt.atom a ∈ ss → a.Holds rd σ

theorem qwAH_append {rd : Reader} {σ : Val} {xs ys : List Stmt} :
    qwAH rd σ (xs ++ ys) ↔ qwAH rd σ xs ∧ qwAH rd σ ys := by
  simp only [qwAH, List.mem_append]
  exact ⟨fun h ↦ ⟨fun a ha ↦ h a (Or.inl ha), fun a ha ↦ h a (Or.inr ha)⟩,
    fun h a ha ↦ ha.elim (h.1 a) (h.2 a)⟩

theorem qwAH_cons {rd : Reader} {σ : Val} {a : Atom} {ss : List Stmt} :
    qwAH rd σ (.atom a :: ss) ↔ a.Holds rd σ ∧ qwAH rd σ ss := by
  simp only [qwAH, List.mem_cons, Stmt.atom.injEq]
  exact ⟨fun h ↦ ⟨h a (Or.inl rfl), fun b hb ↦ h b (Or.inr hb)⟩,
    fun h b hb ↦ hb.elim (fun e ↦ e ▸ h.1) (h.2 b)⟩

theorem qwAH_nil {rd : Reader} {σ : Val} : qwAH rd σ [] ↔ True := by simp [qwAH]

/-- A statement is an atom. -/
def isAtomB : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem allAtoms_of_all {ss : List Stmt} (h : ss.all isAtomB = true) : AllAtoms ss := fun s hs ↦ by
  have := List.all_eq_true.mp h s hs
  cases s with
  | atom a => exact ⟨a, rfl⟩
  | _ => simp [isAtomB] at this

theorem qwScale_atoms (x : V) (c k : ℕ) : (qwScale x c k).1.all isAtomB = true := by
  unfold qwScale; split <;> simp [isAtomB]

theorem qwAcc_atoms (acc : Option V) (t : V) (k : ℕ) : (qwAcc acc t k).1.all isAtomB = true := by
  cases acc <;> simp [qwAcc, isAtomB]

theorem qwRead_atoms (c : V) (start w k : ℕ) : (qwRead c start w k).1.all isAtomB = true := by
  simp [qwRead, isAtomB]

theorem qwSquares_atoms (x : V) : ∀ a k, (qwSquares x a k).1.all isAtomB = true
  | 0, _ => rfl
  | a + 1, k => by
    simp only [qwSquares, List.all_cons, isAtomB, Bool.true_and]
    exact qwSquares_atoms _ a _

theorem qwSplit_atoms (c : V) (start a w k : ℕ) : (qwSplit c start a w k).1.all isAtomB = true := by
  simp only [qwSplit, List.all_append, qwSquares_atoms, List.all_cons, List.all_nil, isAtomB,
    Bool.and_true]

theorem qwWindow_atoms (d cd base cut at0 i k : ℕ) (lo hi : Option V) :
    (qwWindow d cd base cut at0 i k lo hi).1.all isAtomB = true := by
  simp only [qwWindow]
  split_ifs <;> simp only [List.all_append, qwRead_atoms, qwScale_atoms, qwAcc_atoms,
    qwSplit_atoms, Bool.and_true]

theorem qwWindows_atoms (d cd base cut at0 : ℕ) : ∀ i n k lo hi,
    (qwWindows d cd base cut at0 i n k lo hi).1.all isAtomB = true
  | _, 0, _, _, _ => rfl
  | i, n + 1, k, lo, hi => by
    simp only [qwWindows, List.all_append, qwWindow_atoms, qwWindows_atoms, Bool.and_true]

theorem qwPr_atoms (j base cut d k : ℕ) (lo hi : V) (recon : Option V) :
    (qwPr j base cut d k lo hi recon).1.all isAtomB = true := by
  unfold qwPr; split
  · simp [isAtomB]
  · split <;> simp [isAtomB]

theorem qwPtr_atoms (j n k : ℕ) : (qwPtr j n k).1.all isAtomB = true := by
  unfold qwPtr; split <;> simp [isAtomB]

theorem qwPos_atoms (d cd j k : ℕ) (recon : Option V) :
    (qwPos d cd j k recon).1.all isAtomB = true := by
  simp only [qwPos, List.all_append, qwWindows_atoms, qwPr_atoms, qwPtr_atoms, Bool.and_true]

theorem qwPositions_atoms (d cd : ℕ) : ∀ j n k recon,
    (qwPositions d cd j n k recon).1.all isAtomB = true
  | _, 0, _, _ => rfl
  | j, n + 1, k, recon => by
    simp only [qwPositions, List.all_append, qwPos_atoms, qwPositions_atoms, Bool.and_true]

theorem qwRest_atoms (d : ℕ) : ∀ i n k recon, (qwRest d i n k recon).1.all isAtomB = true
  | _, 0, _, _ => rfl
  | i, n + 1, k, recon => by
    simp only [qwRest, List.all_append, qwRead_atoms, qwScale_atoms, qwAcc_atoms, qwRest_atoms,
      Bool.and_true]

/-! ## The blocks' values -/

theorem cbWord_zero' : cbWord 0 = 1 := by rw [cbWord]; exact word_one

theorem cbWord_eq' (i : ℕ) : cbWord i = coordBasis i := by
  simp only [cbWord, word, ofBits_mod]; rfl

theorem qwScale_val {rd : Reader} {σ : Val} {x : V} {c k : ℕ} (h : qwAH rd σ (qwScale x c k).1) :
    σ (qwScale x c k).2.2 = σ x * cbWord c := by
  by_cases hc : c = 0
  · simp only [qwScale, hc, ↓reduceIte, cbWord_zero', mul_one]
  · simp only [qwScale, hc, ↓reduceIte, qwAH_cons, qwAH_nil, Atom.Holds] at h ⊢
    rw [h.2.1, h.1]

theorem qwAcc_val {rd : Reader} {σ : Val} {acc : Option V} {t : V} {k : ℕ}
    (h : qwAH rd σ (qwAcc acc t k).1) : qwOpt σ (qwAcc acc t k).2.2 = qwOpt σ acc + σ t := by
  cases acc with
  | none => simp [qwAcc, qwOpt]
  | some a =>
    simp only [qwAcc, qwAH_cons, qwAH_nil, Atom.Holds] at h
    simp [qwAcc, qwOpt, h.1]

theorem qwSquares_val {rd : Reader} {σ : Val} : ∀ {x : V} {a k : ℕ},
    qwAH rd σ (qwSquares x a k).1 → σ (qwSquares x a k).2 = σ x ^ (2 ^ a)
  | _, 0, _, _ => by simp [qwSquares]
  | x, a + 1, k, h => by
    simp only [qwSquares, qwAH_cons, Atom.Holds] at h ⊢
    rw [qwSquares_val h.2, h.1, pow_succ, pow_mul, sq, mul_pow]

end
end LeanVM.Guest.B1
