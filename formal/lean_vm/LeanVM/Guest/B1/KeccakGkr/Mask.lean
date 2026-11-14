/-
  LeanVM.Guest.B1.KeccakGkr.Mask

  Values that are binary polynomials in one value `s`: a kernel-evaluated pass over a block of
  atoms gives each value's polynomial as a bit mask, sound for every valuation of the block.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib

/-!
# Polynomials in `s` over the bits

The instance weights of a layer (G:2678-2697) are sums of powers of the challenge `s`, combined at
compile time by `x·` (a product with `s`), `+` and products of such polynomials. A polynomial over `GF(2)` is a bit mask `m`;
its value at `s` is `pe m s = Σ_b [bit b of m] s^b`, and `+` is `xor` (characteristic two) and `s·`
a shift (`pe_xor`, `pe_shl`), a product of two a carry-less product (`clmul`, `pe_clmul`).

`maskRun sv st block` walks a block of constants `1`, additions, products with the value `sv` or
of two masked values, copies and loads (stores, skipped), keeping each value's mask; `maskRun_sound`: if the block
holds, every value the pass records is `pe` of its mask at `σ sv`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The value of the binary polynomial of mask `m` at `x` (degrees below 64). -/
def pe (m : ℕ) (x : E) : E := ∑ b ∈ range 64, if m.testBit b then x ^ b else 0

theorem pe_xor (a b : ℕ) (x : E) : pe (a ^^^ b) x = pe a x + pe b x := by
  simp only [pe, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp [e_add_self]

theorem pe_shl (a : ℕ) (ha : a < 2 ^ 63) (x : E) : pe (a <<< 1) x = x * pe a x := by
  have hb : ∀ i, (a <<< 1).testBit (i + 1) = a.testBit i := by
    intro i; rw [Nat.testBit_shiftLeft]; simp
  have h0 : (a <<< 1).testBit 0 = false := by rw [Nat.testBit_shiftLeft]; simp
  have h63 : a.testBit 63 = false := Nat.testBit_eq_false_of_lt ha
  unfold pe
  rw [Finset.sum_range_succ', Finset.sum_range_succ (fun b => if a.testBit b then x ^ b else 0) 63,
    mul_add, Finset.mul_sum]
  simp only [hb, h0, h63, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> simp [pow_succ, mul_comm]

theorem pe_one (x : E) : pe 1 x = 1 := by
  unfold pe
  rw [Finset.sum_range_succ']
  simp [Nat.testBit_succ]

/-- The carry-less product of two masks of at most `32` bits: a product of polynomials over
`GF(2)`. -/
def clmul (a b : ℕ) : ℕ :=
  (List.range 32).foldl (fun acc i ↦ if b.testBit i then acc ^^^ (a <<< i) else acc) 0

theorem pe_shl_n (a : ℕ) (x : E) : ∀ n, a < 2 ^ (64 - n) → n ≤ 63 →
    pe (a <<< n) x = x ^ n * pe a x
  | 0, _, _ => by simp
  | n + 1, ha, hn => by
    have h1 : a <<< n < 2 ^ 63 := by
      rw [Nat.shiftLeft_eq]
      calc a * 2 ^ n < 2 ^ (64 - (n + 1)) * 2 ^ n :=
            Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos n)
        _ = 2 ^ 63 := by rw [← pow_add]; congr 1; omega
    have ih := pe_shl_n a x n (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      (by omega)
    rw [show a <<< (n + 1) = (a <<< n) <<< 1 by rw [Nat.shiftLeft_add], pe_shl _ h1, ih]
    ring

theorem pe_of_lt' (m n : ℕ) (hm : m < 2 ^ n) (hn : n ≤ 64) (x : E) :
    pe m x = ∑ b ∈ range n, if m.testBit b then x ^ b else 0 := by
  unfold pe
  refine (Finset.sum_subset (fun b hb ↦ by simp at hb ⊢; omega) fun b _ hb ↦ ?_).symm
  have hnb : n ≤ b := by simpa using hb
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hnb))]
  simp

theorem pe_clmul_aux (a b : ℕ) (ha : a < 2 ^ 32) (x : E) : ∀ n ≤ 32,
    pe ((List.range n).foldl (fun acc i ↦ if b.testBit i then acc ^^^ (a <<< i) else acc) 0) x =
      pe a x * ∑ i ∈ range n, if b.testBit i then x ^ i else 0
  | 0, _ => by simp [pe]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, mul_add, ← pe_clmul_aux a b ha x n (by omega)]
    split
    · rename_i hb
      rw [pe_xor, pe_shl_n a x n (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
        (by omega)]
      ring
    · rename_i hb
      rw [mul_zero, add_zero]

/-- **A carry-less product is the product of the polynomials.** -/
theorem pe_clmul (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (x : E) :
    pe (clmul a b) x = pe a x * pe b x := by
  rw [clmul, pe_clmul_aux a b ha x 32 le_rfl, pe_of_lt' b 32 hb (by norm_num)]

/-- One atom of the pass. -/
def maskStep (sv : V) (st : List (V × ℕ)) : Stmt → Option (List (V × ℕ))
  | .atom (.const d c) => if eEqb c (word 1 0) then some ((d, 1) :: st) else none
  | .atom (.add d a b) =>
      match st.lookup a, st.lookup b with
      | some ma, some mb => some ((d, ma ^^^ mb) :: st)
      | _, _ => none
  | .atom (.mul d a b) =>
      if b = sv then
        match st.lookup a with
        | some ma => if ma < 2 ^ 63 then some ((d, ma <<< 1) :: st) else none
        | none => none
      else if a = sv then
        match st.lookup b with
        | some mb => if mb < 2 ^ 63 then some ((d, mb <<< 1) :: st) else none
        | none => none
      else
        match st.lookup a, st.lookup b with
        | some ma, some mb =>
            if ma < 2 ^ 32 ∧ mb < 2 ^ 32 then some ((d, clmul ma mb) :: st) else none
        | _, _ => none
  | .atom (.copy d a) =>
      match st.lookup a with
      | some ma => some ((d, ma) :: st)
      | none => none
  | .atom (.load _ _ _) => some st
  | _ => none

/-- The pass over a block. -/
def maskRun (sv : V) : List (V × ℕ) → List Stmt → Option (List (V × ℕ))
  | st, [] => some st
  | st, s :: ss =>
      match maskStep sv st s with
      | some st' => maskRun sv st' ss
      | none => none

/-- Every recorded value is its mask's polynomial at `x`. -/
def MaskOk (σ : Val) (x : E) (st : List (V × ℕ)) : Prop := ∀ p ∈ st, σ p.1 = pe p.2 x

theorem MaskOk.lookup {x : E} {st : List (V × ℕ)} (h : MaskOk σ x st) {v : V} {m : ℕ}
    (hl : st.lookup v = some m) : σ v = pe m x := by
  induction st with
  | nil => simp at hl
  | cons p st ih =>
    rcases p with ⟨w, mw⟩
    by_cases hw : v = w
    · subst hw
      simp at hl
      subst hl
      exact h _ (List.mem_cons_self ..)
    · simp only [List.lookup, show (v == w) = false by simpa using hw] at hl
      exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hl

theorem maskStep_sound {sv : V} {st st' : List (V × ℕ)} {s : Stmt} (hs : maskStep sv st s = some st')
    (hok : MaskOk σ (σ sv) st) {next : Prop} {kret : List E → Prop}
    (h : Stmt.Holds C rd σ s next kret) : MaskOk σ (σ sv) st' ∧ next := by
  match s, hs with
  | .atom (.const d c), hs =>
    simp only [maskStep] at hs
    split at hs
    · rename_i hc
      cases hs
      obtain ⟨hd, hn⟩ := h
      refine ⟨fun p hp => ?_, hn⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only [Atom.Holds] at hd; rw [hd, eEqb_sound hc, word_one, pe_one]
      · exact hok p hp
    · cases hs
  | .atom (.add d a b), hs =>
    simp only [maskStep] at hs
    split at hs
    · rename_i ma mb ha hb
      cases hs
      obtain ⟨hd, hn⟩ := h
      refine ⟨fun p hp => ?_, hn⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only [Atom.Holds] at hd; rw [hd, hok.lookup ha, hok.lookup hb, pe_xor]
      · exact hok p hp
    · cases hs
  | .atom (.mul d a b), hs =>
    simp only [maskStep] at hs
    split at hs
    · rename_i hb
      split at hs
      · rename_i ma ha
        split at hs
        · rename_i hlt
          cases hs
          obtain ⟨hd, hn⟩ := h
          refine ⟨fun p hp => ?_, hn⟩
          rcases List.mem_cons.1 hp with rfl | hp
          · simp only [Atom.Holds] at hd; subst hb
            rw [hd, hok.lookup ha, pe_shl _ hlt, mul_comm]
          · exact hok p hp
        · cases hs
      · cases hs
    · split at hs
      · rename_i ha'
        split at hs
        · rename_i mb hb'
          split at hs
          · rename_i hlt
            cases hs
            obtain ⟨hd, hn⟩ := h
            refine ⟨fun p hp => ?_, hn⟩
            rcases List.mem_cons.1 hp with rfl | hp
            · simp only [Atom.Holds] at hd; subst ha'
              rw [hd, hok.lookup hb', pe_shl _ hlt]
            · exact hok p hp
          · cases hs
        · cases hs
      · split at hs
        · rename_i ma mb ha hb
          split at hs
          · rename_i hlt
            cases hs
            obtain ⟨hd, hn⟩ := h
            refine ⟨fun p hp => ?_, hn⟩
            rcases List.mem_cons.1 hp with rfl | hp
            · simp only [Atom.Holds] at hd
              rw [hd, hok.lookup ha, hok.lookup hb, pe_clmul _ _ hlt.1 hlt.2]
            · exact hok p hp
          · cases hs
        · cases hs
  | .atom (.copy d a), hs =>
    simp only [maskStep] at hs
    split at hs
    · rename_i ma ha
      cases hs
      obtain ⟨hd, hn⟩ := h
      refine ⟨fun p hp => ?_, hn⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only [Atom.Holds] at hd; rw [hd, hok.lookup ha]
      · exact hok p hp
    · cases hs
  | .atom (.load _ _ _), hs =>
    simp only [maskStep, Option.some.injEq] at hs
    subst hs
    exact ⟨hok, h.2⟩

/-- **The pass is sound**: from a sound start, if the block holds, every value the pass records is
its mask's polynomial at `σ sv`. -/
theorem maskRun_sound {sv : V} : ∀ {st st' : List (V × ℕ)} {ss : List Stmt},
    maskRun sv st ss = some st' → MaskOk σ (σ sv) st → ∀ {next : Prop} {kret : List E → Prop},
    Stmt.HoldsList C rd σ ss next kret → MaskOk σ (σ sv) st' ∧ next
  | st, st', [], hr, hok, _, _, h => by
    simp only [maskRun, Option.some.injEq] at hr
    subst hr; exact ⟨hok, h⟩
  | st, st', s :: ss, hr, hok, next, kret, h => by
    simp only [maskRun] at hr
    split at hr
    · rename_i st1 h1
      obtain ⟨hok1, hrest⟩ := maskStep_sound h1 hok h
      exact maskRun_sound hr hok1 hrest
    · cases hr

end
end LeanVM.Guest.B1.VerifySub
