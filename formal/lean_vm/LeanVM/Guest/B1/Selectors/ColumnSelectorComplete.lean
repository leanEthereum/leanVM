/-
  LeanVM.Guest.B1.Selectors.ColumnSelectorComplete

  `column_selector` is complete: for an offset `g^o`, `o < 2^32` a multiple of `2^κ`, and the
  opening point's tables in memory, the eq weight of `o`'s bits above `κ` is an outcome of
  `column_selector__L{κ}`.
-/

module

public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.CoreData

/-!
# `column_selector` is complete (TRIAGE G #68)

The valuation `cskVal` gives every value of `column_selector__L{κ}`'s body its role: the hint's
digits are `o`'s base-16 digits `u_k` from nibble `κ / 4` on (`cskU`); in nibble `k`, the range
check's bound `g^15`, its cofactor `g^(15 - u_k)` and the two words it reads (the memory is
defined below `2^4`), the pointer into the eq table, the eq weight (`cskXE`), the running eq
product (`cskS`), the pointer into the shares, the share (`cskXG`) and the running product
(`cskR`); the returned copy. Every statement holds of it, the assertion because the shares
multiply to `g^o` (`cs_digits`), and the returned eq product is the selector (`cs_sel_prod`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## Reads below `2^4` -/

/-- The word at address `g^a`, or `0`. -/
noncomputable def cskRd (rd : Reader) (a : ℕ) : E := (rd (addressOfIndex a)).getD 0

theorem csk_load {rd : Reader} (hlow : ∀ i < 16, (rd (addressOfIndex i)).isSome) {a : ℕ}
    (ha : a < 16) : LoadHolds rd (gen ^ a) 0 (cskRd rd a) := by
  rw [gen_pow_eq_ofK]
  refine ⟨by simp [IsInK], ?_⟩
  have : (ofK (addressOfIndex a)).limb 0 * addressOfIndex 0 = addressOfIndex a := by
    simp [Parameters.addressOfIndex]
  rw [this]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hlow a ha)
  rw [cskRd, hv]; rfl

/-! ## The digits -/

/-- **An offset's digits**: `o < 2^32`, a multiple of `16^(κ/4)`, is `16^(κ/4)` times the number of
its base-16 digits from `κ / 4` on. -/
theorem cs_digits {κ : ℕ} (hκ : κ < 32) {o : ℕ} (ho : o < 2 ^ 32) (hd : 2 ^ (4 * (κ / 4)) ∣ o) :
    o = 16 ^ (κ / 4) * csDig (fun k ↦ o / 16 ^ (κ / 4 + k) % 16) (csN κ) := by
  have hu : ∀ k < csN κ, o / 16 ^ (κ / 4 + k) % 16 < 16 := fun k _ => Nat.mod_lt _ (by norm_num)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show 16 ^ (κ / 4) = 2 ^ (4 * (κ / 4)) by rw [pow_mul]; norm_num, Nat.testBit_two_pow_mul]
  by_cases hi : i < 4 * (κ / 4)
  · obtain ⟨m, hm⟩ := hd
    rw [hm, Nat.testBit_two_pow_mul]
    simp [show ¬ (4 * (κ / 4) ≤ i) by omega]
  · obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < 4 ∧ i = 4 * (κ / 4) + (4 * k + t) :=
      ⟨(i - 4 * (κ / 4)) / 4, (i - 4 * (κ / 4)) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [show 4 * (κ / 4) + (4 * k + t) - 4 * (κ / 4) = 4 * k + t by omega, testBit_csDig hu k t ht]
    simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and]
    by_cases hk : k < csN κ
    · rw [decide_eq_true hk, Bool.true_and, show (16 : ℕ) = 2 ^ 4 by norm_num,
        Nat.testBit_mod_two_pow, decide_eq_true ht, Bool.true_and, ← pow_mul,
        Nat.testBit_div_two_pow]
      congr 1; ring
    · rw [decide_eq_false hk, Bool.false_and]
      apply Nat.testBit_lt_two_pow
      calc o < 2 ^ 32 := ho
        _ ≤ 2 ^ (4 * (κ / 4) + (4 * k + t)) :=
          Nat.pow_le_pow_right (by norm_num) (by simp only [csN] at hk; omega)

/-! ## The roles -/

/-- Digit `k` of `o`: its base-16 digit `κ / 4 + k`. -/
def cskU (κ o k : ℕ) : ℕ := o / 16 ^ (κ / 4 + k) % 16

/-- Nibble `k`'s eq weight. -/
def cskXE (κ o : ℕ) (p p1 : List E) (k : ℕ) : E :=
  selEqEntry p p1 (κ / 4 + k) (csW κ k - 1) (cskU κ o k)

/-- Nibble `k`'s share. -/
def cskXG (κ o k : ℕ) : E := gen ^ (cskU κ o k * 16 ^ (κ / 4 + k))

/-- The running eq product after nibble `k`. -/
def cskS (κ o : ℕ) (p p1 : List E) (k : ℕ) : E := ∏ m ∈ range (k + 1), cskXE κ o p p1 m

/-- The running `g`-power product after nibble `k`. -/
def cskR (κ o k : ℕ) : E := ∏ m ∈ range (k + 1), cskXG κ o m

/-- Value `s` of nibble `k`. -/
noncomputable def cskRole (κ o : ℕ) (se sg : E) (p p1 : List E) (rd : Reader) (k s : ℕ) : E :=
  if s = 0 then w15 else if s = 1 then gen ^ (15 - cskU κ o k)
  else if s = 2 then cskRd rd (cskU κ o k) else if s = 3 then cskRd rd (15 - cskU κ o k)
  else if s = 4 then se * gen ^ cskU κ o k else if s = 5 then cskXE κ o p p1 k
  else if k = 0 then (if s = 6 then sg * gen ^ cskU κ o k else cskXG κ o k)
  else if s = 6 then cskS κ o p p1 k else if s = 7 then sg * gen ^ cskU κ o k
  else if s = 8 then cskXG κ o k else cskR κ o k

/-- The valuation, by value number. -/
noncomputable def cskVal (κ o : ℕ) (se sg : E) (p p1 : List E) (rd : Reader) (x : ℕ) : E :=
  if x = 0 then gen ^ o else if x = 1 then se else if x = 2 then sg
  else if κ = 32 then word 1 0
  else if x < 3 + csN κ then gen ^ cskU κ o (x - 3)
  else if x < csC κ 1 then cskRole κ o se sg p p1 rd 0 (x - csC κ 0)
  else if x < csC κ (csN κ) then
    cskRole κ o se sg p p1 rd (1 + (x - csC κ 1) / 10) ((x - csC κ 1) % 10)
  else cskS κ o p p1 (csN κ - 1)

section Val

variable {κ o : ℕ} {se sg : E} {p p1 : List E} {rd : Reader}

theorem cskVal_at (hκ : κ < 32) {k s : ℕ} (hk : k < csN κ) (hs : s < if k = 0 then 8 else 10) :
    cskVal κ o se sg p p1 rd (csC κ k + s) = cskRole κ o se sg p p1 rd k s := by
  have hN1 : 1 ≤ csN κ := by unfold csN; omega
  have h32 : κ ≠ 32 := by omega
  have hC0 : csC κ 0 = 3 + csN κ := rfl
  have hC1 : csC κ 1 = 3 + csN κ + 8 := by simp [csC]
  have hCN : csC κ (csN κ) = 3 + csN κ + 8 + 10 * (csN κ - 1) := by
    simp only [csC]; rw [ite_eq_right (by omega)]
  unfold cskVal
  rw [hC1, hCN, ite_eq_right (by unfold csC; split <;> omega),
    ite_eq_right (by unfold csC; split <;> omega), ite_eq_right (by unfold csC; split <;> omega),
    ite_eq_right h32]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte] at hs
    rw [hC0, ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega
  · simp only [hk0, ↓reduceIte] at hs
    have hCk : csC κ k = 3 + csN κ + 8 + 10 * (k - 1) := by simp [csC, hk0]
    rw [hCk, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1 <;> omega

theorem cskVal_digit (hκ : κ < 32) {k : ℕ} (hk : k < csN κ) :
    cskVal κ o se sg p p1 rd (3 + k) = gen ^ cskU κ o k := by
  unfold cskVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]
  congr 2; omega

theorem cskVal_sel (hκ : κ < 32) {k : ℕ} (hk : k < csN κ) :
    cskVal κ o se sg p p1 rd (csSel κ k) = cskS κ o p p1 k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [show csSel κ 0 = csC κ 0 + 5 from rfl, cskVal_at hκ hk (by simp)]
    simp [cskRole, cskS]
  · rw [show csSel κ k = csC κ k + 6 by simp [csSel, hk0], cskVal_at hκ hk (by simp [hk0])]
    simp [cskRole, hk0]

theorem cskVal_rb (hκ : κ < 32) {k : ℕ} (hk : k < csN κ) :
    cskVal κ o se sg p p1 rd (csRb κ k) = cskR κ o k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [show csRb κ 0 = csC κ 0 + 7 from rfl, cskVal_at hκ hk (by simp)]
    simp [cskRole, cskR]
  · rw [show csRb κ k = csC κ k + 9 by simp [csRb, hk0], cskVal_at hκ hk (by simp [hk0])]
    simp [cskRole, hk0]

end Val

theorem csC_ge (κ k : ℕ) : 3 + csN κ ≤ csC κ k := by unfold csC; split <;> omega

theorem csC_one_le {κ : ℕ} (hκ : κ < 32) : csC κ 1 ≤ csC κ (csN κ) := by
  have : 1 ≤ csN κ := by unfold csN; omega
  unfold csC; simp only [one_ne_zero, ↓reduceIte]; split <;> omega

theorem cskVal_last {κ o : ℕ} {se sg : E} {p p1 : List E} {rd : Reader} (hκ : κ < 32) :
    cskVal κ o se sg p p1 rd (csC κ (csN κ)) = cskS κ o p p1 (csN κ - 1) := by
  have hC := csC_ge κ (csN κ)
  have := csC_one_le hκ
  unfold cskVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-! ## The relation -/

theorem csk_rel {κ : ℕ} (hκ : κ < 31) {rd : Reader} {o : ℕ} {se sg : E} {p p1 : List E}
    (ho : o < 2 ^ 32) (hd : 2 ^ κ ∣ o) (hlow : ∀ i < 16, (rd (addressOfIndex i)).isSome)
    (hE : EqTabsAt rd se p p1) (hG : GTabsAt rd sg) :
    coreProgram.Rel rd (lName "column_selector" κ) [gen ^ o, se, sg]
      [cskVal κ o se sg p p1 rd (csRet κ)] := by
  obtain ⟨fn, hf, hfp, hb⟩ := csFound hκ
  set F := cskVal κ o se sg p p1 rd with hF
  have f0 : F 0 = gen ^ o := by simp [hF, cskVal]
  have f1 : F 1 = se := by simp [hF, cskVal]
  have f2 : F 2 = sg := by simp [hF, cskVal]
  refine (tb_rel_pre hf hb (csPre_noRet κ) [gen ^ o, se, sg] _).mpr ⟨fun x ↦ F x.idx,
    by rw [hfp]; simp only [List.map_cons, List.map_nil]; rw [f0, f1, f2], ?_, rfl⟩
  by_cases h32 : κ = 32
  · subst h32
    have ho0 : o = 0 := by
      obtain ⟨q, rfl⟩ := hd
      have : q = 0 := by
        by_contra hq
        have : 2 ^ 32 * 1 ≤ 2 ^ 32 * q := Nat.mul_le_mul_left _ (by omega)
        omega
      simp [this]
    subst ho0
    simp only [csPre, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      true_and]
    have e3 : F 3 = word 1 0 := by simp [hF, cskVal]
    have e4 : F 4 = word 1 0 := by simp [hF, cskVal]
    rw [e3, e4, f0, tb_word_one, pow_zero]
    exact ⟨rfl, e_add_self 1, rfl⟩
  have hκ' : κ < 32 := by omega
  have hdig := cs_digits hκ' ho (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd)
  have hu : ∀ k < csN κ, cskU κ o k < 16 := fun k _ => Nat.mod_lt _ (by norm_num)
  simp only [csPre, h32, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (csNibT_noRet κ)),
    tb_holdsList_flatten_range _ _ (csNibT_noRet κ)]
  have hN1 : 1 ≤ csN κ := by unfold csN; omega
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · -- nibble `k`
    obtain ⟨hw1, hw4⟩ := csW_bounds κ k
    have hj : κ / 4 + k < 8 := by simp only [csN] at hk; omega
    have hdk := cs_dvd hu (by rw [show 16 ^ (κ / 4) * csDig (cskU κ o) (csN κ) = o from hdig.symm]; exact hd) k hk
    have hxe : LoadHolds rd (se * gen ^ cskU κ o k) (64 * (κ / 4 + k) + 16 * (csW κ k - 1))
        (cskXE κ o p p1 k) := by
      rw [tb_loadHolds_mul_gen_pow, show cskU κ o k + (64 * (κ / 4 + k) + 16 * (csW κ k - 1)) =
        64 * (κ / 4 + k) + 16 * (csW κ k - 1) + cskU κ o k by omega]
      exact hE _ hj _ (by omega) _ (hu k hk) hdk
    have hxg : LoadHolds rd (sg * gen ^ cskU κ o k) (16 * (κ / 4 + k)) (cskXG κ o k) := by
      rw [tb_loadHolds_mul_gen_pow, show cskU κ o k + 16 * (κ / 4 + k) =
        16 * (κ / 4 + k) + cskU κ o k by omega]
      exact hG _ hj _ (hu k hk)
    have hrc : LoadHolds rd (gen ^ cskU κ o k) 0 (cskRd rd (cskU κ o k)) ∧
        w15 = gen ^ cskU κ o k * gen ^ (15 - cskU κ o k) ∧
        LoadHolds rd (gen ^ (15 - cskU κ o k)) 0 (cskRd rd (15 - cskU κ o k)) :=
      ⟨csk_load hlow (hu k hk), by
        rw [← pow_add, Nat.add_sub_cancel' (by have := hu k hk; omega), word_g15, gen_pow_eq_ofK],
        csk_load hlow (by omega)⟩
    have e : ∀ s, s < (if k = 0 then 8 else 10) →
        F (csC κ k + s) = cskRole κ o se sg p p1 rd k s := fun s hs => cskVal_at hκ' hk hs
    have ed : F (3 + k) = gen ^ cskU κ o k := cskVal_digit hκ' hk
    unfold csNibT
    by_cases hk0 : k = 0
    · subst hk0
      have e' : ∀ s, s < 8 → F (csC κ 0 + s) = cskRole κ o se sg p p1 rd 0 s :=
        fun s hs => e s (by simpa using hs)
      simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.cons_append,
        List.nil_append]
      have e0 := e' 0 (by norm_num)
      rw [Nat.add_zero] at e0 ed
      rw [e0, e' 1 (by norm_num), e' 2 (by norm_num), e' 3 (by norm_num), e' 4 (by norm_num),
        e' 5 (by norm_num), e' 6 (by norm_num), e' 7 (by norm_num), ed, f1, f2]
      simp only [cskRole, Nat.add_zero, OfNat.ofNat_ne_zero, one_ne_zero, ↓reduceIte,
        show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
        show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 1 by omega, show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 1 by omega, show (6 : ℕ) ≠ 2 by omega,
        show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 5 by omega,
        show (7 : ℕ) ≠ 1 by omega, show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega,
        show (7 : ℕ) ≠ 4 by omega, show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega]
      exact ⟨trivial, hrc, trivial, hxe, trivial, hxg⟩
    · have e' : ∀ s, s < 10 → F (csC κ k + s) = cskRole κ o se sg p p1 rd k s :=
        fun s hs => e s (by simpa [hk0] using hs)
      have eS : F (csSel κ (k - 1)) = cskS κ o p p1 (k - 1) := cskVal_sel hκ' (by omega)
      have eR : F (csRb κ (k - 1)) = cskR κ o (k - 1) := cskVal_rb hκ' (by omega)
      simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
        List.cons_append, List.nil_append]
      have e0 := e' 0 (by norm_num)
      rw [Nat.add_zero] at e0
      rw [e0, e' 1 (by norm_num), e' 2 (by norm_num), e' 3 (by norm_num), e' 4 (by norm_num),
        e' 5 (by norm_num), e' 6 (by norm_num), e' 7 (by norm_num), e' 8 (by norm_num),
        e' 9 (by norm_num), ed, f1, f2, eS, eR]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [cskRole, hk0, ↓reduceIte, Nat.add_sub_cancel, cskS, cskR, prod_range_succ _ (k' + 1),
        OfNat.ofNat_ne_zero, one_ne_zero,
        show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
        show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 1 by omega, show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 1 by omega, show (6 : ℕ) ≠ 2 by omega,
        show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 5 by omega,
        show (7 : ℕ) ≠ 1 by omega, show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega,
        show (7 : ℕ) ≠ 4 by omega, show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega,
        show (8 : ℕ) ≠ 1 by omega, show (8 : ℕ) ≠ 2 by omega, show (8 : ℕ) ≠ 3 by omega,
        show (8 : ℕ) ≠ 4 by omega, show (8 : ℕ) ≠ 5 by omega, show (8 : ℕ) ≠ 6 by omega,
        show (8 : ℕ) ≠ 7 by omega, show (9 : ℕ) ≠ 1 by omega, show (9 : ℕ) ≠ 2 by omega,
        show (9 : ℕ) ≠ 3 by omega, show (9 : ℕ) ≠ 4 by omega, show (9 : ℕ) ≠ 5 by omega,
        show (9 : ℕ) ≠ 6 by omega, show (9 : ℕ) ≠ 7 by omega, show (9 : ℕ) ≠ 8 by omega]
      exact ⟨trivial, hrc, trivial, hxe, trivial, trivial, hxg, trivial⟩
  · -- the assertion and the copy
    have eS : F (csSel κ (csN κ - 1)) = cskS κ o p p1 (csN κ - 1) := cskVal_sel hκ' (by omega)
    have eR : F (csRb κ (csN κ - 1)) = cskR κ o (csN κ - 1) := cskVal_rb hκ' (by omega)
    have hC := csC_ge κ (csN κ)
    have eC : F (csC κ (csN κ)) = cskS κ o p p1 (csN κ - 1) := cskVal_last hκ'
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [eS, eR, eC, f0]
    refine ⟨?_, rfl⟩
    rw [cskR, show csN κ - 1 + 1 = csN κ by omega,
      prod_congr rfl (fun m _ => show cskXG κ o m = gen ^ (cskU κ o m * 16 ^ (κ / 4 + m)) from rfl),
      prod_gen_pow_csDig, show 16 ^ (κ / 4) * csDig (cskU κ o) (csN κ) = o from hdig.symm]
    exact e_add_self _

/-- **`column_selector` is complete** at its 33 specializations. -/
theorem column_selector_complete_holds : column_selector_complete_Spec := by
  intro κ hκ rd o se sg p p1 ho hd hp hp1 hlow hE hG
  have hR := csk_rel hκ ho hd hlow hE hG
  by_cases h32 : κ = 32
  · subst h32
    have ho0 : o = 0 := by
      obtain ⟨q, rfl⟩ := hd
      have : q = 0 := by
        by_contra hq
        have : 2 ^ 32 * 1 ≤ 2 ^ 32 * q := Nat.mul_le_mul_left _ (by omega)
        omega
      simp [this]
    subst ho0
    have : cskVal 32 0 se sg p p1 rd (csRet 32) = 1 := by simp [cskVal, csRet, tb_word_one]
    rw [this] at hR
    simpa [bitsEq] using hR
  have hκ' : κ < 32 := by omega
  have hdig := cs_digits hκ' ho (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd)
  have hret : cskVal κ o se sg p p1 rd (csRet κ) = cskS κ o p p1 (csN κ - 1) := by
    simp only [csRet, h32, ↓reduceIte]; exact cskVal_last hκ'
  rw [hret, cskS, show csN κ - 1 + 1 = csN κ by unfold csN; omega] at hR
  have hsel := cs_sel_prod hκ' (u := cskU κ o) (fun k _ => Nat.mod_lt _ (by norm_num)) hp hp1
  rw [show (fun m ↦ cskXE κ o p p1 m) = fun k ↦ selEqEntry p p1 (κ / 4 + k) (csW κ k - 1)
    (cskU κ o k) from rfl] at hR
  rw [hsel, show 16 ^ (κ / 4) * csDig (cskU κ o) (csN κ) = o from hdig.symm] at hR
  exact hR

end
end LeanVM.Guest.B1.Tables
