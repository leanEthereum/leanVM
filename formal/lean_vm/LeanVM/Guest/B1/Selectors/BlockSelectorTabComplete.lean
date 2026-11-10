/-
  LeanVM.Guest.B1.Selectors.BlockSelectorTabComplete

  `block_selector_tab` is complete: for `n < 34` bits whose nibbles' `g`-power digits are in
  memory, the memory defined below `2^4` (the digits' range checks) and a run's nibble tables in
  memory, their eq weight and `g`-power product are an outcome of `block_selector_tab__L{n}`.
-/

module

public import LeanVM.Guest.B1.Selectors.BlockSelectorTab
public import LeanVM.Guest.B1.Selectors.ColumnSelectorComplete

/-!
# `block_selector_tab` is complete (TRIAGE G #49)

The valuation `btkVal` gives every value of `block_selector_tab__L{n}`'s body its role
(`btkRole`): in nibble `k`, the digit `g^u` (`u = btkU`, the nibble's bits), the range check's
bound `g^(2^w - 1)`, its cofactor `g^(2^w - 1 - u)` and the two words it reads (the memory is
defined below `2^4`), the pointer into the eq table, the eq weight (`btkXE`), the running eq
product (`btkS`), the pointer into the `g` table, the share (`btkXG`) and the running `g`-power
product (`btkR`); the two returned copies. Every statement holds of it: the digits by the digits in
memory, the weights and shares by the tables in memory, the rest by its definition; the returned
products are the bits' eq weight and `g`-power product (`bt_reindex`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The roles -/

/-- Bit `t` of nibble `k`. -/
def btkB (bs : List Bool) (k t : ℕ) : Bool := bs.getD (4 * k + t) false

/-- Nibble `k`'s digit's exponent: its bits. -/
def btkU (n : ℕ) (bs : List Bool) (k : ℕ) : ℕ := bitsVal (btkB bs k) (btW n k)

/-- Nibble `k`'s eq weight. -/
def btkXE (n : ℕ) (bs : List Bool) (zs zs1 : List E) (k : ℕ) : E :=
  (eqLevels (nib zs k) (nib zs1 k)).getD (2 ^ btW n k - 2 + btkU n bs k) 0

/-- Nibble `k`'s share. -/
def btkXG (n : ℕ) (bs : List Bool) (gs : List E) (k : ℕ) : E :=
  (gTable (nib gs k)).getD (btkU n bs k) 0

/-- The running eq product after nibble `k`. -/
def btkS (n : ℕ) (bs : List Bool) (zs zs1 : List E) (k : ℕ) : E :=
  ∏ m ∈ range (k + 1), btkXE n bs zs zs1 m

/-- The running `g`-power product after nibble `k`. -/
def btkR (n : ℕ) (bs : List Bool) (gs : List E) (k : ℕ) : E :=
  ∏ m ∈ range (k + 1), btkXG n bs gs m

/-- Value `s` of nibble `k`. -/
noncomputable def btkRole (n : ℕ) (eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    (rd : Reader) (k s : ℕ) : E :=
  if s = 0 then gen ^ btkU n bs k else if s = 1 then word (2 ^ (2 ^ btW n k - 1)) 0
  else if s = 2 then gen ^ (2 ^ btW n k - 1 - btkU n bs k)
  else if s = 3 then cskRd rd (btkU n bs k)
  else if s = 4 then cskRd rd (2 ^ btW n k - 1 - btkU n bs k)
  else if s = 5 then eqt * gen ^ btkU n bs k else if s = 6 then btkXE n bs zs zs1 k
  else if k = 0 then (if s = 7 then gt * gen ^ btkU n bs k else btkXG n bs gs k)
  else if s = 7 then btkS n bs zs zs1 k else if s = 8 then gt * gen ^ btkU n bs k
  else if s = 9 then btkXG n bs gs k else btkR n bs gs k

/-- **Value `x` of `block_selector_tab__L{n}`.** -/
noncomputable def btkVal (n : ℕ) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    (rd : Reader) (x : ℕ) : E :=
  if x = 0 then sb else if x = 1 then eqt else if x = 2 then gt
  else if n = 0 then word 1 0
  else if x < 12 then btkRole n eqt gt bs zs zs1 gs rd 0 (x - 3)
  else if x < btC (btN n) then btkRole n eqt gt bs zs zs1 gs rd (1 + (x - 12) / 11) ((x - 12) % 11)
  else if x = btC (btN n) then btkS n bs zs zs1 (btN n - 1)
  else btkR n bs gs (btN n - 1)

section Val

variable {n : ℕ} {sb eqt gt : E} {bs : List Bool} {zs zs1 gs : List E} {rd : Reader}

theorem btC_succ (k : ℕ) : btC (k + 1) = 12 + 11 * k := by simp [btC]

theorem btC_last {n : ℕ} (hn : n ≠ 0) : btC (btN n) = 12 + 11 * (btN n - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, btN n = m + 1 := ⟨btN n - 1, by unfold btN; omega⟩
  rw [hm, btC_succ, Nat.add_sub_cancel]

theorem btkVal_at (hn : n ≠ 0) {k s : ℕ} (hk : k < btN n) (hs : s < if k = 0 then 9 else 11) :
    btkVal n sb eqt gt bs zs zs1 gs rd (btC k + s) = btkRole n eqt gt bs zs zs1 gs rd k s := by
  have hCN := btC_last hn
  unfold btkVal
  rw [hCN]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte] at hs
    rw [show btC 0 = 3 from rfl, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right hn, ite_eq_left (by omega)]
    congr 1; omega
  · simp only [hk0, ↓reduceIte] at hs
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [btC_succ, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right hn, ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1 <;> omega

theorem btkVal_sel (hn : n ≠ 0) {k : ℕ} (hk : k < btN n) :
    btkVal n sb eqt gt bs zs zs1 gs rd (btSel k) = btkS n bs zs zs1 k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [show btSel 0 = btC 0 + 6 from rfl, btkVal_at hn hk (by simp)]
    simp [btkRole, btkS]
  · rw [show btSel k = btC k + 7 by simp [btSel, hk0], btkVal_at hn hk (by simp [hk0])]
    simp [btkRole, hk0]

theorem btkVal_rb (hn : n ≠ 0) {k : ℕ} (hk : k < btN n) :
    btkVal n sb eqt gt bs zs zs1 gs rd (btRb k) = btkR n bs gs k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [show btRb 0 = btC 0 + 8 from rfl, btkVal_at hn hk (by simp)]
    simp [btkRole, btkR]
  · rw [show btRb k = btC k + 10 by simp [btRb, hk0], btkVal_at hn hk (by simp [hk0])]
    simp [btkRole, hk0]

theorem btkVal_last (hn : n ≠ 0) :
    btkVal n sb eqt gt bs zs zs1 gs rd (btC (btN n)) = btkS n bs zs zs1 (btN n - 1) := by
  have hCN := btC_last hn
  unfold btkVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hn,
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem btkVal_last1 (hn : n ≠ 0) :
    btkVal n sb eqt gt bs zs zs1 gs rd (btC (btN n) + 1) = btkR n bs gs (btN n - 1) := by
  have hCN := btC_last hn
  unfold btkVal
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hn,
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end Val

/-! ## The digits, the weights and the shares -/

/-- Bits past a width that are clear leave `bitsVal` alone. -/
theorem bitsVal_clear {f : ℕ → Bool} {w : ℕ} : ∀ {m : ℕ}, w ≤ m →
    (∀ t, w ≤ t → t < m → f t = false) → bitsVal f m = bitsVal f w
  | 0, hw, _ => by rw [show w = 0 by omega]
  | m + 1, hw, h => by
    by_cases hwm : w = m + 1
    · rw [hwm]
    · rw [bitsVal, bitsVal_clear (m := m) (by omega) fun t h1 h2 => h t h1 (by omega),
        h m (by omega) (by omega)]
      simp

theorem btkU_lt (n : ℕ) (bs : List Bool) (k : ℕ) : btkU n bs k < 2 ^ btW n k :=
  bitsVal_lt _ _

/-- **The digit in memory** is `g^u`, `u` the nibble's bits. -/
theorem btk_digit {bs : List Bool} {n : ℕ} (hbl : bs.length = n) {k : ℕ} (hk : k < btN n) :
    (nibDigits bs).getD k 0 = gen ^ btkU n bs k := by
  have hk' : k < (nibDigits bs).length := by simpa [nibDigits, hbl, btN] using hk
  rw [List.getD_eq_getElem _ _ hk']
  simp only [nibDigits, List.getElem_map, List.getElem_range]
  congr 1
  unfold btkU
  rw [← bitsVal_clear (m := 4) (btW_le n k) fun t ht ht4 => ?_]
  · rfl
  · show bs.getD (4 * k + t) false = false
    rw [List.getD_eq_default _ _ (by unfold btW at ht; split at ht <;> omega)]

/-- Nibble `k`'s eq weight in memory, at its digit. -/
theorem btk_xeLoad {rd : Reader} {eqt gt : E} {n : ℕ} {zs zs1 gs : List E} (bs : List Bool)
    (hzl : zs.length = n) (hz1l : zs1.length = n) (hrt : RunTables rd eqt gt n zs zs1 gs)
    {k : ℕ} (hk : k < btN n) :
    LoadHolds rd (eqt * gen ^ btkU n bs k) (32 * k + 2 ^ btW n k - 2) (btkXE n bs zs zs1 k) := by
  have hw1 := btW_pos hk
  have hlen := nib_length hzl hk
  have hlen1 := nib_length hz1l hk
  have hU := btkU_lt n bs k
  have h2 := two_le_two_pow hw1
  have hl : 2 ^ btW n k - 2 + btkU n bs k < (eqLevels (nib zs k) (nib zs1 k)).length := by
    rw [eqLevels_length hlen hlen1, pow_succ]; omega
  have h1 := tbReadsAt_getD ((hrt k (by simpa [btN] using hk)).1) hl
  rw [tb_loadHolds_mul_gen_pow] at h1
  rw [tb_loadHolds_mul_gen_pow,
    show btkU n bs k + (32 * k + 2 ^ btW n k - 2) = 32 * k + (2 ^ btW n k - 2 + btkU n bs k) by
      omega]
  exact h1

/-- Nibble `k`'s share in memory, at its digit. -/
theorem btk_xgLoad {rd : Reader} {eqt gt : E} {n : ℕ} {zs zs1 gs : List E} (bs : List Bool)
    (hgl : gs.length = n) (hrt : RunTables rd eqt gt n zs zs1 gs) {k : ℕ} (hk : k < btN n) :
    LoadHolds rd (gt * gen ^ btkU n bs k) (16 * k) (btkXG n bs gs k) := by
  have hlen := nib_length hgl hk
  have hl : btkU n bs k < (gTable (nib gs k)).length := by
    rw [gTable_length hlen]; exact btkU_lt n bs k
  have h1 := tbReadsAt_getD ((hrt k (by simpa [btN] using hk)).2) hl
  rw [tb_loadHolds_mul_gen_pow] at h1
  rw [tb_loadHolds_mul_gen_pow, add_comm]
  exact h1

/-- Nibble `k`'s eq weight, as a product. -/
theorem btkXE_prod {n : ℕ} {zs zs1 : List E} (bs : List Bool) (hzl : zs.length = n)
    (hz1l : zs1.length = n) {k : ℕ} (hk : k < btN n) :
    btkXE n bs zs zs1 k = ∏ t ∈ range (btW n k),
      (if bs.getD (4 * k + t) false then zs.getD (4 * k + t) 0 else zs1.getD (4 * k + t) 0) := by
  have hw1 := btW_pos hk
  have hlen := nib_length hzl hk
  have hlen1 := nib_length hz1l hk
  rw [btkXE, btkU, eqLevels_getD (hlen.trans hlen1.symm) hw1 (by omega) (bitsVal_lt _ _)]
  refine prod_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  rw [bitPick, testBit_bitsVal, nib_getD ht', nib_getD ht']
  simp [ht', btkB]

/-- Nibble `k`'s share, as a product. -/
theorem btkXG_prod {n : ℕ} {gs : List E} (bs : List Bool) (hgl : gs.length = n) {k : ℕ}
    (hk : k < btN n) :
    btkXG n bs gs k = ∏ t ∈ range (btW n k),
      (if bs.getD (4 * k + t) false then gs.getD (4 * k + t) 0 else 1) := by
  have hlen := nib_length hgl hk
  rw [btkXG, btkU, gTable_getD hlen (bitsVal_lt _ _)]
  refine prod_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  rw [bitPick, testBit_bitsVal, nib_getD ht']
  simp [ht', btkB]

/-- **The returned products** are the bits' eq weight and `g`-power product. -/
theorem btk_products {n : ℕ} (hn : n ≠ 0) {bs : List Bool} {zs zs1 gs : List E}
    (hbl : bs.length = n) (hzl : zs.length = n) (hz1l : zs1.length = n) (hgl : gs.length = n) :
    btkS n bs zs zs1 (btN n - 1) = bitsEq bs zs zs1 ∧ btkR n bs gs (btN n - 1) = bitsPow bs gs := by
  have hN : btN n - 1 + 1 = btN n := by unfold btN; omega
  rw [btkS, btkR, hN, bitsEq_eq_prod (m := n) hbl hzl hz1l, bitsPow_eq_prod (m := n) hbl hgl,
    ← bt_reindex (fun i ↦ if bs.getD i false then zs.getD i 0 else zs1.getD i 0) n,
    ← bt_reindex (fun i ↦ if bs.getD i false then gs.getD i 0 else 1) n]
  exact ⟨prod_congr rfl fun k hk ↦ btkXE_prod bs hzl hz1l (mem_range.mp hk),
    prod_congr rfl fun k hk ↦ btkXG_prod bs hgl (mem_range.mp hk)⟩

/-! ## The relation -/

/-- **`block_selector_tab` is complete** at its 34 specializations. -/
theorem block_selector_tab_complete_holds : block_selector_tab_complete_Spec := by
  intro n hn rd sb eqt gt bs zs zs1 gs hbl hzl hz1l hgl hbr hlow hrt
  obtain ⟨fn, hf, hp, hb⟩ := btFound hn
  set F := btkVal n sb eqt gt bs zs zs1 gs rd with hF
  have f0 : F 0 = sb := by simp [hF, btkVal]
  have f1 : F 1 = eqt := by simp [hF, btkVal]
  have f2 : F 2 = gt := by simp [hF, btkVal]
  refine (tb_rel_pre hf hb (btPre_noRet n) [sb, eqt, gt] _).mpr ⟨fun x ↦ F x.idx,
    by rw [hp]; simp only [List.map_cons, List.map_nil]; rw [f0, f1, f2], ?_, ?_⟩
  · by_cases h0 : n = 0
    · subst h0
      simp only [btPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      simp [hF, btkVal]
    simp only [btPre, h0, ↓reduceIte]
    rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
      tb_holdsList_flatten_range _ _ (btNibT_noRet n)]
    refine ⟨fun k hk ↦ ?_, ?_⟩
    · -- nibble `k`
      have hw1 := btW_pos hk
      have hw4 := btW_le n k
      have hU := btkU_lt n bs k
      have hW16 : 2 ^ btW n k ≤ 16 := by
        calc 2 ^ btW n k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hw4
          _ = 16 := by norm_num
      have hdig : LoadHolds rd sb k (gen ^ btkU n bs k) := by
        have h := tbReadsAt_getD hbr (k := k) (by simpa [nibDigits, hbl, btN] using hk)
        rwa [btk_digit hbl hk] at h
      have hrc : LoadHolds rd (gen ^ btkU n bs k) 0 (cskRd rd (btkU n bs k)) ∧
          word (2 ^ (2 ^ btW n k - 1)) 0 =
            gen ^ btkU n bs k * gen ^ (2 ^ btW n k - 1 - btkU n bs k) ∧
          LoadHolds rd (gen ^ (2 ^ btW n k - 1 - btkU n bs k)) 0
            (cskRd rd (2 ^ btW n k - 1 - btkU n bs k)) :=
        ⟨csk_load hlow (by omega), by
          rw [← pow_add, Nat.add_sub_cancel' (by omega), tb_word_two_pow (by omega)],
          csk_load hlow (by omega)⟩
      have hxe := btk_xeLoad bs hzl hz1l hrt hk
      have hxg := btk_xgLoad bs hgl hrt hk
      have e : ∀ s, s < (if k = 0 then 9 else 11) →
          F (btC k + s) = btkRole n eqt gt bs zs zs1 gs rd k s := fun s hs => btkVal_at h0 hk hs
      unfold btNibT
      by_cases hk0 : k = 0
      · subst hk0
        have e' : ∀ s, s < 9 → F (btC 0 + s) = btkRole n eqt gt bs zs zs1 gs rd 0 s :=
          fun s hs => e s (by simpa using hs)
        simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.cons_append,
          List.nil_append]
        have e0 := e' 0 (by norm_num)
        rw [Nat.add_zero] at e0
        rw [e0, e' 1 (by norm_num), e' 2 (by norm_num), e' 3 (by norm_num), e' 4 (by norm_num),
          e' 5 (by norm_num), e' 6 (by norm_num), e' 7 (by norm_num), e' 8 (by norm_num), f0, f1,
          f2]
        simp only [btkRole, OfNat.ofNat_ne_zero, one_ne_zero, ↓reduceIte,
          show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
          show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega,
          show (5 : ℕ) ≠ 1 by omega, show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega,
          show (5 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 1 by omega, show (6 : ℕ) ≠ 2 by omega,
          show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 5 by omega,
          show (7 : ℕ) ≠ 1 by omega, show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega,
          show (7 : ℕ) ≠ 4 by omega, show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega,
          show (8 : ℕ) ≠ 1 by omega, show (8 : ℕ) ≠ 2 by omega, show (8 : ℕ) ≠ 3 by omega,
          show (8 : ℕ) ≠ 4 by omega, show (8 : ℕ) ≠ 5 by omega, show (8 : ℕ) ≠ 6 by omega,
          show (8 : ℕ) ≠ 7 by omega]
        exact ⟨hdig, trivial, hrc, trivial, hxe, trivial, hxg⟩
      · have e' : ∀ s, s < 11 → F (btC k + s) = btkRole n eqt gt bs zs zs1 gs rd k s :=
          fun s hs => e s (by simpa [hk0] using hs)
        have eS : F (btSel (k - 1)) = btkS n bs zs zs1 (k - 1) := btkVal_sel h0 (by omega)
        have eR : F (btRb (k - 1)) = btkR n bs gs (k - 1) := btkVal_rb h0 (by omega)
        simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
          List.cons_append, List.nil_append]
        have e0 := e' 0 (by norm_num)
        rw [Nat.add_zero] at e0
        rw [e0, e' 1 (by norm_num), e' 2 (by norm_num), e' 3 (by norm_num), e' 4 (by norm_num),
          e' 5 (by norm_num), e' 6 (by norm_num), e' 7 (by norm_num), e' 8 (by norm_num),
          e' 9 (by norm_num), e' 10 (by norm_num), f0, f1, f2, eS, eR]
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [btkRole, hk0, ↓reduceIte, Nat.add_sub_cancel, btkS, btkR,
          prod_range_succ _ (k' + 1), OfNat.ofNat_ne_zero, one_ne_zero,
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
          show (9 : ℕ) ≠ 6 by omega, show (9 : ℕ) ≠ 7 by omega, show (9 : ℕ) ≠ 8 by omega,
          show (10 : ℕ) ≠ 1 by omega, show (10 : ℕ) ≠ 2 by omega, show (10 : ℕ) ≠ 3 by omega,
          show (10 : ℕ) ≠ 4 by omega, show (10 : ℕ) ≠ 5 by omega, show (10 : ℕ) ≠ 6 by omega,
          show (10 : ℕ) ≠ 7 by omega, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega]
        exact ⟨hdig, trivial, hrc, trivial, hxe, trivial, trivial, hxg, trivial⟩
    · -- the copies
      have hN : 1 ≤ btN n := by simp only [btN]; omega
      have eS : F (btSel (btN n - 1)) = btkS n bs zs zs1 (btN n - 1) := btkVal_sel h0 (by omega)
      have eR : F (btRb (btN n - 1)) = btkR n bs gs (btN n - 1) := btkVal_rb h0 (by omega)
      have v1 : F (btC (btN n)) = btkS n bs zs zs1 (btN n - 1) := btkVal_last h0
      have v2 : F (btC (btN n) + 1) = btkR n bs gs (btN n - 1) := btkVal_last1 h0
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [eS, eR, v1, v2]
      exact ⟨rfl, rfl⟩
  · -- the returns
    by_cases h0 : n = 0
    · subst h0
      obtain rfl := List.length_eq_zero_iff.mp hbl
      obtain rfl := List.length_eq_zero_iff.mp hzl
      obtain rfl := List.length_eq_zero_iff.mp hz1l
      obtain rfl := List.length_eq_zero_iff.mp hgl
      simp [btRet, hF, btkVal, bitsEq, bitsPow, tb_word_one]
    · simp only [btRet, h0, ↓reduceIte, List.map_cons, List.map_nil]
      show [F (btC (btN n)), F (btC (btN n) + 1)] = _
      obtain ⟨h1, h2⟩ := btk_products h0 hbl hzl hz1l hgl
      have v1 : F (btC (btN n)) = btkS n bs zs zs1 (btN n - 1) := btkVal_last h0
      have v2 : F (btC (btN n) + 1) = btkR n bs gs (btN n - 1) := btkVal_last1 h0
      rw [v1, v2, h1, h2]

end
end LeanVM.Guest.B1.Tables
