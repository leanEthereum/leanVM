/-
  LeanVM.Guest.B1.Selectors.BlockSelectorTab

  B1 for `block_selector_tab`: its 34 specializations read range-checked `g`-power digits and,
  off the shared nibble tables, return their bits' eq weight and `g`-power product.
-/

module

public import LeanVM.Guest.B1.Selectors.SelPartial

/-!
# `block_selector_tab` (TRIAGE G #49)

`block_selector_tab(digits, eq_tab, g_tab, n)` (G:2143-2162) reads, for each nibble `j` of the
`n` bits (the last `n - 4j` wide, `w`), its hinted digit `d = g^u` at `digits`, range-checks
`u < 2^w` (`assert_digit`, G:2130-2140), and multiplies the eq weight at `eq_tab·g^u` (offset
`32j + 2^w - 2`) and the share at `g_tab·g^u` (offset `16j`). The bits are the digits' (`u`'s bit
`t` the bit `4j + t`): the caller pins their `g`-power product to a certified offset.

The body of `block_selector_tab__L{n}` is `btPre n` (`btFound`, by kernel evaluation): nibble `k`
from value `btC k` (`btNibT`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The number of nibbles of `n` bits. -/
def btN (n : ℕ) : ℕ := (n + 3) / 4

/-- The width of nibble `k`. -/
def btW (n k : ℕ) : ℕ := if 4 * k + 4 ≤ n then 4 else n - 4 * k

/-- The first value of nibble `k`: its digit. -/
def btC (k : ℕ) : ℕ := if k = 0 then 3 else 12 + 11 * (k - 1)

/-- The eq product after nibble `k`. -/
def btSel (k : ℕ) : ℕ := if k = 0 then btC 0 + 6 else btC k + 7

/-- The rebuilt product after nibble `k`. -/
def btRb (k : ℕ) : ℕ := if k = 0 then btC 0 + 8 else btC k + 10

/-- Nibble `k` of `block_selector_tab__L{n}`: the digit, its range check against `g^(2^w - 1)`,
the eq weight at `eq_tab·g^u`, the share at `g_tab·g^u`, the running products. -/
def btNibT (n k : ℕ) : List Stmt :=
  let w := btW n k
  let c := btC k
  [.atom (.load (.n c) (.n 0) k), .atom (.const (.n (c + 1)) (word (2 ^ (2 ^ w - 1)) 0)),
    .atom (.rangeCheck (.n c) (.n (c + 2)) (.n (c + 3)) (.n (c + 4)) (.n (c + 1))),
    .atom (.mul (.n (c + 5)) (.n 1) (.n c)),
    .atom (.load (.n (c + 6)) (.n (c + 5)) (32 * k + 2 ^ w - 2))] ++
  if k = 0 then
    [.atom (.mul (.n (c + 7)) (.n 2) (.n c)), .atom (.load (.n (c + 8)) (.n (c + 7)) (16 * k))]
  else
    [.atom (.mul (.n (c + 7)) (.n (btSel (k - 1))) (.n (c + 6))),
      .atom (.mul (.n (c + 8)) (.n 2) (.n c)), .atom (.load (.n (c + 9)) (.n (c + 8)) (16 * k)),
      .atom (.mul (.n (c + 10)) (.n (btRb (k - 1))) (.n (c + 9)))]

/-- `block_selector_tab__L{n}`'s statements before its `ret`. -/
def btPre (n : ℕ) : List Stmt :=
  if n = 0 then [.atom (.const (.n 3) (word 1 0)), .atom (.const (.n 4) (word 1 0))]
  else ((List.range (btN n)).map (btNibT n)).flatten ++
    [.atom (.copy (.n (btC (btN n))) (.n (btSel (btN n - 1)))),
      .atom (.copy (.n (btC (btN n) + 1)) (.n (btRb (btN n - 1))))]

/-- The values `block_selector_tab__L{n}` returns. -/
def btRet (n : ℕ) : List V :=
  if n = 0 then [.n 3, .n 4] else [.n (btC (btN n)), .n (btC (btN n) + 1)]

/-- The function found by name is the template. -/
noncomputable def btCheck (n : ℕ) : Bool :=
  match coreProgram.find? (lName "block_selector_tab" n) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      tbStmtsEqb fn.body (btPre n ++ [.ret (btRet n)])
  | none => false

theorem btCheck_all : (List.range 34).all btCheck = true := by decide +kernel

theorem btFound {n : ℕ} (hn : n < 34) : ∃ fn : Fn,
    coreProgram.find? (lName "block_selector_tab" n) = some fn ∧ fn.params = [.n 0, .n 1, .n 2] ∧
      fn.body = btPre n ++ [.ret (btRet n)] := by
  have h := List.all_eq_true.mp btCheck_all n (List.mem_range.mpr hn)
  unfold btCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem btNibT_noRet (n k : ℕ) : Stmt.noRetList (btNibT n k) = true := by
  unfold btNibT; split <;> rfl

theorem btPre_noRet (n : ℕ) : Stmt.noRetList (btPre n) = true := by
  unfold btPre
  split
  · rfl
  · rw [tb_noRetList_append, tb_noRetList_flatten_range _ _ (btNibT_noRet n)]; rfl

theorem btW_le (n k : ℕ) : btW n k ≤ 4 := by unfold btW; split <;> omega

theorem btW_pos {n k : ℕ} (hk : k < btN n) : 1 ≤ btW n k := by
  unfold btW btN at *; split <;> omega

/-- `g^(2^w - 1)`, the range check of a `w`-bit digit. -/
theorem word_digit_bound {w : ℕ} (hw : w ≤ 4) :
    word (2 ^ (2 ^ w - 1)) 0 = ofK (Parameters.addressOfIndex (2 ^ w - 1)) := by
  rw [tb_word_two_pow (by have : 2 ^ w ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hw; omega),
    gen_pow_eq_ofK]

section Sem

variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
variable {C : CallRel} {σ : Val} {kret : List E → Prop}

include hμ in
/-- **A nibble**: its digit `g^u` read at `digits`, `u < 2^w`; the eq weight and the share it
reads, at `g^u` past the tables' offsets; the running products. -/
theorem holds_btNib {n k : ℕ} (hk : k < btN n)
    (h : Stmt.HoldsList C Lm.read σ (btNibT n k) True kret) :
    ∃ u < 2 ^ btW n k, LoadHolds Lm.read (σ (.n 0)) k (gen ^ u) ∧
      ∃ xe xg, LoadHolds Lm.read (σ (.n 1)) (u + (32 * k + 2 ^ btW n k - 2)) xe ∧
        LoadHolds Lm.read (σ (.n 2)) (u + 16 * k) xg ∧
        σ (.n (btSel k)) = (if k = 0 then 1 else σ (.n (btSel (k - 1)))) * xe ∧
        σ (.n (btRb k)) = (if k = 0 then 1 else σ (.n (btRb (k - 1)))) * xg := by
  have hw1 := btW_pos hk
  have hw4 := btW_le n k
  unfold btNibT at h
  rw [tb_holdsList_append_noRet rfl] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  obtain ⟨hld, hc, ⟨r1, r2, r3⟩, hm, hl⟩ := h1
  have hK : 2 ≤ 2 ^ btW n k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ btW n k := Nat.pow_le_pow_right (by norm_num) hw1
  obtain ⟨u, hu, hd⟩ := tb_rc_sound' hμ Lm (K := 2 ^ btW n k) (by omega)
    (by have : 2 ^ btW n k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hw4; omega)
    (by rw [hc, word_digit_bound hw4]) r1 r2 r3
  refine ⟨u, hu, hd ▸ hld, ?_⟩
  rw [hm, hd, tb_loadHolds_mul_gen_pow] at hl
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h2
    obtain ⟨hm2, hl2⟩ := h2
    rw [hm2, hd, tb_loadHolds_mul_gen_pow] at hl2
    refine ⟨_, _, hl, hl2, ?_, ?_⟩ <;> simp [btSel, btRb]
  · simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h2
    obtain ⟨hs, hm2, hl2, hr⟩ := h2
    rw [hm2, hd, tb_loadHolds_mul_gen_pow] at hl2
    exact ⟨_, _, hl, hl2, by simp only [btSel, hk0, ↓reduceIte]; exact hs,
      by simp only [btRb, hk0, ↓reduceIte]; exact hr⟩

end Sem

/-! ## Products over the nibbles -/

/-- **The nibbles cover the bits `0 .. n - 1`**: nibble `k`'s bits `4k + t`, `t < w_k`. -/
theorem bt_reindex {M : Type} [CommMonoid M] (F : ℕ → M) (n : ℕ) :
    ∏ k ∈ Finset.range (btN n), ∏ t ∈ Finset.range (btW n k), F (4 * k + t) =
      ∏ i ∈ Finset.range n, F i := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by decide),
    (Nat.div_add_mod n 4).symm⟩
  have hfull : ∏ k ∈ Finset.range q, ∏ t ∈ Finset.range (btW (4 * q + r) k), F (4 * k + t) =
      ∏ i ∈ Finset.range (4 * q), F i := by
    have h4 := prod_range_four_blocks F 0 q
    simp only [Nat.zero_add] at h4
    rw [← h4]
    refine Finset.prod_congr rfl fun k hk => ?_
    have := Finset.mem_range.mp hk
    rw [show btW (4 * q + r) k = 4 by simp only [btW]; split <;> omega]

  rw [Finset.prod_range_add]
  by_cases hr0 : r = 0
  · subst hr0
    rw [show btN (4 * q + 0) = q by simp only [btN]; omega, hfull, Finset.prod_range_zero, mul_one]
  · rw [show btN (4 * q + r) = q + 1 by simp only [btN]; omega, Finset.prod_range_succ, hfull,
      show btW (4 * q + r) q = r by simp only [btW]; split <;> omega]

/-- `bitsPow` as a product over the positions. -/
theorem bitsPow_eq_prod : ∀ {m : ℕ} {bs : List Bool} {gs : List E}, bs.length = m →
    gs.length = m → bitsPow bs gs = ∏ i ∈ Finset.range m, (if bs.getD i false then gs.getD i 0 else 1)
  | 0, bs, gs, h1, _ => by rw [List.length_eq_zero_iff] at h1; subst h1; rfl
  | m + 1, b :: bs, g :: gs, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    rw [bitsPow, List.zip_cons_cons, List.map_cons, List.prod_cons, ← bitsPow,
      bitsPow_eq_prod h1 h2, Finset.prod_range_succ', mul_comm]
    simp

theorem nib_getD {l : List E} {n k t : ℕ} (ht : t < btW n k) :
    (nib l k).getD t 0 = l.getD (4 * k + t) 0 := by
  rw [nib, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by unfold btW at ht; split at ht <;> omega),
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem nib_length {l : List E} {n k : ℕ} (hl : l.length = n) (hk : k < btN n) :
    (nib l k).length = btW n k := by
  simp only [nib, List.length_take, List.length_drop, hl, btW]
  unfold btN at hk
  split <;> omega

/-- **`block_selector_tab` is sound** at its 34 specializations. -/
theorem block_selector_tab_sound {n : ℕ} (hn : n < 34) {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
    {args rets : List E} (h : coreProgram.Rel Lm.read (lName "block_selector_tab" n) args rets) :
    BlockSelTabOut n Lm.read args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := btFound hn
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb (btPre_noRet n) args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar hret
  by_cases h0 : n = 0
  · subst h0
    simp only [btPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
    simp only [btRet, ↓reduceIte, List.map_cons, List.map_nil, BlockSelTabOut]
    refine ⟨[], rfl, tbReadsAt_nil _ _, fun zs zs1 gs hz hz1 hg _ => ?_⟩
    rw [List.length_eq_zero_iff] at hz hz1 hg
    subst hz hz1 hg
    simp [hpre.1, hpre.2, tb_word_one, bitsEq, bitsPow]
  simp only [btPre, h0, ↓reduceIte] at hpre
  rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
    tb_holdsList_flatten_range _ _ (btNibT_noRet n)] at hpre
  obtain ⟨hnibs, htail⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
  obtain ⟨hc1, hc2⟩ := htail
  set N := btN n with hNdef
  have hN1 : 1 ≤ N := by simp only [hNdef, btN]; omega
  have hNib : ∀ k < N, _ := fun k hk => holds_btNib hμ Lm (C := coreProgram.Rel Lm.read)
    (σ := σ) (kret := fun rs => rs = (btRet n).map σ) hk (hnibs k hk)
  choose U hU hdig xe xg hxe hxg hsel hrb using hNib
  let U' : ℕ → ℕ := fun k ↦ if hk : k < N then U k hk else 0
  have hU' : ∀ k (hk : k < N), U' k = U k hk := fun k hk => by simp only [U', hk, ↓reduceDIte]
  let xe' : ℕ → E := fun k ↦ if hk : k < N then xe k hk else 1
  let xg' : ℕ → E := fun k ↦ if hk : k < N then xg k hk else 1
  have hS : ∀ k < N, σ (.n (btSel k)) = ∏ m ∈ Finset.range (k + 1), xe' m := by
    intro k hk
    induction k with
    | zero => rw [hsel 0 hk]; simp [xe', hk]
    | succ k ih =>
      rw [hsel (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xe', hk]
  have hR : ∀ k < N, σ (.n (btRb k)) = ∏ m ∈ Finset.range (k + 1), xg' m := by
    intro k hk
    induction k with
    | zero => rw [hrb 0 hk]; simp [xg', hk]
    | succ k ih =>
      rw [hrb (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xg', hk]
  let F : ℕ → Bool := fun i ↦ (U' (i / 4)).testBit (i % 4)
  have hF : ∀ k t, t < 4 → F (4 * k + t) = (U' k).testBit t := fun k t ht => by
    simp only [F]
    rw [show (4 * k + t) / 4 = k by omega, show (4 * k + t) % 4 = t by omega]
  let bs := (List.range n).map F
  have hbs : ∀ i < n, bs.getD i false = F i := fun i hi => by
    simp [bs, List.getD_eq_getElem?_getD, hi]
  have hkt : ∀ i < n, i / 4 < N ∧ i % 4 < btW n (i / 4) := fun i hi => by
    simp only [hNdef, btN, btW]; constructor
    · omega
    · split <;> omega
  -- a digit's bits past its width vanish
  have hhigh : ∀ k (hk : k < N), ∀ t, btW n k ≤ t → (U' k).testBit t = false := by
    intro k hk t ht
    rw [hU' k hk]
    apply Nat.testBit_lt_two_pow
    exact lt_of_lt_of_le (hU k hk) (Nat.pow_le_pow_right (by norm_num) ht)
  simp only [btRet, h0, ↓reduceIte, List.map_cons, List.map_nil, BlockSelTabOut]
  refine ⟨bs, by simp [bs], fun k hk => ?_, fun zs zs1 gs hz hz1 hg hRT => ⟨?_, ?_⟩⟩
  · -- the digits
    have hk' : k < N := by simpa [nibDigits, bs, hNdef, btN] using hk
    simp only [nibDigits, List.getElem_map, List.getElem_range]
    have e : bitsVal (fun t ↦ bs.getD (4 * k + t) false) 4 = U k hk' := by
      rw [← bitsVal_testBit (lt_of_lt_of_le (hU k hk')
        (Nat.pow_le_pow_right (by norm_num) (btW_le n k)))]
      refine bitsVal_congr fun t ht => ?_
      by_cases hin : 4 * k + t < n
      · rw [hbs _ hin, hF k t ht, hU' k hk']
      · have hw : btW n k ≤ t := by simp only [btW]; split <;> omega
        rw [List.getD_eq_default _ _ (by simp [bs]; omega), ← hU' k hk', hhigh k hk' t hw]
    rw [e]
    exact hdig k hk'
  · -- the eq weight
    have hxe' : ∀ k < N, xe' k = ∏ t ∈ Finset.range (btW n k),
        (if F (4 * k + t) then zs.getD (4 * k + t) 0 else zs1.getD (4 * k + t) 0) := by
      intro k hk
      have hw1 := btW_pos hk
      have hw4 := btW_le n k
      have hlen := nib_length hz hk
      have hlen1 := nib_length hz1 hk
      have hUlt := hU k hk
      have hl : 2 ^ btW n k - 2 + U k hk < (eqLevels (nib zs k) (nib zs1 k)).length := by
        rw [eqLevels_length hlen hlen1]
        have := two_le_two_pow hw1
        rw [pow_succ]; omega
      have h1 := tbReadsAt_getD ((hRT k (by simpa [hNdef, btN] using hk)).1) hl
      rw [tb_loadHolds_mul_gen_pow, eqLevels_getD (hlen.trans hlen1.symm) hw1 (by omega) hUlt] at h1
      have h2 := hxe k hk
      have := two_le_two_pow hw1
      rw [show U k hk + (32 * k + 2 ^ btW n k - 2) = 32 * k + (2 ^ btW n k - 2 + U k hk) by omega]
        at h2
      simp only [xe', hk, ↓reduceDIte]
      rw [tb_loadHolds_unique h2 h1]
      refine Finset.prod_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      rw [bitPick, nib_getD ht', nib_getD ht', hF k t (by omega), hU' k hk]
    rw [hc1, hS (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxe' k (Finset.mem_range.mp hk)),
      bt_reindex (fun i ↦ if F i then zs.getD i 0 else zs1.getD i 0) n,
      bitsEq_eq_prod (m := n) (by simp [bs]) hz hz1]
    exact Finset.prod_congr rfl fun i hi => by rw [hbs i (Finset.mem_range.mp hi)]
  · -- the rebuilt power
    have hxg' : ∀ k < N, xg' k = ∏ t ∈ Finset.range (btW n k),
        (if F (4 * k + t) then gs.getD (4 * k + t) 0 else 1) := by
      intro k hk
      have hlen := nib_length hg hk
      have hUlt := hU k hk
      have hl : U k hk < (gTable (nib gs k)).length := by
        rw [gTable_length hlen]; exact hUlt
      have h1 := tbReadsAt_getD ((hRT k (by simpa [hNdef, btN] using hk)).2) hl
      rw [tb_loadHolds_mul_gen_pow, gTable_getD hlen hUlt] at h1
      have h2 := hxg k hk
      rw [show U k hk + 16 * k = 16 * k + U k hk by omega] at h2
      simp only [xg', hk, ↓reduceDIte]
      rw [tb_loadHolds_unique h2 h1]
      refine Finset.prod_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      have hw4 := btW_le n k
      rw [bitPick, nib_getD ht', hF k t (by omega), hU' k hk]
    rw [hc2, hR (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxg' k (Finset.mem_range.mp hk)),
      bt_reindex (fun i ↦ if F i then gs.getD i 0 else 1) n,
      bitsPow_eq_prod (m := n) (by simp [bs]) hg]
    exact Finset.prod_congr rfl fun i hi => by rw [hbs i (Finset.mem_range.mp hi)]

theorem block_selector_tab_holds : block_selector_tab_Spec :=
  fun _ hn _ hμ Lm _ _ h => block_selector_tab_sound hn hμ Lm h

end
end LeanVM.Guest.B1.Tables
