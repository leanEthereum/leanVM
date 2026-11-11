/-
  LeanVM.Guest.B1.Selectors.BlockSelector

  B1 for `block_selector`: its 34 specializations read pinned bits and return their eq weight and
  `g`-power product, a bit at a time.
-/

module

public import LeanVM.Guest.B1.Selectors.IndexMle

/-!
# `block_selector` (TRIAGE G #50)

`block_selector(sel_bits, zeta1_hi, idxc_hi, n)` (G:1856-1871) reads bit `k < n` at `sel_bits`,
pins it by the write-once store of its square (`b = b²`, so `b ∈ {0, 1}`), and multiplies
`b + zeta1_hi[k]` and `1 + b·idxc_hi[k]`. Its specialization `block_selector__L{n}` is `bsBody n`:
bit `k`'s block from value `10k + 1` (`bsBlk`), the first without the products, then copies of the
two last products (`bsFound`, by kernel evaluation for all `n < 34`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The bit read at block `k`. -/
def bsBit (k : ℕ) : ℕ := if k = 0 then 3 else 10 * k + 1

/-- The eq product after block `k`. -/
def bsEq (k : ℕ) : ℕ := if k = 0 then 6 else 10 * k + 5

/-- The `g`-power product after block `k`. -/
def bsRb (k : ℕ) : ℕ := if k = 0 then 10 else 10 * k + 10

/-- Block `k` of `block_selector`. -/
def bsBlk (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 3) (.n 0) 0), .atom (.mul (.n 4) (.n 3) (.n 3)),
      .atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 1) 0),
      .atom (.add (.n 6) (.n 3) (.n 5)), .atom (.const (.n 7) (word 1 0)),
      .atom (.load (.n 8) (.n 2) 0), .atom (.mul (.n 9) (.n 3) (.n 8)),
      .atom (.add (.n 10) (.n 7) (.n 9))]
  else
    let B := 10 * k + 1
    [.atom (.load (.n B) (.n 0) k), .atom (.mul (.n (B + 1)) (.n B) (.n B)),
      .atom (.load (.n (B + 1)) (.n 0) k), .atom (.load (.n (B + 2)) (.n 1) k),
      .atom (.add (.n (B + 3)) (.n B) (.n (B + 2))),
      .atom (.mul (.n (B + 4)) (.n (bsEq (k - 1))) (.n (B + 3))),
      .atom (.const (.n (B + 5)) (word 1 0)), .atom (.load (.n (B + 6)) (.n 2) k),
      .atom (.mul (.n (B + 7)) (.n B) (.n (B + 6))),
      .atom (.add (.n (B + 8)) (.n (B + 5)) (.n (B + 7))),
      .atom (.mul (.n (B + 9)) (.n (bsRb (k - 1))) (.n (B + 8)))]

/-- `block_selector__L{n}`'s statements before its `ret`. -/
def bsPre (n : ℕ) : List Stmt :=
  if n = 0 then [.atom (.const (.n 3) (word 1 0)), .atom (.const (.n 4) (word 1 0))]
  else ((List.range n).map bsBlk).flatten ++
    [.atom (.copy (.n (10 * n + 1)) (.n (bsEq (n - 1)))),
      .atom (.copy (.n (10 * n + 2)) (.n (bsRb (n - 1))))]

/-- The values `block_selector__L{n}` returns. -/
def bsRet (n : ℕ) : List V := if n = 0 then [.n 3, .n 4] else [.n (10 * n + 1), .n (10 * n + 2)]

/-- The function found by name is the template. -/
noncomputable def bsCheck (n : ℕ) : Bool :=
  match coreProgram.find? (lName "block_selector" n) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      tbStmtsEqb fn.body (bsPre n ++ [.ret (bsRet n)])
  | none => false

theorem bsCheck_all : (List.range 34).all bsCheck = true := by decide +kernel

theorem bsFound {n : ℕ} (hn : n < 34) : ∃ fn : Fn,
    coreProgram.find? (lName "block_selector" n) = some fn ∧ fn.params = [.n 0, .n 1, .n 2] ∧
      fn.body = bsPre n ++ [.ret (bsRet n)] := by
  have h := List.all_eq_true.mp bsCheck_all n (List.mem_range.mpr hn)
  unfold bsCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem bsBlk_noRet (k : ℕ) : Stmt.noRetList (bsBlk k) = true := by
  unfold bsBlk; split <;> rfl

theorem bsBlks_noRet : ∀ l : List ℕ, Stmt.noRetList (l.map bsBlk).flatten = true
  | [] => rfl
  | t :: l => by
    rw [List.map_cons, List.flatten_cons, tb_noRetList_append, bsBlk_noRet, bsBlks_noRet l]; rfl

theorem bsPre_noRet (n : ℕ) : Stmt.noRetList (bsPre n) = true := by
  unfold bsPre
  split
  · rfl
  · rw [tb_noRetList_append, bsBlks_noRet]; rfl

/-! ## The semantics -/

/-- A word pinned by the write-once store of its square is a bit. -/
theorem tb_pinned_bit {rd : Reader} {p b s : E} {k : ℕ} (hl : LoadHolds rd p k b)
    (hs : LoadHolds rd p k s) (hsq : s = b * b) : b = bitE (decide (b = 1)) :=
  bitE_of_mul_self (by rw [← hsq]; exact (tb_loadHolds_unique hl hs).symm)

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- What block `k` gives: the bit, its two loads, and the two products. -/
def BsBlkOut (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) k (σ (.n (bsBit k))) ∧
    σ (.n (bsBit k)) = bitE (decide (σ (.n (bsBit k)) = 1)) ∧
    ∃ z1 c, LoadHolds rd (σ (.n 1)) k z1 ∧ LoadHolds rd (σ (.n 2)) k c ∧
      σ (.n (bsEq k)) = (if k = 0 then 1 else σ (.n (bsEq (k - 1)))) * (σ (.n (bsBit k)) + z1) ∧
      σ (.n (bsRb k)) = (if k = 0 then 1 else σ (.n (bsRb (k - 1)))) *
        (1 + σ (.n (bsBit k)) * c)

theorem holds_bsBlk (k : ℕ) (h : Stmt.HoldsList C rd σ (bsBlk k) True kret) : BsBlkOut rd σ k := by
  by_cases h0 : k = 0
  · subst h0
    simp only [bsBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    simp only [BsBlkOut, bsBit, bsEq, bsRb, ↓reduceIte, one_mul]
    refine ⟨h1, tb_pinned_bit h1 h3 h2, _, _, h4, h7, h5, ?_⟩
    rw [h9, h6, h8, tb_word_one]
  · simp only [bsBlk, h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    have e1 : bsBit k = 10 * k + 1 := by simp only [bsBit, h0, ↓reduceIte]
    have e2 : bsEq k = 10 * k + 1 + 4 := by simp only [bsEq, h0, ↓reduceIte]
    have e3 : bsRb k = 10 * k + 1 + 9 := by simp only [bsRb, h0, ↓reduceIte]
    simp only [BsBlkOut, e1, e2, e3, h0, ↓reduceIte]
    refine ⟨h1, tb_pinned_bit h1 h3 h2, _, _, h4, h8, ?_, ?_⟩
    · rw [h6, h5]
    · rw [h11, h10, h7, h9, tb_word_one]

end Sem

theorem tb_prod_map_range_succ' {M : Type} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ((List.range (m + 1)).map f).prod = ((List.range m).map f).prod * f m := by
  rw [List.range_succ, List.map_append, List.prod_append]; simp

theorem tb_zip_map_range {α β : Type} (f : ℕ → α) (g : ℕ → β) (n : ℕ) :
    List.zip ((List.range n).map f) ((List.range n).map g) =
      (List.range n).map fun k ↦ (f k, g k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.zip_append, ih]

/-- **`block_selector` is sound**: `block_selector__L{n}` reads `n` pinned bits and returns
`Π (b + z1)` and `Π (1 + b·c)`. -/
theorem block_selector_sound {n : ℕ} (hn : n < 34) {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (lName "block_selector" n) args rets) : BlockSelOut n rd args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := bsFound hn
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb (bsPre_noRet n) args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar hret
  by_cases h0 : n = 0
  · subst h0
    simp only [bsPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
    simp only [bsRet, ↓reduceIte, List.map_cons, List.map_nil, BlockSelOut]
    refine ⟨[], [], [], rfl, rfl, rfl, tbReadsAt_nil _ _, tbReadsAt_nil _ _, tbReadsAt_nil _ _,
      ?_, ?_⟩
    · simp [hpre.1, tb_word_one]
    · simp [hpre.2, tb_word_one]
  · simp only [bsPre, h0, ↓reduceIte] at hpre
    rw [holdsList_append, holdsList_flatten _ (fun b hb => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact bsBlk_noRet t)] at hpre
    obtain ⟨hblk, hcopy⟩ := hpre
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hcopy
    have hb : ∀ k < n, BsBlkOut rd σ k := fun k hk => holds_bsBlk k
      (hblk _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    choose z1 c hz1 hc heq hrb using fun k (hk : k < n) => (hb k hk).2.2
    let bs := (List.range n).map fun k ↦ decide (σ (.n (bsBit k)) = 1)
    let zs1 := (List.range n).map fun k ↦ if hk : k < n then z1 k hk else 0
    let cs := (List.range n).map fun k ↦ if hk : k < n then c k hk else 0
    have hE : ∀ k < n, σ (.n (bsEq k)) = ((List.range (k + 1)).map fun j ↦
        σ (.n (bsBit j)) + (if hj : j < n then z1 j hj else 0)).prod := by
      intro k hk
      induction k with
      | zero => simp [heq 0 hk, hk]
      | succ k ih =>
        rw [heq (k + 1) hk, tb_prod_map_range_succ' _ (k + 1)]
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [ih (by omega)]
        simp [hk]
    have hR : ∀ k < n, σ (.n (bsRb k)) = ((List.range (k + 1)).map fun j ↦
        1 + σ (.n (bsBit j)) * (if hj : j < n then c j hj else 0)).prod := by
      intro k hk
      induction k with
      | zero => simp [hrb 0 hk, hk]
      | succ k ih =>
        rw [hrb (k + 1) hk, tb_prod_map_range_succ' _ (k + 1)]
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [ih (by omega)]
        simp [hk]
    simp only [bsRet, h0, ↓reduceIte, List.map_cons, List.map_nil, BlockSelOut]
    refine ⟨bs, zs1, cs, by simp [bs], by simp [zs1], by simp [cs], fun k hk => ?_,
      fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · simp only [bs, List.length_map, List.length_range] at hk
      simp only [bs, List.getElem_map, List.getElem_range]
      rw [← (hb k hk).2.1]; exact (hb k hk).1
    · simp only [zs1, List.length_map, List.length_range] at hk
      simp only [zs1, List.getElem_map, List.getElem_range, hk, ↓reduceDIte]
      exact hz1 k hk
    · simp only [cs, List.length_map, List.length_range] at hk
      simp only [cs, List.getElem_map, List.getElem_range, hk, ↓reduceDIte]
      exact hc k hk
    · rw [hcopy.1, hE (n - 1) (by omega), show n - 1 + 1 = n by omega, tb_zip_map_range,
        List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro k hk
      have hk' : k < n := List.mem_range.mp hk
      simp only [Function.comp_apply]
      rw [← (hb k hk').2.1]
    · rw [hcopy.2, hR (n - 1) (by omega), show n - 1 + 1 = n by omega, tb_zip_map_range,
        List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro k hk
      have hk' : k < n := List.mem_range.mp hk
      simp only [Function.comp_apply]
      rw [← (hb k hk').2.1]

theorem block_selector_holds : block_selector_Spec := fun _ hn _ _ _ h => block_selector_sound hn h

end
end LeanVM.Guest.B1.Tables
