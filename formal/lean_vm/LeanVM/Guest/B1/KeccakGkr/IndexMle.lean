/-
  LeanVM.Guest.B1.KeccakGkr.IndexMle

  B1 for `index_mle`: its specializations `index_mle__L19` to `__L24` compute `indexMle`.
-/

module

public import LeanVM.Guest.B1.Tables.Squares
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«index_mle__L»

/-!
# `index_mle`

`index_mle(zeta, n)` (G) multiplies `1 + zeta[g^t]·INDEX_MLE_FACTORS[t]` over `t < n`,
`INDEX_MLE_FACTORS[t] = 1 + g^(2^t)` (`imFactor_eq`). Its specialization `index_mle__L{n}` is
`imBody n`: block `t` from value `6t` (`imBlk`), the first without the product, then a copy of
the last product, matched by the kernel (`stmtsEqb_sound`). The products are `indexMle` of the
loaded words (`indexMle_eq_prod`, `im_sound`). The function is the bus era's (`Selectors/IndexMle`
at tag `formal-bus-archive`), called now only by the link's `index_side`, at the pointer widths
`19` to `24`: `index_mle_sound`.
-/

namespace LeanVM.Guest.B1.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `index_mle__L{n}(zeta)`: the index MLE of the first `n` words at `zeta`. -/
def IndexMleOut (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [zeta], [v] => ∃ zs : List E, zs.length = n ∧ ReadsAt rd zeta zs ∧ v = indexMle zs
  | _, _ => False

/-! ## The specification's side -/

/-- The index MLE's factor at coordinate `t`: `1 + r·(1 + g^(2^t))`. -/
def imFactorOf (r : E) (t : ℕ) : E := 1 + r * (1 + gen ^ 2 ^ t)

theorem indexMleFrom_eq (zs : List E) : ∀ (k : ℕ) (acc : E),
    indexMleFrom (gen ^ 2 ^ k) zs acc =
      acc * ((List.range zs.length).map fun t ↦ imFactorOf (zs.getD t 0) (k + t)).prod := by
  induction zs with
  | nil => intro k acc; simp [indexMleFrom]
  | cons r rs ih =>
    intro k acc
    rw [indexMleFrom, show (gen ^ 2 ^ k) ^ 2 = gen ^ 2 ^ (k + 1) by
      rw [← pow_mul, pow_succ], ih (k + 1), List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.prod_cons, List.map_map]
    have hf : ((fun t ↦ imFactorOf ((r :: rs).getD t 0) (k + t)) ∘ fun t ↦ t + 1) =
        fun t ↦ imFactorOf (rs.getD t 0) (k + 1 + t) := by
      funext t
      rw [Function.comp_apply, List.getD_cons_succ, show k + (t + 1) = k + 1 + t by omega]
    rw [hf, List.getD_cons_zero, imFactorOf, mul_assoc]
    rfl

/-- **`indexMle` as a product** of its factors. -/
theorem indexMle_eq_prod (zs : List E) :
    indexMle zs = ((List.range zs.length).map fun t ↦ imFactorOf (zs.getD t 0) t).prod := by
  have := indexMleFrom_eq zs 0 1
  rw [pow_zero, pow_one] at this
  rw [indexMle, this, one_mul]
  simp

/-! ## The template -/

/-- `INDEX_MLE_FACTORS[t]`: the word of `1 + g^(2^t)`. -/
def imFactor (t : ℕ) : ℕ := tbGSquaresBits.getD t 0 ^^^ 1

theorem imFactor_eq {t : ℕ} (ht : t < 34) : word (imFactor t) 0 = 1 + gen ^ 2 ^ t := by
  rw [tb_word_eOfNat, imFactor, eOfNat_xor, eOfNat_one, gen_pow_two_pow_eq ht, add_comm]

/-- The value loaded at block `t`. -/
def imLoad (t : ℕ) : ℕ := if t = 0 then 2 else 6 * t + 1

/-- The product after block `t`. -/
def imAcc (t : ℕ) : ℕ := 6 * t + 5

/-- Block `t` of `index_mle`. -/
def imBlk (t : ℕ) : List Stmt :=
  if t = 0 then
    [.atom (.const (.n 1) (word 1 0)), .atom (.load (.n 2) (.n (valf% «index_mle» "zeta")) 0),
      .atom (.const (.n 3) (word (imFactor 0) 0)), .atom (.mul (.n 4) (.n 2) (.n 3)),
      .atom (.add (.n 5) (.n 1) (.n 4))]
  else
    [.atom (.const (.n (6 * t)) (word 1 0)), .atom (.load (.n (6 * t + 1)) (.n (valf% «index_mle» "zeta")) t),
      .atom (.const (.n (6 * t + 2)) (word (imFactor t) 0)),
      .atom (.mul (.n (6 * t + 3)) (.n (6 * t + 1)) (.n (6 * t + 2))),
      .atom (.add (.n (6 * t + 4)) (.n (6 * t)) (.n (6 * t + 3))),
      .atom (.mul (.n (6 * t + 5)) (.n (6 * t - 1)) (.n (6 * t + 4)))]

/-- `index_mle__L{n}`'s statements before its `ret`. -/
def imPre (n : ℕ) : List Stmt :=
  if n = 0 then [.atom (.const (.n 1) (word 1 0))]
  else ((List.range n).map imBlk).flatten ++ [.atom (.copy (.n (6 * n)) (.n (6 * n - 1)))]

/-- The value `index_mle__L{n}` returns. -/
def imRet (n : ℕ) : ℕ := if n = 0 then 1 else 6 * n

theorem imBlk_noRet (t : ℕ) : Stmt.noRetList (imBlk t) = true := by
  unfold imBlk; split <;> rfl

theorem imBlks_noRet : ∀ l : List ℕ, Stmt.noRetList (l.map imBlk).flatten = true
  | [] => rfl
  | t :: l => by
    rw [List.map_cons, List.flatten_cons, tb_noRetList_append, imBlk_noRet, imBlks_noRet l]; rfl

theorem imPre_noRet (n : ℕ) : Stmt.noRetList (imPre n) = true := by
  unfold imPre
  split
  · rfl
  · rw [tb_noRetList_append, imBlks_noRet]; rfl

theorem tb_prod_map_range_succ {M : Type} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ((List.range (m + 1)).map f).prod = ((List.range m).map f).prod * f m := by
  rw [List.range_succ, List.map_append, List.prod_append]; simp

/-! ## The semantics -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem holds_imBlk_zero (h : Stmt.HoldsList C rd σ (imBlk 0) True kret) :
    LoadHolds rd (σ (.n (valf% «index_mle» "zeta"))) 0 (σ (.n (imLoad 0))) ∧
      σ (.n (imAcc 0)) = imFactorOf (σ (.n (imLoad 0))) 0 := by
  simp only [imBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h2, ?_⟩
  simp only [imAcc, imLoad, ↓reduceIte, imFactorOf]
  rw [h5, h1, h4, h3, tb_word_one, imFactor_eq (by decide)]

theorem holds_imBlk_succ {t : ℕ} (ht : t < 34) (h0 : t ≠ 0)
    (h : Stmt.HoldsList C rd σ (imBlk t) True kret) :
    LoadHolds rd (σ (.n (valf% «index_mle» "zeta"))) t (σ (.n (imLoad t))) ∧
      σ (.n (imAcc t)) = σ (.n (imAcc (t - 1))) * imFactorOf (σ (.n (imLoad t))) t := by
  simp only [imBlk, h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by simp only [imLoad, h0, ↓reduceIte]; exact h2, ?_⟩
  simp only [imAcc, imLoad, h0, ↓reduceIte, imFactorOf]
  rw [h6, h5, h1, h4, h3, tb_word_one, imFactor_eq ht, show 6 * (t - 1) + 5 = 6 * t - 1 by omega]

end Sem

/-- **`index_mle` is sound**: `index_mle__L{n}(zeta)` returns `indexMle` of the first `n` words
at `zeta`. -/
theorem im_sound {P : Program} {name : String} {fn : Fn} (hf : P.find? name = some fn)
    (hp : fn.params = [.n (valf% «index_mle» "zeta")]) {n : ℕ} (hn : n < 34)
    (hb : fn.body = imPre n ++ [.ret [.n (imRet n)]]) {rd : Reader} {args rets : List E}
    (h : P.Rel rd name args rets) : IndexMleOut n rd args rets := by
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb (imPre_noRet n) args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  simp only [IndexMleOut]
  by_cases h0 : n = 0
  · subst h0
    simp only [imPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
    refine ⟨[], rfl, readsAt_nil _ _, ?_⟩
    simp only [imRet, ↓reduceIte, hpre, tb_word_one, indexMle, indexMleFrom]
  · simp only [imPre, h0, ↓reduceIte] at hpre
    rw [holdsList_append, holdsList_flatten _ (fun b hb => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact imBlk_noRet t)] at hpre
    obtain ⟨hblk, hcopy⟩ := hpre
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hcopy
    have hb : ∀ t < n, Stmt.HoldsList (P.Rel rd) rd σ (imBlk t) True
        (fun rs => rs = [σ (.n (imRet n))]) :=
      fun t ht => hblk _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
    let zs := (List.range n).map fun t ↦ σ (.n (imLoad t))
    have hacc : ∀ t < n, σ (.n (imAcc t)) =
        ((List.range (t + 1)).map fun s ↦ imFactorOf (zs.getD s 0) s).prod := by
      intro t ht
      induction t with
      | zero =>
        rw [(holds_imBlk_zero (hb 0 ht)).2]
        simp [zs, List.getD_eq_getElem?_getD, ht]
      | succ t ih =>
        rw [(holds_imBlk_succ (by omega) (by omega) (hb (t + 1) ht)).2, Nat.add_sub_cancel,
          ih (by omega), tb_prod_map_range_succ _ (t + 1)]
        congr 2
        simp [zs, List.getD_eq_getElem?_getD, ht]
    refine ⟨zs, by simp [zs], fun t ht => ?_, ?_⟩
    · simp only [zs, List.length_map, List.length_range] at ht
      simp only [zs, List.getElem_map, List.getElem_range]
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · exact (holds_imBlk_zero (hb 0 ht)).1
      · exact (holds_imBlk_succ (by omega) (by omega) (hb t ht)).1
    · simp only [imRet, h0, ↓reduceIte]
      rw [hcopy, indexMle_eq_prod, show 6 * n - 1 = imAcc (n - 1) by
        simp only [imAcc]; omega, hacc (n - 1) (by omega), show n - 1 + 1 = n by omega]
      simp [zs]


/-- `index_mle__L{w}`, `19 ≤ w ≤ 24`. -/
def imSpecNames : List String :=
  ["index_mle__L19", "index_mle__L20", "index_mle__L21", "index_mle__L22", "index_mle__L23", "index_mle__L24"]

set_option maxRecDepth 100000 in
theorem index_mle_L19_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (imSpecNames.getD 0 "") args rets → IndexMleOut 19 rd args rets :=
  im_sound (fn := fn% «index_mle__L19») (coreProgram_find?_at (j := idx% «index_mle__L19») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem index_mle_L20_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (imSpecNames.getD 1 "") args rets → IndexMleOut 20 rd args rets :=
  im_sound (fn := fn% «index_mle__L20») (coreProgram_find?_at (j := idx% «index_mle__L20») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem index_mle_L21_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (imSpecNames.getD 2 "") args rets → IndexMleOut 21 rd args rets :=
  im_sound (fn := fn% «index_mle__L21») (coreProgram_find?_at (j := idx% «index_mle__L21») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem index_mle_L22_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (imSpecNames.getD 3 "") args rets → IndexMleOut 22 rd args rets :=
  im_sound (fn := fn% «index_mle__L22») (coreProgram_find?_at (j := idx% «index_mle__L22») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem index_mle_L23_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (imSpecNames.getD 4 "") args rets → IndexMleOut 23 rd args rets :=
  im_sound (fn := fn% «index_mle__L23») (coreProgram_find?_at (j := idx% «index_mle__L23») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem index_mle_L24_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (imSpecNames.getD 5 "") args rets → IndexMleOut 24 rd args rets :=
  im_sound (fn := fn% «index_mle__L24») (coreProgram_find?_at (j := idx% «index_mle__L24») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

/-- **`index_mle` is sound** at the link's widths: `index_mle__L{w}(zeta)` returns `indexMle` of the
`w` words at `zeta`. -/
theorem index_mle_sound (w : ℕ) (h19 : 19 ≤ w) (h24 : w ≤ 24) (rd : Reader) (zeta v : E) :
    coreProgram.Rel rd (imSpecNames.getD (w - 19) "") [zeta] [v] →
      ∃ zs : List E, zs.length = w ∧ ReadsAt rd zeta zs ∧ v = indexMle zs := by
  interval_cases w
  exacts [index_mle_L19_sound rd _ _, index_mle_L20_sound rd _ _, index_mle_L21_sound rd _ _,
    index_mle_L22_sound rd _ _, index_mle_L23_sound rd _ _, index_mle_L24_sound rd _ _]

end
end LeanVM.Guest.B1.KeccakGkr
