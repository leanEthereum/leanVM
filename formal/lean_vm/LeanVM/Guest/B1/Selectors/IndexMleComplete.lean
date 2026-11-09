/-
  LeanVM.Guest.B1.Selectors.IndexMleComplete

  `index_mle` is complete: every `indexMle` of `n < 34` words in memory is an outcome of
  `index_mle__L{n}`.
-/

module

public import LeanVM.Guest.B1.Selectors.IndexMle

/-!
# `index_mle` is complete (TRIAGE G #44)

For words `zs` at `zeta`, the valuation `imVal` gives every value of `index_mle__L{n}`'s body
what the body computes: block `t`'s one, word, factor, product, sum and running product
(`imAccV`), and the final copy the last running product. Every statement holds of it, and the
returned word is `indexMle zs` (`index_mle_complete_holds`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Block `t`'s factor word. -/
def imFac (t : ℕ) : E := word (imFactor t) 0 0

/-- The running product after block `t`. -/
def imAccV (zs : List E) : ℕ → E
  | 0 => 1 + zs.getD 0 0 * imFac 0
  | t + 1 => imAccV zs t * (1 + zs.getD (t + 1) 0 * imFac (t + 1))

/-- Value `r < 6` of block `t ≥ 1`. -/
def imBlkV (zs : List E) (t r : ℕ) : E :=
  if r = 0 then 1 else if r = 1 then zs.getD t 0 else if r = 2 then imFac t
  else if r = 3 then zs.getD t 0 * imFac t else if r = 4 then 1 + zs.getD t 0 * imFac t
  else imAccV zs t

/-- Value `k` of `index_mle__L{n}` at `zeta`, `zs`. -/
def imVal (n : ℕ) (zeta : E) (zs : List E) (k : ℕ) : E :=
  if k = 0 then zeta
  else if n = 0 then 1
  else if k = 6 * n then imAccV zs (n - 1)
  else if k < 6 then imBlkV zs 0 (k - 1)
  else imBlkV zs (k / 6) (k % 6)

theorem imVal_blk {n : ℕ} (zeta : E) (zs : List E) {t r : ℕ} (ht1 : 1 ≤ t) (htn : t < n)
    (hr : r < 6) : imVal n zeta zs (6 * t + r) = imBlkV zs t r := by
  have h1 : (6 * t + r) / 6 = t := by omega
  have h2 : (6 * t + r) % 6 = r := by omega
  simp only [imVal, show 6 * t + r ≠ 0 by omega, show n ≠ 0 by omega,
    show 6 * t + r ≠ 6 * n by omega, show ¬ 6 * t + r < 6 by omega, ↓reduceIte, h1, h2]

theorem imVal_blk0 {n : ℕ} (zeta : E) (zs : List E) (hn : n ≠ 0) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k < 6) : imVal n zeta zs k = imBlkV zs 0 (k - 1) := by
  simp only [imVal, show k ≠ 0 by omega, hn, show k ≠ 6 * n by omega, hk, ↓reduceIte]

theorem imAccV_eq (zs : List E) : ∀ t < 34, imAccV zs t =
    ((List.range (t + 1)).map fun s ↦ imFactorOf (zs.getD s 0) s).prod
  | 0, _ => by simp [imAccV, imFactorOf, imFac, imFactor_eq (show 0 < 34 by norm_num)]
  | t + 1, ht => by
    rw [imAccV, imAccV_eq zs t (by omega), tb_prod_map_range_succ _ (t + 1), imFactorOf, imFac,
      imFactor_eq ht]

theorem imBlkV_0 (zs : List E) (t : ℕ) : imBlkV zs t 0 = 1 := by simp [imBlkV]
theorem imBlkV_1 (zs : List E) (t : ℕ) : imBlkV zs t 1 = zs.getD t 0 := by simp [imBlkV]
theorem imBlkV_2 (zs : List E) (t : ℕ) : imBlkV zs t 2 = imFac t := by simp [imBlkV]
theorem imBlkV_3 (zs : List E) (t : ℕ) : imBlkV zs t 3 = zs.getD t 0 * imFac t := by
  simp [imBlkV]
theorem imBlkV_4 (zs : List E) (t : ℕ) : imBlkV zs t 4 = 1 + zs.getD t 0 * imFac t := by
  simp [imBlkV]
theorem imBlkV_5 (zs : List E) (t : ℕ) : imBlkV zs t 5 = imAccV zs t := by simp [imBlkV]

/-- The running product's value: after block `t`, at `6t + 5` (`5` for block `0`). -/
theorem imVal_acc {n : ℕ} (zeta : E) (zs : List E) (hn : n ≠ 0) {t : ℕ} (ht : t < n) :
    imVal n zeta zs (6 * t + 5) = imAccV zs t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [imVal_blk0 zeta zs hn (by norm_num) (by norm_num)]
    simp [imBlkV, imAccV]
  · rw [imVal_blk zeta zs ht0 ht (by norm_num), imBlkV_5]

/-- **`index_mle` is complete** at its 34 specializations. -/
theorem index_mle_complete_holds : index_mle_complete_Spec := by
  intro n hn rd args rets h
  match args, rets, h with
  | [zeta], [v], ⟨zs, hzl, hzr, hv⟩ =>
    obtain ⟨fn, hf, hp, hb⟩ := imFound hn
    have hz0 : imVal n zeta zs 0 = zeta := by simp [imVal]
    refine (tb_rel_pre hf hb (imPre_noRet n) [zeta] [v]).mpr ⟨fun x ↦ imVal n zeta zs x.idx,
      by rw [hp]; simp only [List.map_cons, List.map_nil]; exact congrArg (· :: []) hz0, ?_, ?_⟩
    · by_cases h0 : n = 0
      · subst h0
        simp only [imPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        simp [imVal, tb_word_one]
      · simp only [imPre, h0, ↓reduceIte]
        rw [holdsList_append, holdsList_flatten _ (fun b hb ↦ by
          obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact imBlk_noRet t)]
        refine ⟨fun b hb ↦ ?_, ?_⟩
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
          have ht := List.mem_range.mp ht
          have hzt : LoadHolds rd zeta t (zs.getD t 0) := by
            have := hzr t (by omega)
            rwa [← List.getD_eq_getElem _ 0] at this
          rcases Nat.eq_zero_or_pos t with rfl | ht0
          · have e := fun k (hk1 : 1 ≤ k) (hk : k < 6) ↦ imVal_blk0 zeta zs h0 hk1 hk
            simp only [imBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
            rw [e 1 le_rfl (by norm_num), e 2 (by norm_num) (by norm_num),
              e 3 (by norm_num) (by norm_num), e 4 (by norm_num) (by norm_num),
              e 5 (by norm_num) (by norm_num), hz0]
            simp only [Nat.reduceSub, imBlkV_0, imBlkV_1, imBlkV_2, imBlkV_3, imBlkV_4, imFac,
              tb_word_one]
            exact ⟨trivial, hzt, trivial, trivial, trivial⟩
          · have e := fun r (hr : r < 6) ↦ imVal_blk (n := n) zeta zs (t := t) (r := r) ht0 ht hr
            have ep : imVal n zeta zs (6 * t - 1) = imAccV zs (t - 1) := by
              rw [show 6 * t - 1 = 6 * (t - 1) + 5 by omega, imVal_acc zeta zs h0 (by omega)]
            simp only [imBlk, show t ≠ 0 by omega, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
              Atom.Holds, and_true]
            rw [ep, hz0, show imVal n zeta zs (6 * t) = imBlkV zs t 0 from e 0 (by norm_num),
              e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
              e 5 (by norm_num)]
            rw [imBlkV_0, imBlkV_1, imBlkV_2, imBlkV_3, imBlkV_4, imBlkV_5, imFac, tb_word_one]
            refine ⟨rfl, hzt, rfl, rfl, rfl, ?_⟩
            obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
            simp [imAccV, imFac]
        · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          rw [show 6 * n - 1 = 6 * (n - 1) + 5 by omega, imVal_acc zeta zs h0 (by omega)]
          simp [imVal, h0]
    · show [imVal n zeta zs (imRet n)] = [v]
      rw [hv, indexMle_eq_prod, hzl]
      by_cases h0 : n = 0
      · subst h0; simp [imVal, imRet]
      · simp only [imRet, h0, ↓reduceIte, imVal, show 6 * n ≠ 0 by omega]
        rw [imAccV_eq zs (n - 1) (by omega), show n - 1 + 1 = n by omega]
  | [], _, h => simp [IndexMleOut] at h
  | _ :: _ :: _, _, h => simp [IndexMleOut] at h
  | [_], [], h => simp [IndexMleOut] at h
  | [_], _ :: _ :: _, h => simp [IndexMleOut] at h

end
end LeanVM.Guest.B1.Tables
