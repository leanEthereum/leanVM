/-
  LeanVM.Guest.B1.Selectors.RunNibbles

  B1 for `selector_run_nibbles`: a selector run's length split into its full nibbles and the
  partial one's width.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables
public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# `selector_run_nibbles`

`selector_run_nibbles(len_g)` hints the six bits of `len_g`'s exponent, pins them Boolean,
rebuilds `r_g = g^r` from the low two and `q_g = g^q` from the high four, asserts `q_g^4·r_g =
len_g` (so `len_g = g^n`, `n = 4q + r < 64`) and returns `q_g = g^(n / 4)`: `verify_tables` sizes
the run's tables by it and `shared_selector_tables` fills them.

* `selector_run_nibbles_holds`: its relation is `RunNibblesOut`;
* `selector_run_nibbles_complete_holds`: every `g^n`, `n < 64`, gives `g^(n / 4)` (the valuation
  `srnVal`: the bits of `n`, their factors, `g^r`, `g^q`);
* `selector_run_nibbles_relIn`: it loads nothing and calls nothing, so it holds in any region.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `selector_run_nibbles`' statements before its `ret`. -/
def srnPre : List Stmt :=
  [.atom (.hint (.bitsExp (.n 0) 6 (.stack [.n 1, .n 2, .n 3, .n 4, .n 5, .n 6]))),
    .atom (.mul (.n 1) (.n 1) (.n 1)), .atom (.mul (.n 2) (.n 2) (.n 2)),
    .atom (.mul (.n 3) (.n 3) (.n 3)), .atom (.mul (.n 4) (.n 4) (.n 4)),
    .atom (.mul (.n 5) (.n 5) (.n 5)), .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.const (.n 7) (word 1 0)), .atom (.const (.n 8) (word (imFactor 0) 0)),
    .atom (.mul (.n 9) (.n 1) (.n 8)), .atom (.add (.n 10) (.n 7) (.n 9)),
    .atom (.const (.n 11) (word 1 0)), .atom (.const (.n 12) (word (imFactor 1) 0)),
    .atom (.mul (.n 13) (.n 2) (.n 12)), .atom (.add (.n 14) (.n 11) (.n 13)),
    .atom (.mul (.n 15) (.n 10) (.n 14)),
    .atom (.const (.n 16) (word 1 0)), .atom (.const (.n 17) (word (imFactor 0) 0)),
    .atom (.mul (.n 18) (.n 3) (.n 17)), .atom (.add (.n 19) (.n 16) (.n 18)),
    .atom (.const (.n 20) (word 1 0)), .atom (.const (.n 21) (word (imFactor 1) 0)),
    .atom (.mul (.n 22) (.n 4) (.n 21)), .atom (.add (.n 23) (.n 20) (.n 22)),
    .atom (.mul (.n 24) (.n 19) (.n 23)),
    .atom (.const (.n 25) (word 1 0)), .atom (.const (.n 26) (word (imFactor 2) 0)),
    .atom (.mul (.n 27) (.n 5) (.n 26)), .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 29) (.n 24) (.n 28)),
    .atom (.const (.n 30) (word 1 0)), .atom (.const (.n 31) (word (imFactor 3) 0)),
    .atom (.mul (.n 32) (.n 6) (.n 31)), .atom (.add (.n 33) (.n 30) (.n 32)),
    .atom (.mul (.n 34) (.n 29) (.n 33)),
    .atom (.mul (.n 35) (.n 34) (.n 34)), .atom (.mul (.n 36) (.n 35) (.n 35)),
    .atom (.mul (.n 37) (.n 36) (.n 15)), .atom (.assertEq (.n 37) (.n 0)),
    .atom (.copy (.n 38) (.n 34))]

noncomputable def srnCheck : Bool :=
  match coreProgram.find? "selector_run_nibbles" with
  | some fn => decide (fn.params = [.n 0]) && tbStmtsEqb fn.body (srnPre ++ [.ret [.n 38]])
  | none => false

theorem srnCheck_eq : srnCheck = true := by decide +kernel

theorem srnFound : ∃ fn : Fn, coreProgram.find? "selector_run_nibbles" = some fn ∧
    fn.params = [.n 0] ∧ fn.body = srnPre ++ [.ret [.n 38]] := by
  have h := srnCheck_eq
  unfold srnCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem srnPre_noRet : Stmt.noRetList srnPre = true := rfl

/-- **`selector_run_nibbles` is sound**. -/
theorem selector_run_nibbles_holds : selector_run_nibbles_Spec := by
  intro rd args rets h
  obtain ⟨fn, hf, hp, hb⟩ := srnFound
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb srnPre_noRet args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  simp only [srnPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at hpre
  obtain ⟨p1, p2, p3, p4, p5, p6, c7, c8, m9, a10, c11, c12, m13, a14, m15, c16, c17, m18, a19,
    c20, c21, m22, a23, m24, c25, c26, m27, a28, m29, c30, c31, m32, a33, m34, m35, m36, m37, e37,
    h38⟩ := hpre
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (1 + k)) = 1)
  have pin : ∀ k < 6, σ (.n (1 + k)) * σ (.n (1 + k)) = σ (.n (1 + k)) := by
    intro k hk
    interval_cases k
    · exact p1.symm
    · exact p2.symm
    · exact p3.symm
    · exact p4.symm
    · exact p5.symm
    · exact p6.symm
  let r := bitsVal f 2
  let q := bitsVal (fun k ↦ f (k + 2)) 4
  have hr4 : r < 4 := bitsVal_lt f 2
  have hq16 : q < 16 := bitsVal_lt _ 4
  have hrg : σ (.n 15) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (1 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m15, a10, a14, c7, c11, m9, m13, c8, c12, tb_word_one, this]
  have hqg : σ (.n 34) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (1 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m34, m29, m24, a19, a23, a28, a33, c16, c20, c25, c30, m18, m22, m27, m32, c17, c21, c26,
      c31, tb_word_one, this]
  have hq4 : σ (.n 36) = gen ^ (4 * q) := by rw [m36, m35, hqg]; ring
  refine ⟨4 * q + r, by omega, ?_, ?_⟩
  · rw [← e_add_eq_zero_iff.mp e37, m37, hq4, hrg, ← pow_add]
  · rw [h38, hqg, show (4 * q + r) / 4 = q by omega]

/-! ## Completeness -/

/-- Bit `k` of `n` as a word. -/
def ssB (n k : ℕ) : E := bitE (n.testBit k)

/-- The factor of bit `k` of `n` at share `t`. -/
def ssF (n k t : ℕ) : E := word 1 0 + ssB n k * word (imFactor t) 0

/-- **Value `x` of `selector_run_nibbles`** on `g^n`. -/
def srnVal (n x : ℕ) : E :=
  let v15 := ssF n 0 0 * ssF n 1 1
  let v34 := ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3
  let v36 := v34 * v34 * (v34 * v34)
  [gen ^ n, ssB n 0, ssB n 1, ssB n 2, ssB n 3, ssB n 4, ssB n 5,
    word 1 0, word (imFactor 0) 0, ssB n 0 * word (imFactor 0) 0, ssF n 0 0,
    word 1 0, word (imFactor 1) 0, ssB n 1 * word (imFactor 1) 0, ssF n 1 1, v15,
    word 1 0, word (imFactor 0) 0, ssB n 2 * word (imFactor 0) 0, ssF n 2 0,
    word 1 0, word (imFactor 1) 0, ssB n 3 * word (imFactor 1) 0, ssF n 3 1,
    ssF n 2 0 * ssF n 3 1,
    word 1 0, word (imFactor 2) 0, ssB n 4 * word (imFactor 2) 0, ssF n 4 2,
    ssF n 2 0 * ssF n 3 1 * ssF n 4 2,
    word 1 0, word (imFactor 3) 0, ssB n 5 * word (imFactor 3) 0, ssF n 5 3, v34,
    v34 * v34, v36, v36 * v15, v34].getD x 0

theorem ssF_eq (n k t : ℕ) (ht : t < 34) :
    ssF n k t = gen ^ (2 ^ t * (n.testBit k).toNat) := by
  rw [ssF, ssB, imFactor_eq ht, tb_word_one]
  cases n.testBit k
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul, Bool.toNat_true, mul_one]
    rw [← add_assoc, e_add_self, zero_add]

theorem ss_bits {n : ℕ} (hn : n < 64) :
    n % 4 = (n.testBit 0).toNat + 2 * (n.testBit 1).toNat ∧
      n / 4 = (n.testBit 2).toNat + 2 * (n.testBit 3).toNat + 4 * (n.testBit 4).toNat +
        8 * (n.testBit 5).toNat := by
  have h := bitsVal_testBit (n := 6) hn
  simp only [bitsVal, Nat.reducePow, one_mul, zero_add] at h
  have b0 := Bool.toNat_le (n.testBit 0); have b1 := Bool.toNat_le (n.testBit 1)
  have b2 := Bool.toNat_le (n.testBit 2); have b3 := Bool.toNat_le (n.testBit 3)
  have b4 := Bool.toNat_le (n.testBit 4); have b5 := Bool.toNat_le (n.testBit 5)
  omega

theorem ssB_mul_self (n k : ℕ) : ssB n k = ssB n k * ssB n k := by rw [ssB, bitE_mul_self]

/-- **`selector_run_nibbles` is complete.** -/
theorem selector_run_nibbles_complete_holds : selector_run_nibbles_complete_Spec := by
  intro rd n hn
  obtain ⟨fn, hf, hp, hb⟩ := srnFound
  obtain ⟨hr, hq⟩ := ss_bits hn
  have v15 : ssF n 0 0 * ssF n 1 1 = gen ^ (n % 4) := by
    rw [ssF_eq n 0 0 (by norm_num), ssF_eq n 1 1 (by norm_num), ← pow_add, hr]; ring_nf
  have v34 : ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3 = gen ^ (n / 4) := by
    rw [ssF_eq n 2 0 (by norm_num), ssF_eq n 3 1 (by norm_num), ssF_eq n 4 2 (by norm_num),
      ssF_eq n 5 3 (by norm_num), ← pow_add, ← pow_add, ← pow_add, hq]; ring_nf
  refine (tb_rel_pre hf hb srnPre_noRet _ _).mpr ⟨fun x ↦ srnVal n x.idx, by rw [hp]; rfl, ?_,
    by simp [srnVal, v34]⟩
  simp only [srnPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true]
  simp (config := { decide := true }) only [srnVal, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, true_and, v15, v34]
  set q := n / 4 with hqd
  have p4 : gen ^ q * gen ^ q * (gen ^ q * gen ^ q) = gen ^ (4 * q) := by
    simp only [← pow_add]; congr 1; omega
  rw [p4]
  refine ⟨ssB_mul_self n 0, ssB_mul_self n 1, ssB_mul_self n 2, ssB_mul_self n 3, ssB_mul_self n 4,
    ssB_mul_self n 5, rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩
  rw [← pow_add, show 4 * q + n % 4 = n by omega]
  exact e_add_self _

/-! ## In a region -/

theorem srn_flat : srnPre.all Stmt.flat = true := by decide +kernel

theorem srn_noLoad : srnPre.filterMap Stmt.loadS = [] := by decide +kernel

theorem srn_calls : srnPre.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem srn_noDisp : srnPre.all noDispB = true := by decide +kernel

/-- **`selector_run_nibbles` loads from any region**: it loads nothing and calls nothing. -/
theorem selector_run_nibbles_relIn {rd : Reader} {R : ℕ → Prop} {args rets : List E}
    (h : coreProgram.Rel rd "selector_run_nibbles" args rets) :
    coreProgram.RelIn rd R "selector_run_nibbles" args rets := by
  obtain ⟨fn, hf, -, hb⟩ := srnFound
  refine relIn_of_flatRel hf hb srn_flat h fun σ _ _ ↦ ⟨fun s hs ↦ ?_, by rw [srn_noLoad]; simp,
    fun c hc _ ↦ ?_⟩
  · exact dispOk_of_noDisp (List.all_eq_true.mp srn_noDisp s hs)
  · rw [filterMap_callSF srn_noDisp, srn_calls] at hc
    simp at hc

end
end LeanVM.Guest.B1.Tables
