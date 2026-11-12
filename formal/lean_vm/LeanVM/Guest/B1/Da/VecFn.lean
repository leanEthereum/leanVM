/-
  LeanVM.Guest.B1.Da.VecFn

  `da_vector`'s body, checked, and its meaning from its callees' (G:4371-4388).
-/

module

public import LeanVM.Guest.B1.Da.Offsets
public import LeanVM.Guest.B1.Da.Expand

/-!
# `da_vector` (G:4371-4388)

`da_vector(z)` (`core31`): the powers `zs[j] = z^(2^j)` by squaring, `zs[14] = 0`; the shifts of
the tree over the cell index (`above_top`, zero at `8 … 14`); then `da_factors__L14_L7_L0(zs)`,
`da_expand__L14_L7(1, ·, zs, above_top)`, `da_factors__L7_L8_L128(zs)` and
`da_column_offsets(zs)`, whose results it returns with `zs`. `vecOk` checks the body (kernel
evaluation in `VecFnChk`); `da_vector_val` gives `MeaningDaVector` from the callees' meanings:
the factors and shifts the callees read are `zs`' (`factorAt_congr`, `expandLeaf_congr`), so the
tree over the cell index has the top leaves (`topLeaf_eq`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Congruences -/

theorem factorAt_congr {Z Z' : ℕ → E} {top n : ℕ} (h : Z (top - Nat.log 2 n) = Z' (top - Nat.log 2 n)) :
    factorAt Z top n = factorAt Z' top n := by
  rw [factorAt, factorAt, h]

theorem expandLeaf_congr {root : E} {F F' Z Z' S S' : ℕ → E} {top D y : ℕ} (hy : y < 2 ^ D)
    (hF : ∀ n, 1 ≤ n → n < 2 ^ D → F n = F' n) (hZ : ∀ d < D, Z (top - d) = Z' (top - d))
    (hS : ∀ d < D, S (top - d) = S' (top - d)) :
    expandLeaf root F Z S top D y = expandLeaf root F' Z' S' top D y := by
  unfold expandLeaf
  congr 1
  refine congrArg _ (List.map_congr_left fun k hk ↦ ?_)
  have hk' := List.mem_range.mp hk
  have hm : y >>> (D - k) < 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, show D - k + k = D by omega]; exact hy)
  rw [hF _ (Nat.le_add_right_of_le (Nat.one_le_two_pow (n := k)))
    (by calc 2 ^ k + y >>> (D - k) < 2 ^ k + 2 ^ k := by omega
          _ = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)),
    hZ k hk', hS k hk']

/-! ## The check -/

/-- `da_vector`'s block (its body but the final `ret`). -/
noncomputable def vecP : List Stmt := (Fn.body Data.core31).dropLast

/-- The value of `z^(2^j)`: `.n 0`, then `.n (j + 1)`. -/
def vecPw (j : ℕ) : ℕ := if j = 0 then 0 else j + 1

/-- **`da_vector`'s block, checked.** -/
noncomputable def vecOk : Bool :=
  let P := vecP
  let A := atomsIn P
  decide (Data.core31.params = [.n 0]) &&
  stmtsEqb (Fn.body Data.core31) (P ++ [.ret [.n 30, .n 31, .n 32, .n 33]]) && P.all Stmt.flat &&
  (List.range 14).all (fun j ↦ A.any (isLoadAt (.n (vecPw j)) (.n 1) j)) &&
  (List.range 13).all (fun j ↦ isMul A (.n (j + 2)) (.n (vecPw j)) (.n (vecPw j))) &&
  A.any (isConstAt (.n 16) 0 0) && A.any (isLoadAt (.n 16) (.n 1) 14) &&
  (List.range 7).all (fun i ↦ A.any (isConstAt (.n (18 + i)) 0 0) &&
    A.any (isLoadAt (.n (18 + i)) (.n 17) (8 + i))) &&
  hasCall P "da_factors__L14_L7_L0" [.n 1] [.n 25] && A.any (isConstAt (.n 26) 1 0) &&
  hasCall P "da_expand__L14_L7" [.n 26, .n 25, .n 1, .n 17] [.n 27] &&
  hasCall P "da_factors__L7_L8_L128" [.n 1] [.n 28] &&
  hasCall P "da_column_offsets" [.n 1] [.n 29] &&
  A.any (isCopyAt (.n 30) (.n 1)) && A.any (isCopyAt (.n 31) (.n 27)) &&
  A.any (isCopyAt (.n 32) (.n 28)) && A.any (isCopyAt (.n 33) (.n 29))

/-- **`da_vector`'s core IR gives its meaning**, from its callees'. -/
theorem da_vector_val (hok : vecOk = true) (hfac : da_factors_sound_Spec)
    (hexp : da_expand_sound_Spec) (hoff : da_column_offsets_sound_Spec) :
    da_vector_sound_Spec := by
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_vector _ _).mp hrel
  unfold vecOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hpw⟩, hsq⟩, hc16⟩, hl16⟩, hshift⟩, hcf⟩,
    hc26⟩, hce⟩, hcf7⟩, hco⟩, h30⟩, h31⟩, h32⟩, h33⟩ := hok
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat vecP (List.all_eq_true.mpr hflat) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  subst hret
  have hat := atoms_of_flat hall
  set z := σ (.n 0)
  -- the powers
  have hpow : ∀ j < 14, σ (.n (vecPw j)) = z ^ 2 ^ j := by
    intro j
    induction j with
    | zero => intro _; simp [vecPw, z]
    | succ j ih =>
      intro hj
      have := isMul_sound (hsq j (by omega)) hat
      rw [show vecPw (j + 1) = j + 2 by simp [vecPw], this, ih (by omega), ← pow_two, ← pow_mul,
        ← pow_succ]
  have hzs : ZsAt rd (σ (.n 1)) z := by
    intro j hj
    rcases Nat.lt_or_ge j 14 with h | h
    · have := load_sound (hpw j h) hat
      rwa [hpow j h, ← show zsVal z j = z ^ 2 ^ j by simp [zsVal, h]] at this
    · have := load_sound hl16 hat
      rw [const_sound hc16 hat, word_zero] at this
      rwa [show j = 14 by omega, show zsVal z 14 = 0 by simp [zsVal]]
  have hzu : ∀ {j v}, j < 15 → LoadHolds rd (σ (.n 1)) j v → v = zsVal z j := fun hj h ↦
    loadHolds_unique h (hzs _ hj)
  -- the callees
  have rF14 := hfac.1 rd _ _ (call_of_flat hall hcf)
  have rE := hexp.1 rd _ _ (call_of_flat hall hce)
  have rF7 := hfac.2 rd _ _ (call_of_flat hall hcf7)
  have rO := hoff rd _ _ (call_of_flat hall hco)
  simp only [List.map_cons, List.map_nil, MeaningDaFactors, MeaningDaExpand,
    MeaningDaColumnOffsets] at rF14 rE rF7 rO
  obtain ⟨Z1, hZ1, hF1⟩ := rF14
  obtain ⟨F, Z, S, hF, hZ, hS, hrun⟩ := rE
  obtain ⟨Z2, hZ2, hF2⟩ := rF7
  obtain ⟨Z3, hZ3, hO⟩ := rO
  rw [const_sound hc26 hat, word_one] at hrun
  simp only [MeaningDaVector, copy_sound h30 hat, copy_sound h31 hat, copy_sound h32 hat,
    copy_sound h33 hat]
  refine ⟨hzs, ⟨hrun.1, fun k hk w hw ↦ ?_⟩, fun n hn1 hn2 ↦ ?_, fun h hh j hj ↦ ?_⟩
  · -- the top leaves
    rw [hrun.2 k (by norm_num at hk ⊢; omega) w hw, ← topLeaf_eq z hk]
    refine expandLeaf_congr (by norm_num; omega) (fun n h1 h2 ↦ ?_) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
    · have e1 := loadHolds_unique (hF n h1 h2) (hF1 n h1 h2)
      rw [e1]
      refine factorAt_congr ?_
      have hl : Nat.log 2 n < 7 := Nat.log_lt_of_lt_pow (by omega) h2
      have := hZ1 (Nat.log 2 n) hl
      exact hzu (by omega) this
    · exact hzu (by omega) (hZ d hd)
    · have hsh := (hshift (6 - d) (by omega))
      have l := load_sound hsh.2 hat
      rw [const_sound hsh.1 hat, word_zero, show 8 + (6 - d) = 14 - d by omega] at l
      exact loadHolds_unique (hS d hd) l
  · -- the cell tree's factors
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num] at hn2
    refine (factorAt_congr ?_) ▸ hF2 n hn1 hn2
    have hl : Nat.log 2 n < 8 := Nat.log_lt_of_lt_pow (by omega) hn2
    exact hzu (by omega) (hZ2 (Nat.log 2 n) hl)
  · -- the offsets
    have e := hzu (by omega) (hZ3 j hj)
    rw [← e]
    exact hO h hh j hj

end
end LeanVM.Guest.B1.Da
