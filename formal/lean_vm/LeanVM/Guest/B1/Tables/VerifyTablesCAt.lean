/-
  LeanVM.Guest.B1.Tables.VerifyTablesCAt

  `verify_tables`' body holding up to a statement, and the soundness side's values on it.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesVals
public import LeanVM.Guest.B1.Tables.VerifyTablesTail
public import LeanVM.Guest.B1.Tables.VerifyTablesCopies

/-!
# The body up to `M`

`VtHoldsAt M`: the first `M` statements hold. Its readers (`atom`, `slice`, `callIf`, `fsNext`,
`squeeze`, by kernel comparison on `vtPre.take M`) and `window_eval_at` are `VtHolds`'s; the
values the completeness proof needs before its final check are the soundness side's, on a prefix
(`vt_vals_at`, `vt_air_at`, `vt_eqhi_at`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The first `M` statements of `verify_tables` hold. -/
def VtHoldsAt (M : ℕ) (rd : Reader) (σ : Val) : Prop :=
  ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ (vtPre.take M) True kret

theorem vt_noRetList_take : ∀ (l : List Stmt) (M : ℕ), Stmt.noRetList l = true → Stmt.noRetList (l.take M) = true
  | [], M, _ => by rw [List.take_nil]; rfl
  | _ :: _, 0, _ => rfl
  | s :: l, M + 1, h => by
    rw [List.take_succ_cons]
    simp only [Stmt.noRetList, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, vt_noRetList_take l M h.2⟩

theorem vtPre_take_noRet (M : ℕ) : Stmt.noRetList (vtPre.take M) = true := vt_noRetList_take _ M vtPre_noRet

section
variable {rd : Reader} {σ : Val} {M : ℕ}

theorem VtHoldsAt.atom (h : VtHoldsAt M rd σ) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] (((vtPre.take M).drop n).take 1) = true) : a.Holds rd σ := by
  obtain ⟨k, h⟩ := h
  exact holds_atom (vtPre_take_noRet M) h n a heq

theorem VtHoldsAt.slice (h : VtHoldsAt M rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk (((vtPre.take M).drop n).take blk.length) = true) :
    ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True kret := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, holds_slice (vtPre_take_noRet M) h n blk heq⟩

theorem VtHoldsAt.callIf (h : VtHoldsAt M rd σ) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : stmtsEqb [.callIf c f args] (((vtPre.take M).drop n).take 1) = true) :
    σ c ≠ 0 → coreProgram.Rel rd f (args.map σ) [] := by
  obtain ⟨k, h⟩ := h
  exact holds_callIf (vtPre_take_noRet M) h n c f args heq

theorem VtHoldsAt.fsNext (h : VtHoldsAt M rd σ) (n : ℕ) (s0 s1 cur : V) (j b : ℕ)
    (heq : stmtsEqb (fsNextT s0 s1 cur j b) (((vtPre.take M).drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars (obsCv cv (σ (.n b))) := by
  obtain ⟨k, h⟩ := h
  exact holds_fsNextAt (vtPre_take_noRet M) h n s0 s1 cur j b heq

theorem VtHoldsAt.squeeze (h : VtHoldsAt M rd σ) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) (((vtPre.take M).drop n).take 14) = true) :
    ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars (sqCv cv) ∧
      σ (.n (b + 13)) = challengeOf (sqCv cv) := by
  obtain ⟨k, h⟩ := h
  exact holds_squeezeAt (vtPre_take_noRet M) h n s0 s1 b heq

theorem take_drop_take {α : Type} (l : List α) {M n len : ℕ} (h : n + len ≤ M) :
    ((l.take M).drop n).take len = (l.drop n).take len := by
  rw [List.drop_take, List.take_take, min_eq_left (by omega)]

/-- **A value of a window of the body up to `M`, by reflection.** -/
theorem window_eval_at (h : VtHoldsAt M rd σ) {χ : ℕ → E} {L : LoadTab} (hL : L.Sound rd σ χ)
    (n len k : ℕ) (e : Ex) (hb : n + len ≤ M)
    (heq : ((symExec L [] (((vtPre.drop n).take len).filterMap atomOf)).get k).norm = e.norm) :
    σ (.n k) = e.eval (fun k => σ (.n k)) χ := by
  obtain ⟨kr, hh⟩ := h
  refine window_eval (vtPre_take_noRet M) hh hL n len k e ?_
  rw [take_drop_take _ hb]; exact heq

/-! ## The soundness side's values, on a prefix -/

/-- `vt_vals` on the first `7854` statements. -/
theorem vt_vals_at (h : VtHoldsAt 7854 rd σ) {w : List E} (hw : 16 ≤ w.length)
    (hfw : ReadsAt rd (σ (.n 11)) w) (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931)))
    (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)]) :
    σ (.n 3326) = pushTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 3705) = pullTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 4553) = countTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      (∀ t : Fin 6, σ (.n (vtCeVars.getD t 0)) =
        (ceEx t).eval (fun k => σ (.n k)) (fun i => w.getD i 0)) ∧
      σ (.n 4631) = σ (.n 4624) * σ (.n 3326) + σ (.n 4625) * σ (.n 3705) +
        σ (.n 4626) * σ (.n 4553) := by
  have hL := vt_fpw_sound hw hfw
  have hE : LoadTab.Sound rd σ (fun i => w.getD i 0) [] := fun _ hq => absurd hq (by simp)
  refine ⟨window_eval_at h hL 1505 1587 3326 pushTotalEx (by norm_num) vt_push_total,
    window_eval_at h (vt_pullTab_sound hw hfw h1 h2 hm) 1505 1892 3705 pullTotalEx (by norm_num)
      vt_pull_total,
    window_eval_at h hE 3397 876 4553 countTotalEx (by norm_num) vt_count_total, fun t => ?_, ?_⟩
  · fin_cases t
    · exact window_eval_at h hL 4374 481 5140 (ceEx 0) (by norm_num) vt_ce0
    · exact window_eval_at h hL 4862 521 5668 (ceEx 1) (by norm_num) vt_ce1
    · exact window_eval_at h hL 5391 269 5945 (ceEx 2) (by norm_num) vt_ce2
    · exact window_eval_at h hL 5668 515 6468 (ceEx 3) (by norm_num) vt_ce3
    · exact window_eval_at h hL 6191 494 6970 (ceEx 4) (by norm_num) vt_ce4
    · exact window_eval_at h hL 6693 1153 8131 (ceEx 5) (by norm_num) vt_ce5
  · have a0 := h.atom 4333 (.mul (.n 4627) (.n 4624) (.n 3326)) (by decide +kernel)
    have a1 := h.atom 4334 (.mul (.n 4628) (.n 4625) (.n 3705)) (by decide +kernel)
    have a2 := h.atom 4335 (.add (.n 4629) (.n 4627) (.n 4628)) (by decide +kernel)
    have a3 := h.atom 4336 (.mul (.n 4630) (.n 4626) (.n 4553)) (by decide +kernel)
    have a4 := h.atom 4337 (.add (.n 4631) (.n 4629) (.n 4630)) (by decide +kernel)
    simp only [Atom.Holds] at a0 a1 a2 a3 a4
    rw [a4, a2, a0, a1, a3]

/-- `vt_resolve` on the first `M` statements, `M ≥ 4273`. -/
theorem vt_resolve_at (h : VtHoldsAt M rd σ) (hM : 4273 ≤ M) :
    ∀ fuel v, σ (.n v) = σ (.n (vtResolve fuel v))
  | 0, v => rfl
  | fuel + 1, v => by
    unfold vtResolve
    split
    · next c hc =>
      have hm := List.mem_of_find?_eq_some hc
      have hv : c.2.1 = v := by simpa using List.find?_some hc
      have hok := List.all_eq_true.mp vt_copies_ok c hm
      have hc1 : c.1 + 1 ≤ 4273 := by
        have : ∀ c ∈ vtCopies, c.1 + 1 ≤ 4273 := by decide
        exact this c hm
      have := h.atom c.1 (.copy (.n c.2.1) (.n c.2.2)) (by rw [take_drop_take _ (by omega)]; exact hok)
      simp only [Atom.Holds] at this
      rw [← hv, this]
      exact vt_resolve_at h hM fuel c.2.2
    · rfl

theorem vt_eqhi_at (h : VtHoldsAt M rd σ) (hM : 4273 ≤ M) {t s k : ℕ} (ht : t < 6) (hs : s < 3)
    (hk : k < ((vtEqhiVars.getD t []).getD s []).length) :
    σ (.n (((vtEqhiVars.getD t []).getD s []).getD k 0)) =
      σ (.n (selVal.getD (eqhiSel t s k) 0 + 23)) := by
  rw [vt_resolve_at h hM 2, vt_eqhi_ok t ht s hs k hk]

/-- `vt_air` on the first `7854` statements. -/
theorem vt_air_at (h : VtHoldsAt 7854 rd σ) {n : ℕ} (τ : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t ≤ n) (hgn : σ (.n 4554) = gen ^ n)
    (htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ τ t) {cp pq : ℕ → E}
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 4639)) j (cp j))
    (hpq : ∀ k ≤ n, LoadHolds rd (σ (.n 4655)) k (pq k)) :
    ∀ t < 6, σ (.n (airAcc t)) = ((List.range (t + 1)).map fun s =>
      cp (n - τ s) * pq (τ s) * σ (.n (airCe.getD s 0))).sum := by
  have hbl : ∀ t < 6, airStmt.getD t 0 + 8 ≤ 7854 := by decide
  have hterm : ∀ t < 6, σ (.n (airQ.getD t 0 + 6)) =
      cp (n - τ t) * pq (τ t) * σ (.n (airCe.getD t 0)) := by
    intro t ht
    obtain ⟨hb, -, -⟩ := air_blocks t ht
    obtain ⟨k, hb⟩ := h.slice (airStmt.getD t 0) (airT (airQ.getD t 0) (airTau.getD t 0) (airCe.getD t 0))
      (by rw [show (airT (airQ.getD t 0) (airTau.getD t 0) (airCe.getD t 0)).length = 7 from rfl,
            take_drop_take _ (show airStmt.getD t 0 + 7 ≤ 7854 by have := hbl t ht; omega)]; exact hb)
    simp only [airT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨m0, m1, l2, m3, l4, m5, m6⟩ := hb
    rw [hgn, htau t ht] at m0
    have hq := gen_pow_cancel (hτ t ht) m0
    rw [m1, hq, loadHolds_gen_pow_mul, Nat.add_zero] at l2
    rw [m3, htau t ht, loadHolds_gen_pow_mul, Nat.add_zero] at l4
    rw [m6, m5, loadHolds_unique l2 (hcp _ (by omega)), loadHolds_unique l4 (hpq _ (hτ t ht))]
  intro t ht
  induction t with
  | zero => simpa [airAcc, airQ] using hterm 0 (by omega)
  | succ t ih =>
    obtain ⟨-, hadd, -⟩ := air_blocks (t + 1) ht
    have ha := h.atom _ _ (by rw [take_drop_take _ (by have := hbl (t + 1) ht; omega)]; exact hadd (by omega))
    simp only [Atom.Holds, Nat.add_sub_cancel] at ha
    rw [ha, ih (by omega), hterm (t + 1) ht, List.range_succ (n := t + 1), List.map_append,
      List.sum_append]
    simp

end

end
end LeanVM.Guest.B1.VerifySub
