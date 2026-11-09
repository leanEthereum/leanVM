/-
  LeanVM.Guest.B1.Tables.VtC.FWin

  The honest window `2688 ..< 6352`: on a memory holding the evaluations at the cursor, `fp_w`,
  the challenges' products and the equality prefix, every statement of the window holds of the
  honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FData
public import LeanVM.Guest.B1.Tables.VtC.FEvals

/-!
# The honest window

By kind (`vtF_cover`): what evaluation settles (`vsh_auto`); a read of `fp_w` (`vt_bufLoad`); an
evaluation's read at the cursor and its limb check (`vtF_ev`), from the evaluation's equations
(`vtF_evalGood`: its limb, tag and cells, the cells canonical); a permutation (`vtF_perm`: its
inputs canonical, the cells' and the carried capacity's, the latter a permutation's outputs or
`hcap`); a table's weight block (`vtF_air`: `g^n = g^(n-τ)·g^τ` with `g^τ` the `kappa_base` frame
variable `σ (30 + t)`, `cprod[n-τ]`, `peq[τ]`). `vtF_window`: all of them.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vtF_mem {s : Stmt} (hs : s ∈ (vtPre.drop vtFLo).take (vtFHi - vtFLo)) : s ∈ vtPre :=
  List.mem_of_mem_drop (List.mem_of_mem_take hs)

/-- A read of a word the memory holds, by membership. -/
theorem vt_readM (hl : args.length = 20) {d p : V} {off : ℕ}
    (hs : Stmt.atom (.load d p off) ∈ vtPre) (hS : Atom.load d p off ∉ vtSL) {v : E}
    (hm : LoadHolds rd (vtσ rd w args p) off v) :
    vtσ rd w args d = v ∧ VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.load d p off)) := by
  have h := vt_goodS (rd := rd) (w := w) hl hs
  simp only [fixNe, GoodS, Good] at h
  have e : vtσ rd w args d = v := by rw [h.resolve_left hS, rdAt, hm.2]; rfl
  refine ⟨e, ?_⟩
  show LoadHolds rd _ _ _
  rw [e]; exact hm

/-! ## The evaluations -/

/-- **Evaluation `k`'s equations**: its high limb, its tag, its two cells. -/
theorem vtF_evalGood (hl : args.length = 20) {k : ℕ} (hk : k < 159) :
    vtσ rd w args (.n (vtEvB k + 3)) = ofK ((vtσ rd w args (.n (vtEvB k))).limb 2) ∧
      vtσ rd w args (.n (vtEvB k + 4)) = word dsObserve 0 0 ∧
      vtσ rd w args (.n (vtEvB k + 7)) = fsPackVals (vtσ rd w args (.n (vtEvB k))) dsObserve 6 ∧
      vtσ rd w args (.n (vtEvB k + 9)) =
        fsPackVals (vtσ rd w args (.n (vtEvB k))) dsObserve 8 := by
  have g := vt_goodL (rd := rd) (w := w) hl _ _ (vtPre_drop _ ▸ vtEval_check k hk)
  simp only [vtEvB] at g ⊢
  generalize (vtEvalData.getD k (0, 0)).2 = b at g ⊢
  generalize vtσ rd w args = σ at g ⊢
  simp only [vtEvalT, fsNextT, fsPackT, List.cons_append, List.nil_append, GoodL, fixNe, GoodS,
    Good, Nat.add_assoc, Nat.reduceAdd] at g
  obtain ⟨-, glimb, g4, -, g5, g6, g7, g8, g9, -⟩ := g
  have e3 : σ (.n (b + 3)) = ofK ((σ (.n b)).limb 2) := by
    have := glimb 2 (by simp)
    simpa [limbAt] using this
  have e6 : σ (.n (b + 6)) = σ (.n (b + 5)) * σ (.n (b + 3)) := by
    simp only [V.n] at g6
    split_ifs at g6 with hc
    · exact g6
    · exact absurd ⟨by omega, by omega⟩ hc
  refine ⟨e3, g4, ?_, ?_⟩
  · rw [g7, e6, g5, e3]; rfl
  · rw [g9, g8, e3]; rfl

/-- An evaluation's cells are canonical. -/
theorem vtF_cellsCanon (hl : args.length = 20) {k : ℕ} (hk : k < 159) :
    IsCanonical128 (vtσ rd w args (.n (vtEvB k + 7))) ∧
      IsCanonical128 (vtσ rd w args (.n (vtEvB k + 9))) := by
  obtain ⟨-, -, e7, e9⟩ := vtF_evalGood (rd := rd) (w := w) hl hk
  rw [e7, e9]
  exact fsPackVals_canonical _ _

/-- The cursor's read. -/
theorem vtF_evRead (hl : args.length = 20) {evs : List E}
    (hcur : TbReadsAt rd (vtσ rd w args (.n 2625)) evs) (hevl : 159 ≤ evs.length) {k : ℕ}
    (hk : k < 159) :
    LoadHolds rd (vtσ rd w args (.n 2625)) k (evs.getD k 0) ∧
      vtσ rd w args (.n (vtEvB k)) = evs.getD k 0 := by
  have heq := vtEval_check k hk
  have hs : Stmt.atom (.load (.n (vtEvB k)) (.n 2625) k) ∈ vtPre :=
    vt_mem_slice (vtPre_drop _ ▸ heq) (by simp [vtEvalT, fsNextT, vtEvB])
  obtain ⟨hm, hr⟩ := vt_bufLoad (p := 2625) (b := 159) hl vtF_loadsBelow (by simp) hcur hevl
    (vtEvL_mem hs (fun _ _ _ h ↦ by cases h))
  exact ⟨hm, hr (not_mem_vtSL vtF_noStore.2.1 _ _)⟩

/-! ## The tables' weights -/

/-- Table `t`'s weight block's statements evaluation does not settle. -/
def vtAirRest (t : ℕ) : List Stmt :=
  [.atom (.mul (.n 2516) (.n (vtAirX t)) (.n (vtTauV t))),
    .atom (.load (.n (vtAirX t + 2)) (.n (vtAirX t + 1)) 0),
    .atom (.load (.n (vtAirX t + 4)) (.n (vtAirX t + 3)) 0)]

theorem vtAirT_rest : ∀ t < 6,
    tbStmtsEqb ((vtAirT t).filter fun s ↦ !autoB s) (vtAirRest t) = true := by
  decide +kernel

theorem vtAirX_gt : ∀ t < 6, 2629 < vtAirX t ∧ vtTauV t < vtAirX t := by decide

/-- Table `t`'s weight block's equations: `x = g^n/g^τ`, the pointers `cprod·x`, `peq·g^τ`. -/
theorem vtF_airGood (hl : args.length = 20) {t : ℕ} (ht : t < 6) :
    vtσ rd w args (.n (vtAirX t)) =
        vtσ rd w args (.n 2516) * (vtσ rd w args (.n (vtTauV t)))⁻¹ ∧
      vtσ rd w args (.n (vtAirX t + 1)) =
        vtσ rd w args (.n 2608) * vtσ rd w args (.n (vtAirX t)) ∧
      vtσ rd w args (.n (vtAirX t + 3)) =
        vtσ rd w args (.n 2629) * vtσ rd w args (.n (vtTauV t)) := by
  have g := vt_goodL (rd := rd) (w := w) hl _ _ (vtPre_drop _ ▸ vtAirT_check t ht)
  obtain ⟨hx, hτx⟩ := vtAirX_gt t ht
  set σ := vtσ rd w args with hσ
  simp only [vtAirT, GoodL, fixNe, GoodS, Good] at g
  obtain ⟨gd, gp, -, gq, -, -⟩ := g
  simp only [V.n] at gd gp gq
  split_ifs at gd with hc
  · exact absurd hc.1 (by omega)
  split_ifs at gp with hc
  swap; · exact absurd ⟨by omega, by omega⟩ hc
  split_ifs at gq with hc
  swap; · exact absurd ⟨by omega, by omega⟩ hc
  exact ⟨gd, gp, gq⟩

/-- **Table `t`'s weight block**: `g^n = x·g^τ`, and `cprod`, `peq` read at `x`, `g^τ`. -/
theorem vtF_air (hl : args.length = 20) {τs : ℕ → ℕ}
    (hkbt : ∀ t < 6, vtσ rd w args (.n (30 + t)) = gen ^ τs t) {n : ℕ}
    (hgn : vtσ rd w args (.n 2516) = gen ^ n) (hτn : ∀ t < 6, τs t ≤ n) {cp pe : ℕ → E}
    (hcp : ∀ j ≤ n, LoadHolds rd (vtσ rd w args (.n 2608)) j (cp j))
    (hpe : ∀ j ≤ n, LoadHolds rd (vtσ rd w args (.n 2629)) j (pe j)) {t : ℕ} (ht : t < 6) :
    ∀ s ∈ (vtAirT t).filter (fun s ↦ !autoB s),
      VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  have hτ : vtσ rd w args (.n (vtTauV t)) = gen ^ τs t := hkbt t ht
  have hchk := vtPre_drop _ ▸ vtAirT_check t ht
  obtain ⟨gd, gp, gq⟩ := vtF_airGood (rd := rd) (w := w) hl ht
  set σ := vtσ rd w args with hσ
  have hτ0 : gen ^ τs t ≠ 0 := pow_ne_zero _ gen_ne_zero
  have ex : σ (.n (vtAirX t)) = gen ^ (n - τs t) := by
    rw [gd, hgn, hτ, ← pow_sub₀ _ gen_ne_zero (hτn t ht)]
  have hs : ∀ s ∈ vtAirT t, s ∈ vtPre := fun s hs' ↦ vt_mem_slice (blk := vtAirT t) hchk hs'
  have hcpL : LoadHolds rd (σ (.n (vtAirX t + 1))) 0 (cp (n - τs t)) := by
    rw [gp, ex, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hcp _ (by omega)
  have hpeL : LoadHolds rd (σ (.n (vtAirX t + 3))) 0 (pe (τs t)) := by
    rw [gq, hτ, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hpe _ (hτn t ht)
  have hfilt := tbStmtsEqb_sound (vtAirT_rest t ht)
  rw [hfilt]
  intro s hs'
  simp only [vtAirRest, List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl | rfl
  · show σ (.n 2516) = σ (.n (vtAirX t)) * σ (.n (vtTauV t))
    rw [gd, hτ, mul_assoc, inv_mul_cancel₀ hτ0, mul_one]
  · have hm := hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hS := not_mem_vtSL (vtF_noStore.2.2 t ht).1 (.n (vtAirX t + 2)) 0
    exact (vt_readM (rd := rd) (w := w) hl hm hS hcpL).2
  · have hm := hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
    have hS := not_mem_vtSL (vtF_noStore.2.2 t ht).2 (.n (vtAirX t + 4)) 0
    exact (vt_readM (rd := rd) (w := w) hl hm hS hpeL).2

/-- Table `t`'s weight pointers: `cprod·g^(n-τ)` and `peq·g^τ`. -/
theorem vtF_airVals (hl : args.length = 20) {τs : ℕ → ℕ}
    (hkbt : ∀ t < 6, vtσ rd w args (.n (30 + t)) = gen ^ τs t) {n : ℕ}
    (hgn : vtσ rd w args (.n 2516) = gen ^ n) (hτn : ∀ t < 6, τs t ≤ n) {t : ℕ} (ht : t < 6) :
    vtσ rd w args (.n (vtAirX t + 1)) = vtσ rd w args (.n 2608) * gen ^ (n - τs t) ∧
      vtσ rd w args (.n (vtAirX t + 3)) = vtσ rd w args (.n 2629) * gen ^ τs t := by
  have hτ : vtσ rd w args (.n (vtTauV t)) = gen ^ τs t := hkbt t ht
  obtain ⟨gd, gp, gq⟩ := vtF_airGood (rd := rd) (w := w) hl ht
  refine ⟨?_, by rw [gq, hτ]⟩
  rw [gp, gd, hgn, hτ, ← pow_sub₀ _ gen_ne_zero (hτn t ht)]

/-! ## An evaluation's statements -/

/-- **Evaluation `k`'s read and limb check hold.** -/
theorem vtF_ev (hl : args.length = 20) {evs : List E}
    (hcur : TbReadsAt rd (vtσ rd w args (.n 2625)) evs) (hevl : 159 ≤ evs.length) {k : ℕ}
    (hk : k < 159) :
    ∀ s ∈ vtEvRest k, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  obtain ⟨hm, hb⟩ := vtF_evRead (w := w) hl hcur hevl hk
  obtain ⟨e3, e4, -, -⟩ := vtF_evalGood (rd := rd) (w := w) hl hk
  intro s hs
  simp only [vtEvRest, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · show LoadHolds rd _ _ _
    rw [hb]; exact hm
  · show IsInK _ ∧ IsInK _
    rw [e3, e4, word_eOfNat]
    exact ⟨ofK_isInK _, eOfNat_isInK _⟩

/-! ## The permutations -/

set_option maxRecDepth 100000 in
/-- Permutation `j`'s outputs are canonical. -/
theorem vtF_permOut (hl : args.length = 20) {j : ℕ} (hj : j < 39) {i : ℕ} (hi : i < 13) :
    IsCanonical128 (vtσ rd w args (.n ((vtPermData.getD j (0, 0)).2 + i))) := by
  have g := vt_goodAt (rd := rd) (w := w) hl _ _ (vtPerm_check j hj)
  simp only [vtPermT, keccakA, fixNe, GoodS, Good] at g
  generalize (vtPermData.getD j (0, 0)).2 = o at g ⊢
  have := g.2.2 ⟨i, hi⟩ (by simp [lyOuts]; exact hi)
  simp only [lyOuts, List.getElem_map, List.getElem_range] at this
  rw [this]
  exact canon_cellsOfState _ _ _

/-- **Permutation `j` holds**, on canonical carried capacity. -/
theorem vtF_perm (hl : args.length = 20)
    (hcap : ∀ i < 5, IsCanonical128 (vtσ rd w args (.n (2620 + i)))) {j : ℕ} (hj : j < 39) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args) (vtPermT j) := by
  have g := vt_goodAt (rd := rd) (w := w) hl _ _ (vtPerm_check j hj)
  simp only [vtPermT, keccakA, fixNe, GoodS] at g
  have hcan : ∀ v ∈ ((List.range 4).flatMap fun i ↦ [V.n (vtEvB (4 * j + i) + 7),
      .n (vtEvB (4 * j + i) + 9)]) ++ vtPermCap j, IsCanonical128 (vtσ rd w args v) := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨i, hi, hv⟩ := List.mem_flatMap.mp hv
      have hk : 4 * j + i < 159 := by simp at hi; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (vtF_cellsCanon (rd := rd) (w := w) hl hk).1
      · exact (vtF_cellsCanon (rd := rd) (w := w) hl hk).2
    · unfold vtPermCap at hv
      split_ifs at hv with h0
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
        exact hcap i (by simpa using hi)
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
        have := vtF_permOut (rd := rd) (w := w) hl (j := j - 1) (by omega) (i := 8 + i)
          (by simp at hi; omega)
        rwa [← Nat.add_assoc] at this
  refine holds_of_good (S := vtSL) (w := w) g fun c ↦ ?_
  obtain ⟨hl13, -, -⟩ := g
  simp only [cells13]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hl13]; exact c.isLt)]
  simp only [List.getElem_map]
  exact hcan _ (List.getElem_mem _)

/-! ## The window -/

/-- **The honest window**: on a memory holding the evaluations `evs` at the cursor, `fp_w`'s first
16 words, the tables' `g^τ` in `kappa_base`'s frame variables, `n ≥ τ` with `g^n`, the
challenges' products `cp` and the equality prefix `pe` up to `n`, and a canonical carried
capacity, every statement of `2688 ..< 6352` holds. -/
theorem vtF_window (hl : args.length = 20) {evs : List E} (hevl : 159 ≤ evs.length)
    (hcur : TbReadsAt rd (vtσ rd w args (.n 2625)) evs)
    {W : List E} (hW : TbReadsAt rd (vtσ rd w args (.n 13)) W) (hWl : 16 ≤ W.length)
    {τs : ℕ → ℕ} (hkbt : ∀ t < 6, vtσ rd w args (.n (30 + t)) = gen ^ τs t)
    {n : ℕ} (hgn : vtσ rd w args (.n 2516) = gen ^ n) (hτn : ∀ t < 6, τs t ≤ n)
    {cp pe : ℕ → E} (hcp : ∀ j ≤ n, LoadHolds rd (vtσ rd w args (.n 2608)) j (cp j))
    (hpe : ∀ j ≤ n, LoadHolds rd (vtσ rd w args (.n 2629)) j (pe j))
    (hcap : ∀ i < 5, IsCanonical128 (vtσ rd w args (.n (2620 + i)))) :
    ∀ s ∈ (vtPre.drop vtFLo).take (vtFHi - vtFLo),
      VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  intro s hs
  cases ha : autoB s
  · cases hr : rdFpw s
    · have hf : s ∈ vtFTags.flatMap vtFTagT := by
        rw [← tbStmtsEqb_sound vtF_cover]
        exact List.mem_filter.mpr ⟨hs, by simp [ha, hr]⟩
      obtain ⟨q, hq, hsq⟩ := List.mem_flatMap.mp hf
      rcases vtFTags_spec q hq with ⟨h0, hk⟩ | ⟨h1, hj⟩ | ⟨h23, ht⟩
      · obtain ⟨a, k⟩ := q
        simp only at h0 hk
        subst h0
        exact vtF_ev hl hcur hevl hk s hsq
      · obtain ⟨a, j⟩ := q
        simp only at h1 hj
        subst h1
        simp only [vtFTagT, List.mem_cons, List.not_mem_nil, or_false] at hsq
        subst hsq
        exact vtF_perm hl hcap hj
      · obtain ⟨a, t⟩ := q
        simp only at h23 ht
        subst h23
        exact vtF_air hl hkbt hgn hτn hcp hpe ht s hsq
    · match s, hr with
      | .atom (.load d (.n 13) off), _ =>
        obtain ⟨hm, hrd⟩ := vt_bufLoad (p := 13) (b := 16) hl vtF_loadsBelow (by simp) hW hWl
          (vtEvL_mem (vtF_mem hs) (fun _ _ _ h ↦ by cases h))
        show LoadHolds rd _ _ _
        rw [hrd (not_mem_vtSL vtF_noStore.1 _ _)]
        exact hm
  · exact vsh_auto hl (vtF_mem hs) ha

end

end
end LeanVM.Guest.B1.Tables
