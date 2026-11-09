/-
  LeanVM.Guest.B1.VerifySub.H.Regions

  Every callee of `verify_sub` on an honest child reads slices of the caller's words and of the
  own buffers (the terminal also `certify_placement`'s and `open_stacked`'s results).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Lin

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem tauList_eq : Tables.vtTauList S.H.τ = S.hs := by
  apply List.ext_getElem (by simp [Tables.vtTauList, S.hs_length])
  intro t h1 h2
  simp only [Tables.vtTauList, List.getElem_map, List.getElem_range]
  rw [← List.getD_eq_getElem _ 0 h2]
  rfl

theorem hs_count (hbl : bytecode.length = 2 ^ 23) : S.hs.map Hints.count = S.hs.map (gen ^ ·) :=
  List.map_congr_left fun x hx ↦ count_eq_gen (by have := S.hh29 hbl x hx; omega)

theorem dimsW_eq (hbl : bytecode.length = 2 ^ 23) : S.H.dimsW = vsDimsW S.logMem S.hs := by
  rw [Tables.VtHonest.dimsW, vsDimsW, S.tauList_eq, S.hs_count hbl]; rfl

theorem curW_eq (hbl : bytecode.length = 2 ^ 23) : S.H.curW = S.xsT := (S.H_run hbl).2.1.symm

/-- **The output lanes in the stream**, at `col_eval_words·g^107`. -/
theorem lanes_stream (hbl : bytecode.length = 2 ^ 23) :
    ((vsStreamW c.proof.stream).drop (10 + S.xsG.length + (5 + 3 * S.H.n + 107))).take
      S.outs.length = S.outs ∧
      10 + S.xsG.length + (5 + 3 * S.H.n + 107) + S.outs.length ≤ (vsStreamW c.proof.stream).length := by
  have hol := (S.lanes hbl).2.2
  have hpl := S.poolW_length hbl
  have hlt := S.stream_pool_lt hbl (j := 161) (by norm_num)
  have hsl : c.proof.stream.length ≤ (vsStreamW c.proof.stream).length := by
    simp [vsStreamW]
  refine ⟨List.ext_getElem (by simp [hol]; omega) fun k h1 h2 ↦ ?_, by rw [hol]; omega⟩
  simp only [List.length_take, List.length_drop] at h1
  have hk : k < 25 := by rw [hol] at h2; exact h2
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0,
    show 10 + S.xsG.length + (5 + 3 * S.H.n + 107) + k =
      10 + S.xsG.length + (5 + (3 * S.H.n + (112 + k - 5))) by omega,
    S.stream_pool hbl (by omega) (by omega)]
  simp only [ChildSegs.outs, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by omega)]

end ChildSegs

theorem expTableWords_sq : (expTableWords.drop 0).take 34 = Tables.gSquaresList := by
  apply List.ext_getElem (by simp [expTableWords, length_etWordsN, Tables.gSquaresList])
  intro k h1 h2
  simp only [List.length_take, List.length_drop] at h1
  have hk : k < 34 := by simpa [Tables.gSquaresList] using h2
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, Nat.zero_add,
    expTableWords_getD k (by omega), etListK_sq k hk, ofK_pow, ← gen_eq_ofK]
  simp [Tables.gSquaresList]

theorem expTableWords_rank : (expTableWords.drop 178).take 34 = Tables.rankKeysList := by
  apply List.ext_getElem (by simp [expTableWords, length_etWordsN, Tables.rankKeysList])
  intro k h1 h2
  have hk : k < 34 := by simpa [Tables.rankKeysList] using h2
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0,
    expTableWords_getD _ (by omega), etListK_rank k hk, ofK_pow, ← gen_eq_ofK]
  simp [Tables.rankKeysList, Tables.rankStride]

/-- **The callees but the terminal read the caller's words and the own buffers.** -/
theorem kid_lin_sub {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b : ℕ) {sqE : ℕ} {Lin : Main.Layout}
    (hexpL : ∀ q ∈ log2Lin sqE, q ∈ Lin) {j : ℕ} (hj : j < 12)
    (pv : List (List E × Main.Layout)) :
    ∀ q ∈ ((S.kids (bases b (vsSizes S.μ)) sqE).getD j noKid pv).Lin,
      SubOf Lin q ∨ SubOf (bufL b (vsSizes S.μ) S.ownW) q := by
  set bs := bases b (vsSizes S.μ) with hbs
  have own : ∀ i < 13, SubOf (bufL b (vsSizes S.μ) S.ownW) (vb bs i, S.ownW.getD i []) :=
    fun i hi ↦ subOf_self (vs_own_mem S b hi)
  have slice : ∀ i < 13, ∀ (off : ℕ) (ys : List E), off + ys.length ≤ (S.ownW.getD i []).length →
      ys = ((S.ownW.getD i []).drop off).take ys.length →
      SubOf (bufL b (vsSizes S.μ) S.ownW) (vb bs i + off, ys) :=
    fun i hi off ys h1 h2 ↦ subOf_slice (vs_own_mem S b hi) off ys h1 h2
  have hsqm : (sqE, expTableWords) ∈ Lin := hexpL _ (by simp [log2Lin])
  have hsq : SubOf Lin (sqE, expTableWords) := subOf_self hsqm
  have hel : expTableWords.length = 236 := by simp [expTableWords, length_etWordsN]
  obtain ⟨sG, sT, sK, sW, sL⟩ := S.stream_segs
  have hl1 : (S.ownW.getD 1 []) = vsStreamW c.proof.stream := rfl
  interval_cases j
  · intro q hq; simp [ChildSegs.kids] at hq
  · intro q hq; simp [ChildSegs.kids] at hq
  · intro q hq; exact Or.inl (subOf_self (hexpL q hq))
  · intro q hq; simp [ChildSegs.kids] at hq
  · intro q hq; simp [ChildSegs.kids] at hq
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (slice 1 (by norm_num) 10 S.xsG (by rw [hl1]; omega) (by rw [hl1, sG]))
    · exact Or.inr (own 5 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, Tables.VtHonest.linL,
      ChildSegs.vtB, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [S.curW_eq hbl]
      have := slice 1 (by norm_num) (10 + S.xsG.length) S.xsT (by rw [hl1]; omega) (by rw [hl1, sT])
      simp only [← Nat.add_assoc] at this
      exact Or.inr this
    · exact Or.inr (own 5 (by norm_num))
    · rw [S.dimsW_eq hbl]; exact Or.inr (own 3 (by norm_num))
    · exact Or.inr (own 2 (by norm_num))
    · exact Or.inl hsq
    · exact Or.inr (own 7 (by norm_num))
    · exact Or.inr (own 0 (by norm_num))
    · exact Or.inr (own 8 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    obtain ⟨-, hopl, hkpl, -, -⟩ := S.runK' hbl
    have hτ := S.τ_bounds hbl
    have hzl : (zvW S.op S.kpt).length = 39 + S.kpt.length := by simp [zvW]; omega
    obtain ⟨hLs, hLl⟩ := S.lanes_stream hbl
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · have := slice 1 (by norm_num) (10 + S.xsG.length + S.xsT.length) S.xsK
        (by rw [hl1]; omega) (by rw [hl1, sK])
      simp only [← Nat.add_assoc] at this
      exact Or.inr this
    · exact Or.inr (own 8 (by norm_num))
    · have := slice 1 (by norm_num) (10 + S.xsG.length + (5 + 3 * S.H.n + 107)) S.outs
        (by rw [hl1]; exact hLl) (by rw [hl1, hLs])
      rw [show vb bs 1 + (10 + S.xsG.length + (5 + 3 * S.H.n + 107)) = S.cL bs by
        simp only [ChildSegs.cL, ChildSegs.cT, vcG]; omega] at this
      exact Or.inr this
    · have := slice 9 (by norm_num) 0 S.op (by show 0 + _ ≤ (zvW S.op S.kpt).length; rw [hzl]; omega)
        (by show S.op = ((zvW S.op S.kpt).drop 0).take S.op.length; simp [zvW])
      rw [Nat.add_zero] at this
      exact Or.inr this
    · exact Or.inr (slice 9 (by norm_num) qkeccakVarsCap S.kpt
        (by show 39 + _ ≤ (zvW S.op S.kpt).length; rw [hzl])
        (by
          show S.kpt = ((zvW S.op S.kpt).drop 39).take S.kpt.length
          have hk : (zvW S.op S.kpt).drop 39 = S.kpt :=
            List.drop_left' (l₁ := S.op ++ List.replicate (39 - S.op.length) 0) (by simp; omega)
          rw [hk, List.take_length]))
    · exact Or.inr (own 10 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (own 10 (by norm_num))
    · exact Or.inr (own 11 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, Tables.cpLin,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have e : 1 :: gen ^ S.logMem :: S.hs.map (gen ^ ·) = S.ownW.getD 4 [] := by
        show _ = vsKbW S.logMem S.hs
        rw [vsKbW, S.hs_count hbl]
      rw [e]; exact Or.inr (own 4 (by norm_num))
    · have := subOf_slice hsqm 0 Tables.gSquaresList
        (by simp [Tables.gSquaresList, hel])
        (by rw [show Tables.gSquaresList.length = 34 by simp [Tables.gSquaresList], expTableWords_sq])
      rw [Nat.add_zero] at this
      exact Or.inl this
    · exact Or.inl (subOf_slice hsqm 178 Tables.rankKeysList
        (by simp [Tables.rankKeysList, hel])
        (by rw [show Tables.rankKeysList.length = 34 by simp [Tables.rankKeysList], expTableWords_rank]))
  · intro q hq; exact Or.inl (subOf_self (hexpL q hq))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    have := slice 1 (by norm_num) (10 + S.xsG.length + S.xsT.length + S.xsK.length) S.xsW
      (by rw [hl1]; omega) (by rw [hl1, sW])
    simp only [← Nat.add_assoc] at this
    exact Or.inr this

end
end LeanVM.Guest.B1.VerifySub
