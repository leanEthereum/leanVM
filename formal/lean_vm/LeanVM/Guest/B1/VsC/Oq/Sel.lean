/-
  LeanVM.Guest.B1.VsC.Oq.Sel

  What an iteration of `opening_queries`' loop is at its honest valuation, before any memory: its
  `match`es' arms, its pops, its values.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.PlacedL
public import LeanVM.Guest.B1.VsC.Oq.Pops

/-!
# An iteration at its honest valuation, memory-free

The archive's `oqIter1_at`, `oqIter0_at` give an iteration's values together with its statements
holding on one memory. The placed composition (`callAtA_nodeL`) fixes the valuation before the
memory, so its path and its pops come first, from the valuation alone:

* `oqQE`, `QD.queryPops_vals`: a query's entries at its honest values, its row's cells and its
  siblings' (`oqQE` reads only the shape and the witness);
* `QD.winSel`: its windows' words are arms of their matches;
* `oqQueryT_match`, `oqQuery_matchOk`, `oqLoop1A_matchOk`, `oqLoop0A_matchOk`: every `match` of a
  query (of an iteration) is a window of its path, so its selector names an arm;
* `oqIter1_vals`, `oqIter0_vals`: an iteration's parameters, its queries' values, its pointers and
  its guard, from `oqIter1F` (`oqIter0F`) alone.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A query's entries -/

/-- **A query's entries**: its row's cells, its siblings' cells. -/
def oqQE (s : Oq) (w : QW) : List Pop :=
  ("merkle_leaf_rows", (oqQD s 0 0 true 0 0 0 0 [] [] w).rowVals) :: (oqQD s 0 0 true 0 0 0 0 [] [] w).wd.wpPops

theorem oqQE_eq (s : Oq) (cd b : ℕ) (emit : Bool) (pr : ℕ) (bp cap flags : E) (rounds : List FoldRound)
    (hsv : List E) (w : QW) :
    ("merkle_leaf_rows", (oqQD s cd b emit pr bp cap flags rounds hsv w).rowVals) ::
      (oqQD s cd b emit pr bp cap flags rounds hsv w).wd.wpPops = oqQE s w := rfl

namespace QD

variable (d : QD) {σ : Val}

theorem fo_lt_e : d.fo < d.e := lt_of_le_of_lt d.fo_le_v d.v_lt_e

/-- **At the honest values a query's entries** are its row's cells and its siblings'. -/
theorem queryPops_vals (hv : d.Hv σ) :
    queryPops σ d.s d.b d.emit = ("merkle_leaf_rows", d.rowVals) :: d.wd.wpPops := by
  have he := d.ch_lt_e
  have hfe := d.fo_lt_e
  have hfo := d.fo_eq
  have hl := d.wd.vals_length
  have hI : d.b + d.s.I ≤ d.ch := by simp only [QD.ch, oqCh, oqKL, oqK1]; split_ifs <;> omega
  have hb := d.b_le_ch
  simp only [queryPops, rowPop, WD.wpPops, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩
  · rw [QD.rowVals]
    exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [hv _ (by omega) (by omega), d.val_row this]
  · exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      have hl' : d.wd.vals.length = 2 * d.s.pd + winOff d.s (oqNpw d.s) + 9 := hl
      rw [show oqCh d.s d.b d.emit = d.ch from rfl, hv _ (by omega) (by omega), d.val_sib this]

/-- **At the honest values a query's windows' words** are arms of their matches. -/
theorem winSel (hv : d.Hv σ) : WinSel σ d.s d.ch := by
  intro i hi
  have h1 := winOff_succ_le (s := d.s) hi
  have hfe := d.fo_lt_e
  have hb := d.b_le_ch
  have h5 : d.fo = oqCq d.s d.ch + 9 := rfl
  have h6 : oqCq d.s d.ch = d.ch + 2 * d.s.pd + winOff d.s (oqNpw d.s) := by rw [oqCq, oqWk_eq]
  have h7 : oqWk d.s d.ch i = d.ch + 2 * d.s.pd + winOff d.s i := oqWk_eq _ _ _
  have hsz : 0 < winSz d.s i := by unfold winSz; omega
  refine ⟨d.wd.wv i, (qwVal_path hi d.q).1, ?_⟩
  rw [show oqWk d.s d.ch i = oqWk d.s d.ch i + 0 from rfl, hv _ (by omega) (by omega),
    d.val_win hi hsz, WD.winV, ite_eq_left rfl, gen_pow_eq_ofK]

end QD

/-! ## The `match`es of a query -/

theorem not_match_of_atoms {ss : List Stmt} (h : AllAtoms ss) {y : V} {arms : List (List Stmt)} :
    Stmt.match_ y arms ∉ ss := fun hm => by
  obtain ⟨a, ha⟩ := h _ hm
  cases ha

/-- **A `match` of a query is one of its path's windows.** -/
theorem oqQueryT_match {s : Oq} {x bp cap flags coefs hs : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    {y : V} {arms : List (List Stmt)} (h : Stmt.match_ y arms ∈ oqQueryT s x bp cap flags coefs hs b emit pr) :
    ∃ i < oqNpw s, y = .n (oqWk s (oqCh s b emit) i) ∧ arms.length = 2 ^ oqWw s i := by
  have hP : AllAtoms (oqPrepT s b ++ (if emit then oqPadT (oqK1 s b) else []) ++
      oqLeafT s b (oqPr s b emit pr) (oqKL s b emit)) :=
    allAtoms_append (allAtoms_append (oqPrepT_atoms _ _)
      (by split <;> first | exact oqPadT_atoms _ | exact allAtoms_nil)) (oqLeafT_atoms _ _ _ _)
  have hQ : AllAtoms (oqFoldT s coefs x b (oqFo s b emit) ++
      (if s.final = 1 then oqFinT s x hs (oqVal s (oqFo s b emit)) else [])) :=
    allAtoms_append (oqFoldT_atoms _ _ _ _ _)
      (by split <;> first | exact oqFinT_atoms _ _ _ _ | exact allAtoms_nil)
  rw [QD.oqQueryT_eq] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact absurd h (not_match_of_atoms hP)
    · unfold oqWalkT at h
      rcases List.mem_append.mp h with h | h
      · unfold oqPathT at h
        rcases List.mem_append.mp h with h | h
        · simp at h
        · obtain ⟨l, hl, hm⟩ := List.mem_flatten.mp h
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
          simp only [oqWinT, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
            Stmt.match_.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact ⟨i, List.mem_range.mp hi, rfl, by simp⟩
      · exact absurd h (not_match_of_atoms (oqCapT_atoms _ _ _ _ _ _))
  · exact absurd h (not_match_of_atoms hQ)

/-- A window's word naming an arm makes its `match` name one. -/
theorem matchOk_of_winSel {σ : Val} {s : Oq} {ch : ℕ} (hw : WinSel σ s ch) {i : ℕ} (hi : i < oqNpw s)
    {arms : List (List Stmt)} (hl : arms.length = 2 ^ oqWw s i) :
    MatchOk σ (.match_ (.n (oqWk s ch i)) arms) := by
  obtain ⟨k, hk, he⟩ := hw i hi
  have h6 : 2 ^ oqWw s i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) (oqWw_le s i)
  exact ⟨by rw [hl]; exact le_trans h6 (by norm_num), k, by rw [hl]; exact hk, he⟩

/-- **Every `match` of a query names an arm**, its windows' words arms of their matches. -/
theorem oqQuery_matchOk {σ : Val} {s : Oq} {x bp cap flags coefs hs : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hw : WinSel σ s (oqCh s b emit)) : ∀ st ∈ oqQueryT s x bp cap flags coefs hs b emit pr, MatchOk σ st := by
  intro st hst
  cases st with
  | match_ y arms =>
    obtain ⟨i, hi, rfl, hl⟩ := oqQueryT_match hst
    exact matchOk_of_winSel hw hi hl
  | _ => trivial

/-- **Every `match` of a level-0 iteration names an arm.** -/
theorem oqLoop1A_matchOk {σ : Val} {s : Oq} (h1 : WinSel σ s (oqCh s 15 true))
    (h2 : WinSel σ s (oqCh s (oqE1 s + 2) false)) : ∀ st ∈ oqLoop1A s, MatchOk σ st := by
  intro st hst
  cases st with
  | match_ y arms =>
    unfold oqLoop1A at hst
    dsimp only at hst
    rcases List.mem_append.mp hst with hst | hG
    · rcases List.mem_append.mp hst with hst | hC
      · rcases List.mem_append.mp hst with hst | hQ2
        · rcases List.mem_append.mp hst with hst | hB
          · rcases List.mem_append.mp hst with hA | hQ1
            · simp at hA
            · exact oqQuery_matchOk h1 _ hQ1
          · simp at hB
        · exact oqQuery_matchOk h2 _ hQ2
      · split at hC <;> simp at hC
    · simp [oqGuardA] at hG
  | _ => trivial

/-- **Every `match` of a deeper iteration names an arm.** -/
theorem oqLoop0A_matchOk {σ : Val} {s : Oq} (h1 : WinSel σ s (oqCh s 14 true)) :
    ∀ st ∈ oqLoop0A s, MatchOk σ st := by
  intro st hst
  cases st with
  | match_ y arms =>
    unfold oqLoop0A at hst
    dsimp only at hst
    rcases List.mem_append.mp hst with hst | hG
    · rcases List.mem_append.mp hst with hst | hC
      · rcases List.mem_append.mp hst with hA | hQ
        · simp at hA
        · exact oqQuery_matchOk h1 _ hQ
      · split at hC <;> simp at hC
    · simp [oqGuardA] at hG
  | _ => trivial

/-! ## An iteration's values -/

/-- **A level-0 iteration's values at `oqIter1F`**, memory-free: its parameters, its queries' honest
values, their points' and windows' pointers, the chain's pointers and the guard. -/
theorem oqIter1_vals {s : Oq} {cd j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w1 w2 : QW} {bp1 bp2 v : E} {σ : Val}
    (hσ : ∀ i, σ (.n i) = oqIter1F s
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      (oqQD s cd 15 true 0 bp1 cap flags rounds hsv w1)
      (oqQD s cd (oqE1 s + 2) false (oqK1 s 15) bp2 cap flags rounds hsv w2) v i) :
    oqLoopParams.map σ = [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] ∧
      (oqQD s cd 15 true 0 bp1 cap flags rounds hsv w1).Hv σ ∧
      (oqQD s cd (oqE1 s + 2) false (oqK1 s 15) bp2 cap flags rounds hsv w2).Hv σ ∧
      σ (.n 11) = positions * gen ^ (2 * j) ∧ σ (.n 12) = qptrs * gen ^ (2 * j) ∧
      σ (.n 14) = bp1 ∧ σ (.n (oqE1 s + 1)) = bp2 ∧
      (s.final ≠ 1 → σ (.n (oqC1 s)) = ch * gen ^ j ∧ σ (.n (oqC1 s + 6)) = ch * gen ^ j) ∧
      σ (.n (oqG1 s + 2)) = gen ^ j * gen + N ∧ σ (.n (oqG1 s + 4)) = gen ^ j * gen := by
  set D1 := oqQD s cd 15 true 0 bp1 cap flags rounds hsv w1 with hD1
  set D2 := oqQD s cd (oqE1 s + 2) false (oqK1 s 15) bp2 cap flags rounds hsv w2 with hD2
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  have hb1' : D1.b = 15 := rfl
  have he1' : D1.e = oqE1 s := rfl
  have hb2' : D2.b = oqE1 s + 2 := rfl
  have he2' : D2.e = oqC1 s := rfl
  have i1 := D1.b_le_ch
  have i2 := D1.ch_lt_e
  have i3 := D2.b_le_ch
  have i4 := D2.ch_lt_e
  have hjj : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter1F, hi, ↓reduceIte]
  have e11 : σ (.n 11) = positions * gen ^ (2 * j) := by rw [hσ, ← hjj]; simp [oqIter1F, hargs]
  have e12 : σ (.n 12) = qptrs * gen ^ (2 * j) := by rw [hσ, ← hjj]; simp [oqIter1F, hargs]
  have e14 : σ (.n 14) = bp1 := by rw [hσ]; simp [oqIter1F, hD1, oqQD]
  have eQ1 : D1.Hv σ := fun i h1 h2 => by
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 10 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
      show i ≠ 12 by omega, show i ≠ 13 by omega, show i ≠ 14 by omega,
      show i < oqE1 s by omega, ↓reduceIte]
  have eB2 : σ (.n (oqE1 s + 1)) = bp2 := by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqE1 s + 1 < 10 by omega, show oqE1 s + 1 ≠ 10 by omega,
      show oqE1 s + 1 ≠ 11 by omega, show oqE1 s + 1 ≠ 12 by omega, show oqE1 s + 1 ≠ 13 by omega,
      show oqE1 s + 1 ≠ 14 by omega, show ¬ oqE1 s + 1 < oqE1 s by omega,
      show oqE1 s + 1 ≠ oqE1 s by omega, ↓reduceIte]
    rfl
  have eQ2 : D2.Hv σ := fun i h1 h2 => by
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 10 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
      show i ≠ 12 by omega, show i ≠ 13 by omega, show i ≠ 14 by omega,
      show ¬ i < oqE1 s by omega, show i ≠ oqE1 s by omega, show i ≠ oqE1 s + 1 by omega,
      show i < oqC1 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC1 s + o)) = (oqIter1C s.final (gen ^ j) N ch mu v
      (oqResV s rounds w1) (oqResV s rounds w2)).getD o 0 := fun o => by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqC1 s + o < 10 by omega, show oqC1 s + o ≠ 10 by omega,
      show oqC1 s + o ≠ 11 by omega, show oqC1 s + o ≠ 12 by omega, show oqC1 s + o ≠ 13 by omega,
      show oqC1 s + o ≠ 14 by omega,
      show ¬ oqC1 s + o < oqE1 s by omega, show oqC1 s + o ≠ oqE1 s by omega,
      show oqC1 s + o ≠ oqE1 s + 1 by omega, show ¬ oqC1 s + o < oqC1 s by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rfl
  have eG : ∀ o < 5, σ (.n (oqG1 s + o)) = (oqGuardV (gen ^ j) N).getD o 0 := fun o _ ↦ by
    rw [oqG1_eq, Nat.add_assoc, eC, oqIter1C_guard]
  obtain ⟨-, eG2, eG4⟩ := oqGuardA_okC (rd := fun _ => none) (C := anyCall) (eP 0 (by omega))
    (eP 1 (by omega)) eG
  have eS : s.final ≠ 1 → ∀ o < 7, σ (.n (oqC1 s + o)) =
      (oqStep1V (gen ^ j) ch mu v (oqResV s rounds w1) (oqResV s rounds w2)).getD o 0 :=
    fun hf o ho ↦ by rw [eC, oqIter1C_step hf _ _ _ _ _ _ _ ho]
  refine ⟨?_, eQ1, eQ2, e11, e12, e14, eB2, fun hf ↦ ⟨?_, ?_⟩, eG2, eG4⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega), eP 8 (by omega), eP 9 (by omega)]
    rfl
  · have := eS hf 0 (by omega); rw [Nat.add_zero] at this; exact this
  · exact eS hf 6 (by omega)

/-- **A deeper iteration's values at `oqIter0F`**, memory-free. -/
theorem oqIter0_vals {s : Oq} {cd j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w : QW} {bp v : E} {σ : Val}
    (hσ : ∀ i, σ (.n i) = oqIter0F s
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      (oqQD s cd 14 true 0 bp cap flags rounds hsv w) v i) :
    oqLoopParams.map σ = [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] ∧
      (oqQD s cd 14 true 0 bp cap flags rounds hsv w).Hv σ ∧
      σ (.n 10) = positions * gen ^ j ∧ σ (.n 12) = qptrs * gen ^ j ∧ σ (.n 13) = bp ∧
      (s.final ≠ 1 → σ (.n (oqC0 s)) = ch * gen ^ j ∧ σ (.n (oqC0 s + 4)) = ch * gen ^ j) ∧
      σ (.n (oqG0 s + 2)) = gen ^ j * gen + N ∧ σ (.n (oqG0 s + 4)) = gen ^ j * gen := by
  set D := oqQD s cd 14 true 0 bp cap flags rounds hsv w with hD
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  have hb' : D.b = 14 := rfl
  have he' : D.e = oqC0 s := rfl
  have i1 := D.b_le_ch
  have i2 := D.ch_lt_e
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter0F, hi, ↓reduceIte]
  have e10 : σ (.n 10) = positions * gen ^ j := by rw [hσ]; simp [oqIter0F, hargs]
  have e12 : σ (.n 12) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter0F, hargs]
  have e13 : σ (.n 13) = bp := by rw [hσ]; simp [oqIter0F, hD, oqQD]
  have eQ : D.Hv σ := fun i h1 h2 => by
    rw [hσ]
    simp only [oqIter0F, show ¬ i < 10 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
      show i ≠ 12 by omega, show i ≠ 13 by omega, show i < oqC0 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC0 s + o)) = (oqIter0C s.final (gen ^ j) N ch mu v
      (oqResV s rounds w)).getD o 0 := fun o => by
    rw [hσ]
    simp only [oqIter0F, show ¬ oqC0 s + o < 10 by omega, show oqC0 s + o ≠ 10 by omega,
      show oqC0 s + o ≠ 11 by omega, show oqC0 s + o ≠ 12 by omega, show oqC0 s + o ≠ 13 by omega,
      show ¬ oqC0 s + o < oqC0 s by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  have eG : ∀ o < 5, σ (.n (oqG0 s + o)) = (oqGuardV (gen ^ j) N).getD o 0 := fun o _ ↦ by
    rw [oqG0_eq, Nat.add_assoc, eC, oqIter0C_guard]
  obtain ⟨-, eG2, eG4⟩ := oqGuardA_okC (rd := fun _ => none) (C := anyCall) (eP 0 (by omega))
    (eP 1 (by omega)) eG
  have eS : s.final ≠ 1 → ∀ o < 5, σ (.n (oqC0 s + o)) =
      (oqStep0V (gen ^ j) ch mu v (oqResV s rounds w)).getD o 0 :=
    fun hf o ho ↦ by rw [eC, oqIter0C_step hf _ _ _ _ _ _ ho]
  refine ⟨?_, eQ, e10, e12, e13, fun hf ↦ ⟨?_, ?_⟩, eG2, eG4⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega), eP 8 (by omega), eP 9 (by omega)]
    rfl
  · have := eS hf 0 (by omega); rw [Nat.add_zero] at this; exact this
  · exact eS hf 4 (by omega)

end
end LeanVM.Guest.B1
