/-
  LeanVM.Guest.B1.Whir.CLr

  `residual_batch` and `level_residual`, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CResQ
public import LeanVM.Guest.B1.Whir.HelperT

/-!
# `residual_batch` and `level_residual`, honestly

`rb_complete`: `residual_batch__L{cols}` steps the chain `h ← (h + R(p))·μ` over its batch's eight
positions. `lr_complete`: `level_residual` at `q` queries, on its positions' buffer, its row of
`basis_d`, `μ`, and its two chains' buffers holding the honest chain (`lrAcc`, the chain over the
first positions from `0`: the batches' at multiples of eight, the rest's after them), returns the
chain over all `q` positions.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The vanishing tables' first entry for `cols` message columns. -/
abbrev vanishOfCols (cols : ℕ) : ℕ := cols * (cols + 1) / 2

/-- The chain over the first `n` positions `p 0, …`, from `0`. -/
def lrAcc (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (n : ℕ) : E :=
  resFoldC D (vanishOfCols cols) cols M 0 ((List.range n).map p)

theorem lrAcc_add (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (n m : ℕ) :
    lrAcc D cols M p (n + m) =
      resFoldC D (vanishOfCols cols) cols M (lrAcc D cols M p n) ((List.range m).map fun i ↦ p (n + i)) := by
  rw [lrAcc, List.range_add, List.map_append, resFoldC_append, lrAcc, List.map_map]
  rfl

theorem lrAcc_succ (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (n : ℕ) :
    lrAcc D cols M p (n + 1) =
      (lrAcc D cols M p n + residualProd (osVals (vanishOfCols cols) cols) (p n) D cols) * M := by
  rw [lrAcc_add]
  simp [resFoldC]

/-! ## Small blocks -/

/-- **A copy, honestly.** -/
theorem copy_complete {σ : Val} {k s : ℕ} (hs : s < k) :
    BlkF C rd σ k (k + 1) (fun _ ↦ σ (.n s)) [.atom (.copy (.n k) (.n s))]
      (fun σ' ↦ σ' (.n k) = σ (.n s)) := by
  intro σ' ha hr
  have v := hr k le_rfl (by omega)
  refine ⟨?_, v⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  rw [v, ha s hs]

/-- A loop's entry, whether or not it runs. -/
theorem loop_entry {f : String} {n : ℕ} {N : E} {rest : List E} (hN : N = gen ^ n)
    (h : 0 < n → IsInK (1 + N) ∧ (1 + N ≠ 0 → coreProgram.Rel rd f (1 :: N :: rest) [])) :
    IsInK (1 + N) ∧ (1 + N ≠ 0 → coreProgram.Rel rd f (1 :: N :: rest) []) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (1 : E) + N = 0 := by rw [hN, pow_zero]; exact CharTwo.add_self_eq_zero _
    rw [h0]
    exact ⟨by simpa using ofK_isInK 0, fun h ↦ absurd rfl h⟩
  · exact h hn

/-! ## `residual_batch` -/

/-- The chain's steps of `residual_batch`. -/
abbrev rbChain (cols : ℕ) : List Stmt × ℕ × ℕ :=
  osResSteps 0 1 0 (vanishOfCols cols) cols 2 (List.range resBatch) 3 4

theorem rbBody_chain (cols : ℕ) : rbBody cols = ((rbChain cols).1 ++
    [.atom (.copy (.n (rbChain cols).2.2) (.n (rbChain cols).2.1))]) ++ [.ret [.n (rbChain cols).2.2]] := by
  simp [rbBody]

theorem osResQ_isFlat (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ),
    (osResQ pos bd row vo n t pe k).1.all Stmt.flat = true
  | 0, _, _, _ => rfl
  | n + 1, t, pe, k => by
    simp [osResQ, osResQ_isFlat pos bd row vo n, Stmt.flat]

theorem osResQuery_isFlat (pos bd row vo n k : ℕ) : (osResQuery pos bd row vo n k).1.all Stmt.flat = true := by
  simp [osResQuery, osResQ_isFlat, Stmt.flat]

theorem osResSteps_isFlat (pp bd row vo ncols mu : ℕ) : ∀ (js : List ℕ) (h k : ℕ),
    (osResSteps pp bd row vo ncols mu js h k).1.all Stmt.flat = true
  | [], _, _ => rfl
  | j :: js, h, k => by
    simp only [osResSteps, osResStep, List.all_append, osResQuery_isFlat, osResSteps_isFlat pp bd row vo ncols mu js]
    simp [Stmt.flat]

/-- **`residual_batch`, honestly**: its batch's eight positions at `B`, its row of `basis_d` at `BD`,
the chain stepped from `H`. -/
theorem rb_complete {cols : ℕ} (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hn : 1 ≤ cols)
    {B BD M H : E} {D : ℕ → E} {ps : List E}
    (hP : List.Forall₂ (fun j p ↦ LoadHolds rd B j p) (List.range resBatch) ps)
    (hD : ∀ s < cols, LoadHolds rd BD s (D s)) :
    coreProgram.Rel rd (rbName cols) [B, BD, M, H] [resFoldC D (vanishOfCols cols) cols M H ps] := by
  obtain ⟨fn, hf, hps, hb⟩ := hrb
  have hk := osResSteps_k 0 1 0 (vanishOfCols cols) cols 2 (List.range resBatch) 3 4 (by omega)
  have hS := osResSteps_complete (C := coreProgram.Rel rd) (rd := rd) (pp := 0) (bd := 1) (row := 0)
    (vo := vanishOfCols cols) (ncols := cols) (mu := 2) (D := D) (M := M)
    (PP := B) (BD := BD) hn (List.range resBatch) ps 3 4 H (argVal [B, BD, M, H]) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [argVal_n]; rfl) (by rw [argVal_n]; rfl)
    (by rw [argVal_n]; rfl) (by rw [argVal_n]; rfl) hP (fun s hs ↦ by rw [Nat.zero_add]; exact hD s hs)
  refine rel_of_blkF hf hps (rbBody_chain cols ▸ hb)
    (by rw [List.all_append, osResSteps_isFlat]; rfl)
    (BlkF.then (k1 := (rbChain cols).2.2) hk.1 (Nat.le_succ _) hS fun σ1 _ ⟨hv, _⟩ ↦
      BlkF.mono (copy_complete hk.2) fun σ' h ↦ ?_)
  simp only [List.map_cons, List.map_nil, h, hv]

/-! ## `level_residual`'s batches' loop -/

/-- The batches' loop's iteration before its tail. -/
def lrIter1A (cols : ℕ) : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 9) (.n 3) (.n 8)), .atom (.mul (.n 10) (.n 2) (.n 0)), .atom (.load (.n 11) (.n 10) 0),
    .call (rbName cols) [.n 9, .n 4, .n 5, .n 11] [.n 12],
    .atom (.mul (.n 13) (.n 2) (.n 0)), .atom (.load (.n 12) (.n 13) 1)]

theorem lrIter1Body_eq (cols : ℕ) (name : String) :
    lrLoop1Body cols name = lrIter1A cols ++ osLoopTail name 6 14 := rfl

/-- **The batches' loop's iteration, honestly.** -/
theorem lrIter1_complete {cols : ℕ} {X N CH P BD M h h' : E}
    (h0 : LoadHolds rd (CH * X) 0 h) (h1 : LoadHolds rd (CH * X) 1 h')
    (hc : C (rbName cols) [P * X ^ 8, BD, M, h] [h']) :
    BlkF C rd (argVal [X, N, CH, P, BD, M]) 6 14
      (fun i ↦ [X * X, X * X * (X * X), X * X * (X * X) * (X * X * (X * X)),
        P * (X * X * (X * X) * (X * X * (X * X))), CH * X, h, h', CH * X].getD (i - 6) 0)
      (lrIter1A cols) (fun _ ↦ True) := by
  intro σ' ha hr
  have v0 : σ' (.n 6) = X * X := by rw [hr 6 (by omega) (by omega)]; rfl
  have v1 : σ' (.n 7) = X * X * (X * X) := by rw [hr 7 (by omega) (by omega)]; rfl
  have v2 : σ' (.n 8) = X * X * (X * X) * (X * X * (X * X)) := by rw [hr 8 (by omega) (by omega)]; rfl
  have v3 : σ' (.n 9) = P * (X * X * (X * X) * (X * X * (X * X))) := by
    rw [hr 9 (by omega) (by omega)]; rfl
  have v4 : σ' (.n 10) = CH * X := by rw [hr 10 (by omega) (by omega)]; rfl
  have v5 : σ' (.n 11) = h := by rw [hr 11 (by omega) (by omega)]; rfl
  have v6 : σ' (.n 12) = h' := by rw [hr 12 (by omega) (by omega)]; rfl
  have v7 : σ' (.n 13) = CH * X := by rw [hr 13 (by omega) (by omega)]; rfl
  have a0 : σ' (.n 0) = X := by rw [ha 0 (by omega), argVal_n]; rfl
  have a2 : σ' (.n 2) = CH := by rw [ha 2 (by omega), argVal_n]; rfl
  have a3 : σ' (.n 3) = P := by rw [ha 3 (by omega), argVal_n]; rfl
  have a4 : σ' (.n 4) = BD := by rw [ha 4 (by omega), argVal_n]; rfl
  have a5 : σ' (.n 5) = M := by rw [ha 5 (by omega), argVal_n]; rfl
  refine ⟨?_, trivial⟩
  simp only [lrIter1A, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
    List.map_nil]
  refine ⟨by rw [v0, a0], by rw [v1, v0], by rw [v2, v1], by rw [v3, a3, v2], by rw [v4, a2, a0],
    by rw [v5, v4]; exact h0, ?_, by rw [v7, a2, a0], by rw [v6, v7]; exact h1⟩
  rw [v3, a4, a5, v5, v6, show X * X * (X * X) * (X * X * (X * X)) = X ^ 8 by ring]
  exact hc

/-! ## `level_residual`'s rest's loop -/

/-- The rest's loop's query block. -/
abbrev lrIter2Q (cols : ℕ) : List Stmt × ℕ × ℕ := osResQuery 9 4 0 (vanishOfCols cols) cols 10

/-- The rest's loop's iteration before its tail. -/
def lrIter2A (cols : ℕ) : List Stmt :=
  [.atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.load (.n 7) (.n 6) 0), .atom (.mul (.n 8) (.n 3) (.n 0)),
    .atom (.load (.n 9) (.n 8) 0)] ++ (lrIter2Q cols).1 ++
    [.atom (.add (.n (lrIter2Q cols).2.2) (.n 7) (.n (lrIter2Q cols).2.1)),
      .atom (.mul (.n ((lrIter2Q cols).2.2 + 1)) (.n (lrIter2Q cols).2.2) (.n 5)),
      .atom (.mul (.n ((lrIter2Q cols).2.2 + 2)) (.n 2) (.n 0)),
      .atom (.load (.n ((lrIter2Q cols).2.2 + 1)) (.n ((lrIter2Q cols).2.2 + 2)) 1)]

theorem lrIter2Body_eq (cols : ℕ) (name : String) :
    lrLoop2Body cols name = lrIter2A cols ++ osLoopTail name 6 ((lrIter2Q cols).2.2 + 3) := rfl

/-- **The rest's loop's iteration, honestly.** -/
theorem lrIter2_complete {cols : ℕ} (hn : 1 ≤ cols) {X N RS T BD M h p : E} {D : ℕ → E}
    (h0 : LoadHolds rd (RS * X) 0 h)
    (h1 : LoadHolds rd (RS * X) 1
      ((h + residualProd (osVals (vanishOfCols cols) cols) p D cols) * M))
    (hp : LoadHolds rd (T * X) 0 p) (hD : ∀ s < cols, LoadHolds rd BD s (D s)) :
    Blk C rd (argVal [X, N, RS, T, BD, M]) 6 ((lrIter2Q cols).2.2 + 3) (lrIter2A cols) (fun _ ↦ True) := by
  obtain ⟨hq1, hq2⟩ : 10 + 2 ≤ (lrIter2Q cols).2.2 ∧ (lrIter2Q cols).2.1 < (lrIter2Q cols).2.2 :=
    osResQuery_k 9 4 0 (vanishOfCols cols) cols 10
  set R := residualProd (osVals (vanishOfCols cols) cols) p D cols
  have a : ∀ σ', AgreeBelow 6 (argVal [X, N, RS, T, BD, M]) σ' →
      σ' (.n 0) = X ∧ σ' (.n 2) = RS ∧ σ' (.n 3) = T ∧ σ' (.n 4) = BD ∧ σ' (.n 5) = M :=
    fun σ' ha ↦ ⟨by rw [ha 0 (by omega), argVal_n]; rfl, by rw [ha 2 (by omega), argVal_n]; rfl,
      by rw [ha 3 (by omega), argVal_n]; rfl, by rw [ha 4 (by omega), argVal_n]; rfl,
      by rw [ha 5 (by omega), argVal_n]; rfl⟩
  have hA : BlkF C rd (argVal [X, N, RS, T, BD, M]) 6 10
      (fun i ↦ [RS * X, h, T * X, p].getD (i - 6) 0)
      [.atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.load (.n 7) (.n 6) 0), .atom (.mul (.n 8) (.n 3) (.n 0)),
        .atom (.load (.n 9) (.n 8) 0)]
      (fun σ' ↦ σ' (.n 7) = h ∧ σ' (.n 9) = p ∧ AgreeBelow 6 (argVal [X, N, RS, T, BD, M]) σ') := by
    intro σ' ha hr
    have v0 : σ' (.n 6) = RS * X := by rw [hr 6 (by omega) (by omega)]; rfl
    have v1 : σ' (.n 7) = h := by rw [hr 7 (by omega) (by omega)]; rfl
    have v2 : σ' (.n 8) = T * X := by rw [hr 8 (by omega) (by omega)]; rfl
    have v3 : σ' (.n 9) = p := by rw [hr 9 (by omega) (by omega)]; rfl
    obtain ⟨a0, a2, a3, -, -⟩ := a σ' ha
    refine ⟨?_, v1, v3, ha⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨by rw [v0, a2, a0], by rw [v1, v0]; exact h0, by rw [v2, a3, a0], by rw [v3, v2]; exact hp⟩
  refine (BlkF.then (k1 := 10) (by omega) (by omega) hA fun σ1 ha1 ⟨e7, e9, _⟩ ↦
    BlkF.then (k1 := (lrIter2Q cols).2.2) (by omega) (by omega)
      (fB := fun _ i ↦ [h + R, (h + R) * M, RS * X].getD (i - (lrIter2Q cols).2.2) 0)
      (osResQuery_complete (C := C) (rd := rd) (pos := 9) (bd := 4) (row := 0) (vo := vanishOfCols cols)
        (n := cols) (k := 10) (D := D) σ1 hn (by omega) (by omega) (by omega)
        (fun s hs ↦ by
          rw [ha1 4 (by omega), (a _ (fun _ h ↦ rfl)).2.2.2.1, Nat.zero_add]; exact hD s hs))
      fun σ2 ha2 ⟨eR, ha2'⟩ ↦ ?_).blk
  intro σ' ha hr
  set e := (lrIter2Q cols).2.2
  set f := (lrIter2Q cols).2.1
  have w0 : σ' (.n e) = h + R := by
    rw [hr e (by omega) (by omega)]; simp only [Nat.sub_self]; rfl
  have w1 : σ' (.n (e + 1)) = (h + R) * M := by
    rw [hr (e + 1) (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]; rfl
  have w2 : σ' (.n (e + 2)) = RS * X := by
    rw [hr (e + 2) (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]; rfl
  have hb6 : AgreeBelow 6 (argVal [X, N, RS, T, BD, M]) σ' := fun i hi ↦ by
    rw [ha i (by omega), ha2' i (by omega), ha1 i hi]
  obtain ⟨b0, b2, -, -, b5⟩ := a σ' hb6
  have b7 : σ' (.n 7) = h := by rw [ha 7 (by omega), ha2' 7 (by omega), e7]
  have bf : σ' (.n f) = R := by rw [ha f hq2, eR, e9]
  refine ⟨?_, trivial⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  refine ⟨by rw [w0, b7, bf], by rw [w1, w0, b5], by rw [w2, b2, b0], by rw [w1, w2]; exact h1⟩

/-! ## The loops -/

theorem lrIter1A_flat (cols : ℕ) : (lrIter1A cols ++ osLoopTailA 14).all Stmt.flat = true := by
  simp [lrIter1A, osLoopTailA, Stmt.flat]

theorem lrIter2A_flat (cols : ℕ) :
    (lrIter2A cols ++ osLoopTailA ((lrIter2Q cols).2.2 + 3)).all Stmt.flat = true := by
  simp [lrIter2A, osLoopTailA, osResQuery_isFlat, Stmt.flat]

theorem forall₂_range_map {R : ℕ → E → Prop} {n : ℕ} {f : ℕ → E} (h : ∀ i < n, R i (f i)) :
    List.Forall₂ R (List.range n) ((List.range n).map f) := by
  rw [List.forall₂_map_right_iff, List.forall₂_same]
  intro x hx
  exact h x (List.mem_range.mp hx)

/-- **The batches' loop, honestly.** -/
theorem lrLoop1_complete {loop : String} {cols q8 : ℕ}
    (hl : FnIs loop (osParams 6) (lrLoop1Body cols loop))
    (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hn : 1 ≤ cols) (hq8 : 0 < q8)
    {CH P BD M : E} {D p : ℕ → E} (hP : ∀ i < resBatch * q8, LoadHolds rd P i (p i))
    (hD : ∀ s < cols, LoadHolds rd BD s (D s))
    (hCH : ∀ j ≤ q8, LoadHolds rd CH j (lrAcc D cols M p (resBatch * j))) :
    IsInK (1 + gen ^ q8) ∧
      (1 + gen ^ q8 ≠ 0 → coreProgram.Rel rd loop (1 :: gen ^ q8 :: [CH, P, BD, M]) []) := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  have hb' : fn.body = (lrIter1A cols ++ osLoopTailA 14) ++
      [.callIf (.n (14 + 2)) loop (.n (14 + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)),
        .ret []] := by
    rw [hb, lrIter1Body_eq, osLoopTail_split, List.append_assoc]
  refine loop_complete hf (lrIter1A_flat cols) hb' hq8 rfl fun j hj ↦ ?_
  have h0 : LoadHolds rd (CH * gen ^ j) 0 (lrAcc D cols M p (resBatch * j)) := by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hCH j (by omega)
  have h1 : LoadHolds rd (CH * gen ^ j) 1 (lrAcc D cols M p (resBatch * j + resBatch)) := by
    rw [loadHolds_mul_gen_pow, show resBatch * j + resBatch = resBatch * (j + 1) by ring]
    exact hCH (j + 1) (by omega)
  have hc : coreProgram.Rel rd (rbName cols) [P * (gen ^ j) ^ 8, BD, M, lrAcc D cols M p (resBatch * j)]
      [lrAcc D cols M p (resBatch * j + resBatch)] := by
    have hF : List.Forall₂ (fun i w ↦ LoadHolds rd (P * (gen ^ j) ^ 8) i w) (List.range resBatch)
        ((List.range resBatch).map fun i ↦ p (resBatch * j + i)) := by
      refine forall₂_range_map fun i hi ↦ ?_
      rw [← pow_mul, loadHolds_mul_gen_pow]
      have : j * 8 + i < resBatch * q8 := by simp only [resBatch] at hi ⊢; omega
      rw [show j * 8 + i = resBatch * j + i by simp only [resBatch]; ring]
      exact hP _ (by simp only [resBatch] at this ⊢; omega)
    have h := rb_complete (rd := rd) hrb hn (B := P * (gen ^ j) ^ 8) (BD := BD) (M := M)
      (H := lrAcc D cols M p (resBatch * j)) (D := D) hF hD
    rw [lrAcc_add]
    exact h
  obtain ⟨σ, h1', h2', h3', h4'⟩ := iter_of_blkF (C := coreProgram.Rel rd) (rd := rd) (n := 6) (K := 14)
    (X := gen ^ j) (N := gen ^ q8) (rest := [CH, P, BD, M]) rfl (by omega)
    (BlkF.mono (lrIter1_complete h0 h1 hc) fun _ _ ↦ trivial)
  exact ⟨σ, by rw [hps]; exact h1', h2', h3', h4'⟩

/-- **The rest's loop, honestly.** -/
theorem lrLoop2_complete {loop : String} {cols r b : ℕ}
    (hl : FnIs loop (osParams 6) (lrLoop2Body cols loop)) (hn : 1 ≤ cols) (hr : 0 < r)
    {RS P BD M : E} {D p : ℕ → E} (hP : ∀ i < r, LoadHolds rd P (b + i) (p (b + i)))
    (hD : ∀ s < cols, LoadHolds rd BD s (D s))
    (hRS : ∀ j ≤ r, LoadHolds rd RS j (lrAcc D cols M p (b + j))) :
    IsInK (1 + gen ^ r) ∧
      (1 + gen ^ r ≠ 0 → coreProgram.Rel rd loop (1 :: gen ^ r :: [RS, P * gen ^ b, BD, M]) []) := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  have hb' : fn.body = (lrIter2A cols ++ osLoopTailA ((lrIter2Q cols).2.2 + 3)) ++
      [.callIf (.n ((lrIter2Q cols).2.2 + 3 + 2)) loop
        (.n ((lrIter2Q cols).2.2 + 3 + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
    rw [hb, lrIter2Body_eq, osLoopTail_split, List.append_assoc]
  refine loop_complete hf (lrIter2A_flat cols) hb' hr rfl fun j hj ↦ ?_
  have h0 : LoadHolds rd (RS * gen ^ j) 0 (lrAcc D cols M p (b + j)) := by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hRS j (by omega)
  have h1 : LoadHolds rd (RS * gen ^ j) 1 ((lrAcc D cols M p (b + j) +
      residualProd (osVals (vanishOfCols cols) cols) (p (b + j)) D cols) * M) := by
    rw [loadHolds_mul_gen_pow, ← lrAcc_succ, show b + j + 1 = b + (j + 1) by ring]
    exact hRS (j + 1) (by omega)
  have hp : LoadHolds rd (P * gen ^ b * gen ^ j) 0 (p (b + j)) := by
    rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]; exact hP j hj
  have hq1 : 10 + 2 ≤ (lrIter2Q cols).2.2 := (osResQuery_k 9 4 0 (vanishOfCols cols) cols 10).1
  obtain ⟨f, hblk⟩ := lrIter2_complete (C := coreProgram.Rel rd) (X := gen ^ j) (N := gen ^ r)
    (T := P * gen ^ b) hn h0 h1 hp hD
  obtain ⟨σ, h1', h2', h3', h4'⟩ := iter_of_blkF (C := coreProgram.Rel rd) (rd := rd) (n := 6)
    (K := (lrIter2Q cols).2.2 + 3) (X := gen ^ j) (N := gen ^ r) (rest := [RS, P * gen ^ b, BD, M]) rfl
    (by omega) hblk
  exact ⟨σ, by rw [hps]; exact h1', h2', h3', h4'⟩

/-! ## `level_residual` -/

/-- **`level_residual`, honestly**: on `q` positions at `P`, the row of `basis_d` at `BD`, the
batches' chain at `CH` (word `j` the chain over the first `8j` positions, `j ≤ q / 8`) and, when
`8 ∤ q`, the rest's chain at `RS` (word `j` the chain over the first `8·(q / 8) + j`), the
specialization returns the chain over the `q` positions. -/
theorem lr_complete {name loop1 loop2 : String} {q cols : ℕ}
    (hlr : FnIs name (osParams 3) (lrBody q loop1 loop2))
    (hl1 : 0 < q / resBatch → FnIs loop1 (osParams 6) (lrLoop1Body cols loop1))
    (hl2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 6) (lrLoop2Body cols loop2))
    (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hn : 1 ≤ cols) (hq : q + 1 < u128Bound)
    {P BD M CH RS : E} {D p : ℕ → E} (hP : ∀ i < q, LoadHolds rd P i (p i))
    (hD : ∀ s < cols, LoadHolds rd BD s (D s))
    (hCH : ∀ j ≤ q / resBatch, LoadHolds rd CH j (lrAcc D cols M p (resBatch * j)))
    (hRS : q % resBatch ≠ 0 → ∀ j ≤ q % resBatch,
      LoadHolds rd RS j (lrAcc D cols M p (resBatch * (q / resBatch) + j))) :
    coreProgram.Rel rd name [P, BD, M] [lrAcc D cols M p q] := by
  obtain ⟨fn, hf, hps, hb⟩ := hlr
  set q8 := q / resBatch with hq8
  set r := q % resBatch with hr
  have hqd : resBatch * q8 + r = q := Nat.div_add_mod q resBatch
  have hq8le : q8 ≤ q := Nat.div_le_self _ _
  have hq8' : q8 + 1 < u128Bound := by omega
  have hr' : r + 1 < u128Bound := by
    have : r ≤ q := Nat.mod_le _ _
    omega
  have h8 : resBatch * q8 < u128Bound := by omega
  have hL1 := loop_entry (rd := rd) (f := loop1) (rest := [CH, P, BD, M]) rfl fun h ↦
    lrLoop1_complete (hl1 h) hrb hn h
      (fun i hi ↦ hP i (lt_of_lt_of_le hi (Nat.mul_div_le q resBatch))) hD hCH
  have hz : LoadHolds rd CH 0 (word 0 0 0) := by
    have := hCH 0 (Nat.zero_le _)
    rw [word_zero]; simpa [lrAcc, resFoldC] using this
  have hB := hCH q8 le_rfl
  rw [rel_iff_sem hf]
  by_cases h0 : r = 0
  · have hb' : fn.body = (osHeap (q8 + 1) 3 ++
        [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
        osLoopCall loop1 q8 [4, 0, 1, 2] 6 ++ [.atom (.load (.n 11) (.n 4) q8)] ++
        [.atom (.copy (.n 12) (.n 11))]) ++ [.ret [.n 12]] := by
      have h0' : q % resBatch = 0 := h0
      rw [hb, lrBody]
      simp only [h0', ↓reduceIte, List.append_assoc, List.cons_append,
        List.nil_append, hq8]
    set vals := [P, BD, M, gw (q8 + 1), CH, word 0 0 0, word 1 0 0, gw q8, word 1 0 0 + gw q8,
      word 1 0 0, gw q8, lrAcc D cols M p (resBatch * q8), lrAcc D cols M p (resBatch * q8)]
    refine ⟨argVal vals, by rw [hps]; rfl, ?_⟩
    rw [hb', holdsList_flat_ret _ (by simp [osHeap, osLoopCall, Stmt.flat])]
    refine ⟨?_, ?_⟩
    · simp only [osHeap, osLoopCall, List.cons_append, List.nil_append,
        allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil, argVal_n]
      simp only [vals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, true_and, and_true]
      rw [word_one, gw_eq (by omega)]
      exact ⟨hz, hL1, hB⟩
    · simp only [List.map_cons, List.map_nil, argVal_n, vals]
      rw [← hqd, h0, Nat.add_zero]; rfl
  · have hb' : fn.body = (osHeap (q8 + 1) 3 ++
        [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
        osLoopCall loop1 q8 [4, 0, 1, 2] 6 ++ [.atom (.load (.n 11) (.n 4) q8)] ++
        (osHeap (r + 1) 12 ++
          [.atom (.load (.n 11) (.n 13) 0), .atom (.const (.n 14) (gw (resBatch * q8))),
            .atom (.mul (.n 15) (.n 0) (.n 14))] ++
          osLoopCall loop2 r [13, 15, 1, 2] 16 ++
          [.atom (.load (.n 21) (.n 13) r), .atom (.copy (.n 22) (.n 21))])) ++ [.ret [.n 22]] := by
      have h0' : ¬ q % resBatch = 0 := h0
      rw [hb, lrBody]
      simp only [h0', ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, hq8, hr]
    have hRS' := hRS h0
    have hL2 := lrLoop2_complete (rd := rd) (b := resBatch * q8) (RS := RS) (hl2 h0) hn
      (Nat.pos_of_ne_zero h0) (fun i hi ↦ hP _ (by omega)) hD hRS'
    set vals := [P, BD, M, gw (q8 + 1), CH, word 0 0 0, word 1 0 0, gw q8, word 1 0 0 + gw q8,
      word 1 0 0, gw q8, lrAcc D cols M p (resBatch * q8), gw (r + 1), RS, gw (resBatch * q8),
      P * gw (resBatch * q8), word 1 0 0, gw r, word 1 0 0 + gw r, word 1 0 0, gw r,
      lrAcc D cols M p q, lrAcc D cols M p q]
    refine ⟨argVal vals, by rw [hps]; rfl, ?_⟩
    rw [hb', holdsList_flat_ret _ (by simp [osHeap, osLoopCall, Stmt.flat])]
    refine ⟨?_, ?_⟩
    · simp only [osHeap, osLoopCall, List.cons_append, List.nil_append,
        allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil, argVal_n]
      simp only [vals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, true_and, and_true]
      have hR0 := hRS' 0 (by omega)
      have hRr := hRS' r le_rfl
      rw [Nat.add_zero] at hR0
      rw [hqd] at hRr
      rw [word_one, gw_eq (by omega), gw_eq (by omega), gw_eq h8]
      exact ⟨hz, hL1, hB, hR0, hL2, hRr⟩
    · simp only [List.map_cons, List.map_nil, argVal_n, vals]; rfl

end
end LeanVM.Guest.B1.Whir
