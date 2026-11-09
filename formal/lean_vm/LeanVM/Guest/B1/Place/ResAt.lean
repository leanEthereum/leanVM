/-
  LeanVM.Guest.B1.Place.ResAt

  `open_stacked`'s residual loop, honestly and placed.
-/

module

public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Whir.CFinRes
public import LeanVM.Guest.B1.Whir.CLoop
public import LeanVM.Guest.B1.Whir.ResLoop

/-!
# The residual loop, honestly and placed

`resIter_complete`: one iteration at `x` (eight queries, the chain `h ← (h + R(p))·μ`) whose
memory is the iteration's meaning (`ResIter`, the row's words `D` at `bd`) holds at a valuation,
with the guard `x·g + N` and the next arguments.
`resLoop_rel`: the loop entered at `1 :: g^n :: rest` holds (`loop_complete`).
`resLoop_pure`: the loop helper places nothing and calls only itself, so it is complete placed
on every memory holding the caller's words where every iteration's meaning holds
(`resLoop_completeAtD`, `completeAt_of_rel_pureD`); `resLoop_completeAtB`, by a tree of at most `B`
words when `B` bounds the loop's valid trees at the call's arguments (`completeAt_of_rel_pureBat`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- A materialized pointer, as a block of named values. -/
theorem osMat_blk {base off k : ℕ} (hoff : off < u128Bound) (hb : base < k) (σ : Val) :
    BlkF C rd σ k (osMat base off k).2.2 (matVal σ base off k) (osMat base off k).1
      (fun σ' ↦ σ' (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off ∧ AgreeBelow k σ σ') :=
  fun _ ha hv ↦ let h := osMat_complete (C := C) (rd := rd) hoff hb ha hv; ⟨h.1, h.2, ha⟩

theorem osMat_v_lt (b o k : ℕ) (hb : b < k) : (osMat b o k).2.1 < (osMat b o k).2.2 := by
  unfold osMat; split_ifs
  · exact hb
  · show k + 1 < k + 2; omega

/-- One atom writing the next value. -/
theorem atom1_complete {k : ℕ} {a : Atom} (σ : Val) (v : E)
    (h : ∀ σ', AgreeBelow k σ σ' → σ' (.n k) = v → a.Holds rd σ') :
    BlkF C rd σ k (k + 1) (fun _ ↦ v) [.atom a] (fun σ' ↦ σ' (.n k) = v ∧ AgreeBelow k σ σ') :=
  fun σ' ha hr ↦ by
    have v0 := hr k le_rfl (by omega)
    exact ⟨allOk_cons.mpr ⟨h σ' ha v0, allOk_nil⟩, v0, ha⟩

/-- Two blocks in sequence, their values chosen. -/
theorem BlkF.thenE {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA Out : Val → Prop}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : ∃ fA, BlkF C rd σ k k1 fA A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → ∃ fB, BlkF C rd σ1 k1 k2 fB B Out) :
    ∃ f, BlkF C rd σ k k2 f (A ++ B) Out := by
  obtain ⟨fA, hA⟩ := hA
  have hB' : ∀ σ1, ∃ fB : ℕ → E, AgreeBelow k σ σ1 → OutA σ1 → BlkF C rd σ1 k1 k2 fB B Out :=
    fun σ1 ↦ by
      by_cases h : AgreeBelow k σ σ1 ∧ OutA σ1
      · obtain ⟨fB, hf⟩ := hB σ1 h.1 h.2; exact ⟨fB, fun _ _ ↦ hf⟩
      · exact ⟨fun _ ↦ 0, fun ha ho ↦ absurd ⟨ha, ho⟩ h⟩
  exact ⟨_, BlkF.then (fB := fun σ1 ↦ Classical.choose (hB' σ1)) h1 h2 hA
    fun σ1 ha ho ↦ Classical.choose_spec (hB' σ1) ha ho⟩

theorem forall₂_range_of {P : ℕ → E → Prop} {n : ℕ} {ps : List E} (hl : ps.length = n)
    (h : ∀ i < n, P i (ps.getD i 0)) : List.Forall₂ P (List.range n) ps := by
  refine List.forall₂_iff_get.mpr ⟨by simp [hl], fun i h1 h2 ↦ ?_⟩
  have := h i (by simpa using h1)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] using this

/-- **One iteration of the residual loop, honestly** (G:1730-1739): at `x`, whose memory is the
iteration's meaning (`ResIter`: the batch's eight positions at `qpos·g^posOff·x^8`, `chain[x]`
and `chain[x·g]` the steps over them), the row's words `D` at `bd`. -/
theorem resIter_complete (lvl : ℕ) (lv : OsLv) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) {D : ℕ → E} (x N qpos bd chain mu : E)
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    (hit : ResIter rd D lv.vanish lv.logCols lv.posOff qpos chain mu x) :
    ∃ σ : Val, (osParams 6).map σ = [x, N, qpos, bd, chain, mu] ∧
      AllOk C rd σ (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv)) ∧
      σ (.n (resLoopR lvl lv + 2)) = x * gen + N ∧
      (.n (resLoopR lvl lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, qpos, bd, chain, mu] := by
  obtain ⟨h, ps, hl, hps, lh, ls⟩ := hit
  set σ0 := segVal [(6, fun i ↦ [x, N, qpos, bd, chain, mu].getD i 0)] with hσ0
  have g : ∀ i < 6, σ0 (.n i) = [x, N, qpos, bd, chain, mu].getD i 0 := fun i hi ↦ by
    rw [hσ0, segVal_n]; simp [segLookup, hi]
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2 g3 g4 g5
  set pp := osMat 2 lv.posOff 6 with hpp
  set y := pp.2.2 with hy
  set st := osResSteps (y + 3) 3 (lvl * ligColsCap) lv.vanish lv.logCols 5 (List.range resBatch)
    (y + 5) (y + 6) with hst
  set r := st.2.2 with hr
  have hR : resLoopR lvl lv = r + 1 := rfl
  have o1 : 6 ≤ y := osMat_next _ _ _
  have o1' : pp.2.1 < y := osMat_v_lt _ _ _ (by omega)
  have o2 : y + 6 ≤ r ∧ st.2.1 < r :=
    osResSteps_k (y + 3) 3 (lvl * ligColsCap) lv.vanish lv.logCols 5 (List.range resBatch) (y + 5)
      (y + 6) (by omega)
  have eA : resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv) =
      pp.1 ++ ([.atom (.mul (.n y) (.n 0) (.n 0)), .atom (.mul (.n (y + 1)) (.n y) (.n y)),
        .atom (.mul (.n (y + 2)) (.n (y + 1)) (.n (y + 1))),
        .atom (.mul (.n (y + 3)) (.n pp.2.1) (.n (y + 2))),
        .atom (.mul (.n (y + 4)) (.n 4) (.n 0)), .atom (.load (.n (y + 5)) (.n (y + 4)) 0)] ++
      (st.1 ++ ([.atom (.mul (.n r) (.n 4) (.n 0)), .atom (.load (.n st.2.1) (.n r) 1)] ++
        osLoopTailA (r + 1)))) := by
    rw [hR]; simp only [resLoopA, List.append_assoc]; rfl
  set X8 := x * x * (x * x) * (x * x * (x * x)) with hX8
  have eX8 : X8 = x ^ resBatch := by rw [hX8]; ring
  set R := resFold D lv.vanish lv.logCols mu h ps with hRdef
  have hB : ∃ f, BlkF C rd σ0 6 (r + 1 + 5) f (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv))
      (fun _ ↦ True) := by
    rw [eA]
    refine BlkF.thenE (k1 := y) o1 (by omega)
      ⟨_, osMat_blk (C := C) (rd := rd) hpo (show 2 < 6 by omega) σ0⟩ fun σ1 ha1 hO1 ↦ ?_
    have hq1 : σ1 (.n pp.2.1) = qpos * gen ^ lv.posOff := by rw [hO1.1, g2]
    have e1 : ∀ i < 6, σ1 (.n i) = σ0 (.n i) := fun i hi ↦ hO1.2 i hi
    refine BlkF.thenE (k1 := y + 6) (by omega) (by omega)
      (OutA := fun σ' ↦ σ' (.n (y + 3)) = qpos * gen ^ lv.posOff * X8 ∧ σ' (.n (y + 5)) = h ∧
        AgreeBelow y σ1 σ')
      ⟨fun i ↦ [x * x, x * x * (x * x), X8, qpos * gen ^ lv.posOff * X8, chain * x, h].getD (i - y) 0,
        ?_⟩ fun σ2 ha2 hO2 ↦ ?_
    · intro σ' ha hv
      have V : ∀ j < 6, σ' (.n (y + j)) =
          [x * x, x * x * (x * x), X8, qpos * gen ^ lv.posOff * X8, chain * x, h].getD j 0 :=
        fun j hj ↦ by rw [hv _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
      have p0 : σ' (.n 0) = x := by rw [ha 0 (by omega), e1 0 (by omega), g0]
      have p4 : σ' (.n 4) = chain := by rw [ha 4 (by omega), e1 4 (by omega), g4]
      have pq : σ' (.n pp.2.1) = qpos * gen ^ lv.posOff := by rw [ha _ o1', hq1]
      refine ⟨?_, v3, v5, ha⟩
      simp only [allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds]
      refine ⟨by rw [v0, p0], by rw [v1, v0], by rw [v2, v1], by rw [v3, pq, v2],
        by rw [v4, p4, p0], ?_⟩
      rw [v5, v4]; exact lh
    have e2 : ∀ i < 6, σ2 (.n i) = σ0 (.n i) := fun i hi ↦
      (hO2.2.2 i (by omega)).trans (e1 i hi)
    have hF : List.Forall₂ (fun j p ↦ LoadHolds rd (qpos * gen ^ lv.posOff * X8) j p)
        (List.range resBatch) ps :=
      forall₂_range_of hl fun i hi ↦ by rw [eX8]; exact hps i hi
    refine BlkF.thenE (k1 := r) o2.1 (by omega)
      ⟨_, osResSteps_complete (C := C) (rd := rd) (pp := y + 3) (bd := 3) (row := lvl * ligColsCap)
        (vo := lv.vanish) (ncols := lv.logCols) (mu := 5) (D := D) (M := mu)
        (PP := qpos * gen ^ lv.posOff * X8) (BD := bd) hml (List.range resBatch) ps (y + 5) (y + 6) h
        σ2 (by omega) (by omega) (by omega) (by omega) (by omega) hO2.1 (by rw [e2 3 (by omega), g3])
        hO2.2.1 (by rw [e2 5 (by omega), g5]) hF hD⟩ fun σ3 ha3 hO3 ↦ ?_
    have e3 : ∀ i < 6, σ3 (.n i) = σ0 (.n i) := fun i hi ↦
      (hO3.2 i (by omega)).trans (e2 i hi)
    have hS : σ3 (.n st.2.1) = R := hO3.1
    refine BlkF.thenE (k1 := r + 1) (by omega) (by omega) (OutA := fun σ' ↦ AgreeBelow r σ3 σ')
      ⟨fun _ ↦ chain * x, ?_⟩ fun σ4 ha4 _ ↦
        ⟨fun i ↦ [word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0,
          x * word 2 0 0].getD (i - (r + 1)) 0, ?_⟩
    · intro σ' ha hv
      have v0 : σ' (.n r) = chain * x := hv r le_rfl (by omega)
      have p0 : σ' (.n 0) = x := by rw [ha 0 (by omega), e3 0 (by omega), g0]
      have p4 : σ' (.n 4) = chain := by rw [ha 4 (by omega), e3 4 (by omega), g4]
      have pS : σ' (.n st.2.1) = R := by rw [ha _ o2.2, hS]
      refine ⟨?_, ha⟩
      simp only [allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds]
      exact ⟨by rw [v0, p4, p0], by rw [pS, v0]; exact ls⟩
    · intro σ' ha hv
      have V : ∀ j < 5, σ' (.n (r + 1 + j)) =
          [word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0].getD j 0 :=
        fun j hj ↦ by rw [hv _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
      have p0' : σ' (.n 0) = x := by
        rw [ha 0 (by omega), ha4 0 (by omega), e3 0 (by omega), g0]
      have p1' : σ' (.n 1) = N := by
        rw [ha 1 (by omega), ha4 1 (by omega), e3 1 (by omega), g1]
      refine ⟨?_, trivial⟩
      simp only [osLoopTailA, allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds]
      exact ⟨v0, by rw [v1, p0', v0], by rw [v2, v1, p1'], v3, by rw [v4, p0', v3]⟩
  obtain ⟨f, hf⟩ := hB
  set σ := fill σ0 6 (r + 1 + 5) f
  have hA := (hf σ (agree_fill _ _ _ _) (range_fill _ _ _ _)).1
  have hlow : ∀ i < 6, σ (.n i) = σ0 (.n i) := fun i hi ↦ fill_lt hi
  obtain ⟨t2, t4⟩ := osLoopTailA_val (allOk_append.mp hA).2
  refine ⟨σ, ?_, hA, ?_, ?_⟩
  · simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, hlow 0 (by omega), hlow 1 (by omega), hlow 2 (by omega),
      hlow 3 (by omega), hlow 4 (by omega), hlow 5 (by omega), g0, g1, g2, g3, g4, g5]
  · rw [t2, hlow 0 (by omega), hlow 1 (by omega), g0, g1]
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, hlow 0 (by omega), hlow 1 (by omega), hlow 2 (by omega),
      hlow 3 (by omega), hlow 4 (by omega), hlow 5 (by omega), g0, g1, g2, g3, g4, g5]

/-- **The residual loop, honestly**: entered from `1` with the bound `g^n`, `0 < n`, on a memory
where every iteration's meaning holds. -/
theorem resLoop_rel {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (lvl : ℕ) (lv : OsLv) (hps : fn.params = osParams 6)
    (hb : fn.body = resLoopBody lvl lv name) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) {D : ℕ → E} {n : ℕ}
    (hn0 : 0 < n) (qpos bd chain mu : E)
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    (hit : ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff qpos chain mu (gen ^ j)) :
    IsInK (1 + gen ^ n) ∧ (1 + gen ^ n ≠ 0 →
      coreProgram.Rel rd name [1, gen ^ n, qpos, bd, chain, mu] []) := by
  rw [resLoopBody_split] at hb
  refine loop_complete (rest := [qpos, bd, chain, mu]) hf (resLoopA_flat lvl lv) hb hn0 rfl
    fun j hj ↦ ?_
  obtain ⟨σ, hp, hA, hg, ha⟩ := resIter_complete (C := coreProgram.Rel rd) lvl lv hml hpo
    (gen ^ j) (gen ^ n) qpos bd chain mu hD (hit j hj)
  exact ⟨σ, by rw [hps]; exact hp, hA, hg, ha⟩

/-! ## Placed -/

theorem pureList_eq_all (S : List String) : ∀ l : List Stmt, Stmt.pureList S l = l.all (Stmt.pure S)
  | [] => rfl
  | s :: l => by simp [Stmt.pureList, pureList_eq_all S l]

theorem osResQ_mem (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ), ∀ s ∈ (osResQ pos bd row vo n t pe k).1,
    ∃ a, s = .atom a ∧ atomUnplaced a = true
  | 0, _, _, _, s, hs => by simp [osResQ] at hs
  | n + 1, t, pe, k, s, hs => by
    simp only [osResQ, List.cons_append, List.mem_cons, List.nil_append] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | hs
    all_goals first
      | exact ⟨_, rfl, rfl⟩
      | exact osResQ_mem pos bd row vo n (t + 1) (k + 5) (k + 6) s hs

theorem osResQuery_pure (S : List String) (pos bd row vo n k : ℕ) :
    ∀ s ∈ (osResQuery pos bd row vo n k).1, Stmt.pure S s = true := by
  intro s hs
  simp only [osResQuery, List.cons_append, List.nil_append, List.mem_cons] at hs
  rcases hs with rfl | rfl | hs
  · rfl
  · rfl
  · obtain ⟨a, rfl, ha⟩ := osResQ_mem pos bd row vo _ _ _ _ s hs; exact ha

theorem osResSteps_pure (S : List String) (pp bd row vo ncols mu : ℕ) :
    ∀ (js : List ℕ) (h k : ℕ), ∀ s ∈ (osResSteps pp bd row vo ncols mu js h k).1,
      Stmt.pure S s = true
  | [], _, _, s, hs => by simp [osResSteps] at hs
  | j :: js, h, k, s, hs => by
    simp only [osResSteps, osResStep, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with ((rfl | hs) | rfl | rfl) | hs
    · rfl
    · exact osResQuery_pure S _ _ _ _ _ _ s hs
    · rfl
    · rfl
    · exact osResSteps_pure S pp bd row vo ncols mu js _ _ s hs

theorem resLoopBody_pure (lvl : ℕ) (lv : OsLv) (name : String) :
    Stmt.pureList [name] (resLoopBody lvl lv name) = true := by
  have hm : ∀ b o k, ∀ s ∈ (osMat b o k).1, Stmt.pure [name] s = true := by
    intro b o k s hs
    rcases osMat_mem b o k s hs with ⟨d, c, rfl⟩ | ⟨d, a, b, rfl⟩ <;> rfl
  rw [pureList_eq_all, resLoopBody_split]
  simp only [resLoopA, osLoopTailA, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    List.all_eq_true.mpr (hm _ _ _), List.all_eq_true.mpr (osResSteps_pure [name] _ _ _ _ _ _ _ _ _)]
  simp [Stmt.pure, atomUnplaced]

/-- **The residual loop helper is pure.** -/
theorem resLoop_pureIn {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (lvl : ℕ) (lv : OsLv) (hb : fn.body = resLoopBody lvl lv name) :
    coreProgram.PureIn [name] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf] at hf'
  cases hf'
  rw [hb]
  exact resLoopBody_pure lvl lv g

/-- **The residual loop, placed**: on every memory holding the caller's words `Lin` where the
row's words and every iteration's meaning hold, entered behind a nonzero guard. -/
theorem resLoop_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {name : String}
    {fn : Fn} (hf : coreProgram.find? name = some fn) (lvl : ℕ) (lv : OsLv)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody lvl lv name)
    (hml : 1 ≤ lv.logCols) (hpo : lv.posOff < u128Bound)
    {D : ℕ → E} {n : ℕ} (hn0 : 0 < n) (hne : 1 + gen ^ n ≠ 0) {qpos bd chain mu : E}
    {Lin : Layout}
    (hmem : ∀ rd, MemL rd Lin → (∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s)) ∧
      ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff qpos chain mu (gen ^ j)) :
    CompleteAtD fs cert k name Lin [1, gen ^ n, qpos, bd, chain, mu] (Returns []) :=
  completeAt_of_rel_pureD (resLoop_pureIn hf lvl lv hb) (List.mem_singleton_self name)
    (fun rd hm ↦ (resLoop_rel hf lvl lv hps hb hml hpo hn0 qpos bd chain mu (hmem rd hm).1
      (hmem rd hm).2).2 hne) k

/-- **The residual loop, placed, by a bounded tree**: as `resLoop_completeAtD`, by a tree of at
most `B` words, `B` bounding the loop's valid trees at the call's arguments. -/
theorem resLoop_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {name : String}
    {fn : Fn} (hf : coreProgram.find? name = some fn) (lvl : ℕ) (lv : OsLv)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody lvl lv name)
    (hml : 1 ≤ lv.logCols) (hpo : lv.posOff < u128Bound)
    {D : ℕ → E} {n : ℕ} (hn0 : 0 < n) (hne : 1 + gen ^ n ≠ 0) {qpos bd chain mu : E}
    {Lin : Layout}
    (hmem : ∀ rd, MemL rd Lin → (∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s)) ∧
      ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff qpos chain mu (gen ^ j))
    {B : ℕ} (hB : ∀ rd (t : Tree), t.name = name →
      t.Valid coreProgram rd [1, gen ^ n, qpos, bd, chain, mu] [] → t.BufsOk coreProgram →
        t.total fs ≤ B) :
    CompleteAtB fs cert k name Lin [1, gen ^ n, qpos, bd, chain, mu] (Returns []) B :=
  completeAt_of_rel_pureBat (resLoop_pureIn hf lvl lv hb) (List.mem_singleton_self name)
    (fun rd hm ↦ (resLoop_rel hf lvl lv hps hb hml hpo hn0 qpos bd chain mu (hmem rd hm).1
      (hmem rd hm).2).2 hne) k hB

end
end LeanVM.Guest.B1
