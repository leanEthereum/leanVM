/-
  LeanVM.Guest.B1.Whir.ResLoop

  The residual loop of `open_stacked` (eight queries' `residual_query` an iteration, chained by
  `μ = 1/λ`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Whir.ResQuery

/-!
# The residual loop (G:1730-1739)

A residual step (`osResStep`) reads a position and runs `h ← (h + R(p))·μ`, `R` the level's
`residual_query`: `osResSteps_val`, the chain `resFold` over the positions read. At `x = g^j` the
loop's iteration reads the positions `8j .. 8j + 7` at `qpos·g^po·x^8`, `h = chain[x]`, and stores
`chain[x·g]` = the eight steps from `h` (`ResIter`; `resLoop_sound`). `resChain`: from
`chain[0] = 0`, `chain[j]` is the steps over the first `8j` positions.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The residual chain's steps `h ← (h + R(p))·μ` over the positions `ps`, `R` the residual on
the vanishing values from `vo` and the row's words `D` over `ml` coordinates. -/
def resFold (D : ℕ → E) (vo ml : ℕ) (mu h : E) (ps : List E) : E :=
  ps.foldl (fun a p ↦ (a + residualProd (osVals vo ml) p D ml) * mu) h

theorem resFold_append (D : ℕ → E) (vo ml : ℕ) (mu h : E) (ps qs : List E) :
    resFold D vo ml mu h (ps ++ qs) = resFold D vo ml mu (resFold D vo ml mu h ps) qs := by
  simp [resFold, List.foldl_append]

/-- **The residual steps**: each reads its position at `pp·g^j` and advances the chain. -/
theorem osResSteps_val {C : CallRel} {σ : Val} {pp bd row vo ncols mu : ℕ} (hn : 1 ≤ ncols)
    {D : ℕ → E} (hD : ∀ s < ncols, LoadHolds rd (σ (.n bd)) (row + s) (D s)) :
    ∀ (js : List ℕ) (h k : ℕ), AllOk C rd σ (osResSteps pp bd row vo ncols mu js h k).1 →
      ∃ ps : List E, List.Forall₂ (fun j p ↦ LoadHolds rd (σ (.n pp)) j p) js ps ∧
        σ (.n (osResSteps pp bd row vo ncols mu js h k).2.1) =
          resFold D vo ncols (σ (.n mu)) (σ (.n h)) ps
  | [], h, k, _ => ⟨[], .nil, by simp [osResSteps, resFold]⟩
  | j :: js, h, k, hok => by
    simp only [osResSteps, osResStep] at hok ⊢
    rw [allOk_append, allOk_append, allOk_append] at hok
    obtain ⟨⟨⟨hl, he⟩, hc⟩, hr⟩ := hok
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hl hc
    have hv := osResQuery_val hn hD he
    obtain ⟨ps, hF, hps⟩ := osResSteps_val hn hD js _ _ hr
    refine ⟨σ (.n k) :: ps, .cons hl hF, ?_⟩
    rw [hps, resFold, resFold, List.foldl_cons, hc.2, hc.1, hv]

/-- **One iteration of the residual loop at `x`**, the row's words `D`: eight positions read at
`qpos·g^po·x^8`, `chain[x·g]` the steps from `chain[x]` over them. -/
def ResIter (rd : Reader) (D : ℕ → E) (vo ml po : ℕ) (qpos chain mu x : E) : Prop :=
  ∃ (h : E) (ps : List E), ps.length = resBatch ∧
    (∀ i < resBatch, LoadHolds rd (qpos * gen ^ po * x ^ resBatch) i (ps.getD i 0)) ∧
    LoadHolds rd (chain * x) 0 h ∧ LoadHolds rd (chain * x) 1 (resFold D vo ml mu h ps)

/-- The residual loop's body before its tail. -/
def resLoopA (lvl : ℕ) (lv : OsLv) : List Stmt :=
  let pp := osMat 2 lv.posOff 6
  let x := pp.2.2
  let st := osResSteps (x + 3) 3 (lvl * ligColsCap) lv.vanish lv.logCols 5 (List.range resBatch)
    (x + 5) (x + 6)
  let r := st.2.2
  pp.1 ++ [.atom (.mul (.n x) (.n 0) (.n 0)), .atom (.mul (.n (x + 1)) (.n x) (.n x)),
    .atom (.mul (.n (x + 2)) (.n (x + 1)) (.n (x + 1))), .atom (.mul (.n (x + 3)) (.n pp.2.1) (.n (x + 2))),
    .atom (.mul (.n (x + 4)) (.n 4) (.n 0)), .atom (.load (.n (x + 5)) (.n (x + 4)) 0)] ++ st.1 ++
    [.atom (.mul (.n r) (.n 4) (.n 0)), .atom (.load (.n st.2.1) (.n r) 1)]

/-- The tail's first value. -/
def resLoopR (lvl : ℕ) (lv : OsLv) : ℕ :=
  (osResSteps ((osMat 2 lv.posOff 6).2.2 + 3) 3 (lvl * ligColsCap) lv.vanish lv.logCols 5
    (List.range resBatch) ((osMat 2 lv.posOff 6).2.2 + 5) ((osMat 2 lv.posOff 6).2.2 + 6)).2.2 + 1

theorem resLoopBody_split (lvl : ℕ) (lv : OsLv) (name : String) :
    resLoopBody lvl lv name = (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv)) ++
      [.callIf (.n (resLoopR lvl lv + 2)) name
        (.n (resLoopR lvl lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
  simp only [resLoopBody, resLoopA, resLoopR, osLoopTail_split, List.append_assoc]

theorem osResQ_flat (pos bd row vo : ℕ) : ∀ n t pe k,
    (osResQ pos bd row vo n t pe k).1.all Stmt.flat = true
  | 0, _, _, _ => rfl
  | n + 1, t, pe, k => by
    simp [osResQ, Stmt.flat, osResQ_flat pos bd row vo n (t + 1) (k + 5) (k + 6)]

theorem osResQuery_flat (pos bd row vo n k : ℕ) :
    (osResQuery pos bd row vo n k).1.all Stmt.flat = true := by
  simp [osResQuery, Stmt.flat, osResQ_flat]

theorem osResSteps_flat (pp bd row vo ncols mu : ℕ) : ∀ (js : List ℕ) (h k : ℕ),
    (osResSteps pp bd row vo ncols mu js h k).1.all Stmt.flat = true
  | [], _, _ => rfl
  | j :: js, h, k => by
    simp [osResSteps, osResStep, Stmt.flat, osResQuery_flat, osResSteps_flat pp bd row vo ncols mu js]

theorem resLoopA_flat (lvl : ℕ) (lv : OsLv) :
    (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv)).all Stmt.flat = true := by
  have hm : ∀ b o k, (osMat b o k).1.all Stmt.flat = true := by
    intro b o k; unfold osMat; split_ifs <;> rfl
  simp [resLoopA, osLoopTailA, hm, osResSteps_flat, Stmt.flat]

theorem forall₂_range_to {P : ℕ → E → Prop} : ∀ (n : ℕ) (ps : List E),
    List.Forall₂ P (List.range n) ps → ps.length = n ∧ ∀ i < n, P i (ps.getD i 0) := by
  intro n ps h
  have hl : ps.length = n := by simpa using h.length_eq.symm
  refine ⟨hl, fun i hi ↦ ?_⟩
  have := List.forall₂_iff_get.mp h
  have h2 := this.2 i (by simpa using hi) (by omega)
  simpa [List.getD_eq_getElem?_getD, hl, hi] using h2

/-- **The residual loop's iteration**: from its body's atoms at `x`, the iteration's meaning, the
guard `x·g + N` and the next call's arguments. -/
theorem resLoop_step (lvl : ℕ) (lv : OsLv) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) {D : ℕ → E}
    (σ : Val) (x N qpos bd chain mu : E) (hp : (osParams 6).map σ = [x, N, qpos, bd, chain, mu])
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    {C : CallRel} (hA : AllOk C rd σ (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv))) :
    ResIter rd D lv.vanish lv.logCols lv.posOff qpos chain mu x ∧
      σ (.n (resLoopR lvl lv + 2)) = x * gen + N ∧
      (.n (resLoopR lvl lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, qpos, bd, chain, mu] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · unfold resLoopA at hA
    set pp := osMat 2 lv.posOff 6
    set y := pp.2.2
    set st := osResSteps (y + 3) 3 (lvl * ligColsCap) lv.vanish lv.logCols 5 (List.range resBatch)
      (y + 5) (y + 6)
    set r := st.2.2
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
    obtain ⟨⟨⟨hpp, m0, m1, m2, m3, m4, l5⟩, hst⟩, mr, sr⟩ := hA
    have hD' : ∀ s < lv.logCols, LoadHolds rd (σ (.n 3)) (lvl * ligColsCap + s) (D s) := by
      rw [h3]; exact hD
    have hP : σ (.n (y + 3)) = qpos * gen ^ lv.posOff * x ^ resBatch := by
      rw [m3, osMat_val hpo hpp, m2, m1, m0, h0, h2]; ring
    have hC : σ (.n (y + 4)) = chain * x := by rw [m4, h4, h0]
    have hR : σ (.n r) = chain * x := by rw [mr, h4, h0]
    obtain ⟨ps, hF, hv⟩ := osResSteps_val hml hD' _ _ _ hst
    obtain ⟨hl, hF⟩ := forall₂_range_to _ _ hF
    rw [hP] at hF
    rw [hC] at l5
    rw [hR, hv, h5] at sr
    exact ⟨σ (.n (y + 5)), ps, hl, hF, l5, sr⟩
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]


/-- **The residual loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`, the
iteration's meaning holds at every `g^j`, `j < n`. -/
theorem resLoop_sound {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (lvl : ℕ) (lv : OsLv) (hps : fn.params = osParams 6)
    (hb : fn.body = resLoopBody lvl lv name) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) {D : ℕ → E}
    {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (qpos bd chain mu : E)
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, qpos, bd, chain, mu] []) :
    ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff qpos chain mu (gen ^ j) := by
  rw [resLoopBody_split] at hb
  refine loop_guarded (rest := [qpos, bd, chain, mu]) hn0 hn rfl
    (loop_sound_flat hf (resLoopA_flat lvl lv) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact resLoop_step lvl lv hml hpo σ x (gen ^ n) qpos bd chain mu hp hD hA

/-- **The chain**: from `chain[0] = 0`, after `j ≤ n` iterations `chain[j]` is the steps over the
first `8j` positions `P` in memory. -/
theorem resChain {D : ℕ → E} {vo ml po : ℕ} {qpos chain mu : E} {n : ℕ} {P : ℕ → E}
    (hP : ∀ i < resBatch * n, LoadHolds rd qpos (po + i) (P i))
    (h0 : LoadHolds rd chain 0 0)
    (hit : ∀ j < n, ResIter rd D vo ml po qpos chain mu (gen ^ j)) :
    ∀ j ≤ n, LoadHolds rd chain j
      (resFold D vo ml mu 0 ((List.range (resBatch * j)).map P)) := by
  intro j
  induction j with
  | zero => intro _; simpa [resFold] using h0
  | succ j ih =>
    intro hj
    obtain ⟨h, ps, hl, hps, lh, ls⟩ := hit j (by omega)
    have hx : (gen ^ j) ^ resBatch = gen ^ (resBatch * j) := by rw [← pow_mul, Nat.mul_comm]
    rw [loadHolds_mul_gen_pow] at lh ls
    have eh := loadHolds_unique lh (by simpa using ih (by omega))
    have eps : ps = (List.range resBatch).map fun i ↦ P (resBatch * j + i) := by
      refine List.ext_getElem (by simp [hl]) fun i h1 h2 ↦ ?_
      have := hps i (by omega)
      rw [hx, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ h1] at this
      simp only [List.getElem_map, List.getElem_range]
      exact loadHolds_unique this (by
        have := hP (resBatch * j + i) (by simp at h2; nlinarith)
        rwa [← Nat.add_assoc] at this)
    rw [eh, eps, ← resFold_append] at ls
    rw [show resBatch * (j + 1) = resBatch * j + resBatch by ring, List.range_add, List.map_append,
      List.map_map]
    exact ls

end
end LeanVM.Guest.B1.Whir
