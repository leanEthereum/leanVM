/-
  LeanVM.Guest.B1.Whir.ResLoop

  The residual loop of `open_stacked` (`resBatch` queries' `residual_query` an iteration, two chains
  by `μ = 1/λ`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Whir.ResQuery

/-!
# The residual loop

A residual step (`osResStep`) reads a position `p` and runs `h ← (h + P(p))·μ`,
`hh ← (hh + H(p))·μ`, `P` the level's `residual_query` product and `H` its high part's share:
`osResSteps_val`, the chains `resFold` over the positions read. At `x = g^j` the loop's iteration
reads the positions `bj .. bj + b - 1` at `qpos·g^po·x^b` (`b = resBatch`), `h, hh = chain[2j],
chain[2j + 1]`, and stores `chain[2j + 2], chain[2j + 3]` (`ResIter`; `resLoop_sound`). `resChain`:
from `chain[0] = chain[1] = 0`, `chain[2j], chain[2j + 1]` are the chains over the first
`bj` positions. `resFold_mul_pow`: `λ^n` times a chain from `0` is `Σ_k λ^k d_k`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {P : Program} {rd : Reader}

/-- The two chains `h ← (h + P(p))·μ`, `hh ← (hh + H(p))·μ` over the positions `ps`. -/
def resFold (P H : E → E) (mu : E) (a : E × E) (ps : List E) : E × E :=
  ps.foldl (fun a p ↦ ((a.1 + P p) * mu, (a.2 + H p) * mu)) a

theorem resFold_append (P H : E → E) (mu : E) (a : E × E) (ps qs : List E) :
    resFold P H mu a (ps ++ qs) = resFold P H mu (resFold P H mu a ps) qs := by
  simp [resFold, List.foldl_append]

/-- **A chain times `λ^n`**, `λ·μ = 1`, from `a`: `a + Σ_k λ^k d_k`. -/
theorem chain_mul_pow {lam mu : E} (hlm : lam * mu = 1) (d : E → E) :
    ∀ (ps : List E) (a : E), lam ^ ps.length * ps.foldl (fun a p ↦ (a + d p) * mu) a =
      a + ∑ k ∈ Finset.range ps.length, lam ^ k * d (ps.getD k 0)
  | [], a => by simp
  | p :: ps, a => by
    have ih := chain_mul_pow hlm d ps ((a + d p) * mu)
    rw [List.foldl_cons, List.length_cons, pow_succ', mul_assoc, ih, Finset.sum_range_succ', mul_add,
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul]
    have e : lam * ((a + d p) * mu) = a + d p := by linear_combination (a + d p) * hlm
    rw [e]
    have e2 : ∀ k, lam * (lam ^ k * d (ps.getD k 0)) = lam ^ (k + 1) * d (ps.getD k 0) :=
      fun k ↦ by ring
    simp only [e2]
    ring

theorem resFold_fst (P H : E → E) (mu : E) :
    ∀ (ps : List E) (a : E × E),
      (resFold P H mu a ps).1 = ps.foldl (fun x p ↦ (x + P p) * mu) a.1
  | [], _ => rfl
  | p :: ps, a => by simp only [resFold, List.foldl_cons] at *; exact resFold_fst P H mu ps _

theorem resFold_snd (P H : E → E) (mu : E) :
    ∀ (ps : List E) (a : E × E),
      (resFold P H mu a ps).2 = ps.foldl (fun x p ↦ (x + H p) * mu) a.2
  | [], _ => rfl
  | p :: ps, a => by simp only [resFold, List.foldl_cons] at *; exact resFold_snd P H mu ps _

/-- **The residual steps**: each reads its position at `pp·g^j` and advances the chains. -/
theorem osResSteps_val {C : CallRel} {σ : Val} {pp bd ro hp ho vo ncols nhs hbits mu : ℕ}
    (hn : 1 ≤ ncols) (hh1 : 1 ≤ nhs) (hb3 : hbits ≤ 3) (hbn : hbits ≤ ncols + 1)
    {D : ℕ → E} {hsv : List E}
    (hD : ∀ s < ncols, LoadHolds rd (σ (.n bd)) (ro + s) (D s)) (hlen : hsv.length = nhs)
    (hload : ∀ c < nhs, LoadHolds rd (σ (.n hp)) (ho + c) (hsv.getD c 0)) :
    ∀ (js : List ℕ) (h hh k : ℕ),
      AllOk C rd σ (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).1 →
      ∃ ps : List E, List.Forall₂ (fun j p ↦ LoadHolds rd (σ (.n pp)) j p) js ps ∧
        (σ (.n (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.1),
          σ (.n (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.2.1)) =
          resFold (fun x ↦ residualProd (osVals vo ncols) x D ncols)
            (fun x ↦ residualChain (osVals vo ncols) x ncols *
              novelSum hsv (residualChain (osVals vo ncols) x) nhs hbits)
            (σ (.n mu)) (σ (.n h), σ (.n hh)) ps
  | [], h, hh, k, _ => ⟨[], .nil, by simp [osResSteps, resFold]⟩
  | j :: js, h, hh, k, hok => by
    simp only [osResSteps, osResStep] at hok ⊢
    rw [allOk_append, allOk_append, allOk_cons] at hok
    obtain ⟨⟨⟨hl, hq⟩, hc⟩, hr⟩ := hok
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_add, holds_mul,
      osLd, osAdd, osMul] at hl hc
    obtain ⟨p1, p2⟩ := osResQuery_val hn hh1 hb3 hbn hD hlen hload hq
    obtain ⟨ps, hF, hps⟩ := osResSteps_val hn hh1 hb3 hbn hD hlen hload js _ _ _ hr
    refine ⟨σ (.n k) :: ps, .cons hl hF, ?_⟩
    rw [hps, resFold, resFold, List.foldl_cons]
    obtain ⟨a1, m1, a2, m2⟩ := hc
    rw [m1, a1, m2, a2, p1, p2]

/-! ## Flatness -/

theorem osResChain_flat (bd ro vo ncols : ℕ) : ∀ (f t ch pe : ℕ) (ws : List ℕ) (k : ℕ),
    (osResChain bd ro vo ncols f t ch pe ws k).1.all Stmt.flat = true
  | 0, _, _, _, _, _ => rfl
  | f + 1, t, ch, pe, ws, k => by
    unfold osResChain
    split_ifs <;> simp [Stmt.flat, osResChain_flat bd ro vo ncols f]

theorem osNovelLevel_flat (hp ho : ℕ) (ins : Option (List ℕ)) (nIn w : ℕ) :
    ∀ (f k : ℕ), (osNovelLevel hp ho ins nIn w f k).1.all Stmt.flat = true
  | 0, _ => rfl
  | f + 1, k => by
    unfold osNovelLevel
    simp only [List.all_append, osNovelLevel_flat hp ho ins nIn w f, Bool.and_true]
    rcases ins with _ | vs <;> split_ifs <;> simp [Stmt.flat]

theorem osNovelLevels_flat (hp ho n nbits : ℕ) (ws : List ℕ) :
    ∀ (f i : ℕ) (ins : Option (List ℕ)) (k : ℕ),
      (osNovelLevels hp ho n nbits ws f i ins k).1.all Stmt.flat = true
  | 0, _, _, _ => rfl
  | f + 1, i, ins, k => by
    unfold osNovelLevels
    simp only [List.all_append, osNovelLevel_flat, osNovelLevels_flat hp ho n nbits ws f,
      Bool.and_self]

theorem osResQuery_flat (pos bd ro hp ho vo ncols nhs hbits k : ℕ) :
    (osResQuery pos bd ro hp ho vo ncols nhs hbits k).1.all Stmt.flat = true := by
  unfold osResQuery osNovelEval
  split_ifs <;> simp [Stmt.flat, osResChain_flat, osNovelLevels_flat]

theorem osResSteps_flat (pp bd ro hp ho vo ncols nhs hbits mu : ℕ) :
    ∀ (js : List ℕ) (h hh k : ℕ),
      (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).1.all Stmt.flat = true
  | [], _, _, _ => rfl
  | j :: js, h, hh, k => by
    simp [osResSteps, osResStep, Stmt.flat, osResQuery_flat,
      osResSteps_flat pp bd ro hp ho vo ncols nhs hbits mu js]

/-! ## The loop -/

/-- **One iteration of the residual loop at `x`**: `resBatch` positions read at
`qpos·g^po·x^resBatch`, the
chains at `chain·x^2` (cells `0, 1`) advanced over them into cells `2, 3`. -/
def ResIter (rd : Reader) (P H : E → E) (po : ℕ) (qpos chain mu x : E) : Prop :=
  ∃ (a : E × E) (ps : List E), ps.length = resBatch ∧
    (∀ i < resBatch, LoadHolds rd (qpos * gen ^ po * x ^ resBatch) i (ps.getD i 0)) ∧
    LoadHolds rd (chain * x ^ 2) 0 a.1 ∧ LoadHolds rd (chain * x ^ 2) 1 a.2 ∧
    LoadHolds rd (chain * x ^ 2) 2 (resFold P H mu a ps).1 ∧
    LoadHolds rd (chain * x ^ 2) 3 (resFold P H mu a ps).2

/-- The residual loop's body before its tail. -/
def resLoopA (lvl : ℕ) (lv : OsLv) : List Stmt :=
  let pp := osMat 2 lv.posOff 7
  let x := pp.2.2
  let y := x + batchLen
  let st := osResSteps y 3 (lvl * ligColsCap) 4 (lvl * hsStride) lv.vanish lv.logCols lv.folds
    lv.highBits 6 (List.range resBatch) (y + 3) (y + 4) (y + 5)
  pp.1 ++ (osBatchPow x).1 ++ [osMul y pp.2.1 (osBatchPow x).2, osMul (y + 1) 5 0,
    osMul (y + 2) (y + 1) 0, osLd (y + 3) (y + 2) 0, osLd (y + 4) (y + 2) 1] ++ st.1 ++
    [osLd st.2.1 (y + 2) 2, osLd st.2.2.1 (y + 2) 3]

/-- The tail's first value. -/
def resLoopR (lvl : ℕ) (lv : OsLv) : ℕ :=
  (osResSteps ((osMat 2 lv.posOff 7).2.2 + batchLen) 3 (lvl * ligColsCap) 4 (lvl * hsStride)
    lv.vanish lv.logCols lv.folds lv.highBits 6 (List.range resBatch)
    ((osMat 2 lv.posOff 7).2.2 + batchLen + 3) ((osMat 2 lv.posOff 7).2.2 + batchLen + 4)
    ((osMat 2 lv.posOff 7).2.2 + batchLen + 5)).2.2.2

/-- `osBatchPow`'s digits spell `resBatch`. -/
theorem batch_digits : digitsVal (osPowDigits resBatch) 1 = resBatch := by decide +kernel

/-- **`osBatchPow` computes `x^resBatch`**, `x` the value `0`. -/
theorem osBatchPow_val {C : CallRel} {σ : Val} (k : ℕ) (h : AllOk C rd σ (osBatchPow k).1) :
    σ (.n (osBatchPow k).2) = σ (.n 0) ^ resBatch := by
  rw [← batch_digits]
  exact osPowSteps_val 0 (osPowDigits resBatch) 0 k 1 (pow_one _).symm h

theorem resLoopBody_split (lvl : ℕ) (lv : OsLv) (name : String) :
    resLoopBody lvl lv name = (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv)) ++
      [.callIf (.n (resLoopR lvl lv + 2)) name
        (.n (resLoopR lvl lv + 4) :: (List.range (7 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
  simp only [resLoopBody, resLoopA, resLoopR, osLoopTail_split, List.append_assoc]

theorem resLoopA_flat (lvl : ℕ) (lv : OsLv) :
    (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv)).all Stmt.flat = true := by
  have hm : ∀ b o k, (osMat b o k).1.all Stmt.flat = true := by
    intro b o k; unfold osMat; split_ifs <;> rfl
  simp [resLoopA, osLoopTailA, hm, osResSteps_flat, osBatchPow, osPowSteps_flat, Stmt.flat]

theorem forall₂_range_to {P : ℕ → E → Prop} : ∀ (n : ℕ) (ps : List E),
    List.Forall₂ P (List.range n) ps → ps.length = n ∧ ∀ i < n, P i (ps.getD i 0) := by
  intro n ps h
  have hl : ps.length = n := by simpa using h.length_eq.symm
  refine ⟨hl, fun i hi ↦ ?_⟩
  have := List.forall₂_iff_get.mp h
  have h2 := this.2 i (by simpa using hi) (by omega)
  simpa [List.getD_eq_getElem?_getD, hl, hi] using h2

/-- What a level's `residual_query` reads: its basis row `D` at `bd`, its high part at `hs`. -/
structure ResRead (rd : Reader) (lvl : ℕ) (lv : OsLv) (bd hs : E) (D : ℕ → E) (hsv : List E) :
    Prop where
  cols : 1 ≤ lv.logCols
  nhs : 1 ≤ lv.folds
  b3 : lv.highBits ≤ 3
  bn : lv.highBits ≤ lv.logCols + 1
  D : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s)
  len : hsv.length = lv.folds
  hs : ∀ c < lv.folds, LoadHolds rd hs (lvl * hsStride + c) (hsv.getD c 0)

/-- A level's residual product, `residual_query`'s first value. -/
def resP (lv : OsLv) (D : ℕ → E) (x : E) : E :=
  residualProd (osVals lv.vanish lv.logCols) x D lv.logCols

/-- A level's high share, `residual_query`'s second value. -/
def resH (lv : OsLv) (hsv : List E) (x : E) : E :=
  residualChain (osVals lv.vanish lv.logCols) x lv.logCols *
    novelSum hsv (residualChain (osVals lv.vanish lv.logCols) x) lv.folds lv.highBits

/-- **The residual loop's iteration**: from its body's atoms at `x`, the iteration's meaning, the
guard `x·g + N` and the next call's arguments. -/
theorem resLoop_step (lvl : ℕ) (lv : OsLv) (hpo : lv.posOff < u128Bound) {D : ℕ → E}
    {hsv : List E} (σ : Val) (x N qpos bd hs chain mu : E)
    (hp : (osParams 7).map σ = [x, N, qpos, bd, hs, chain, mu])
    (hR : ResRead rd lvl lv bd hs D hsv)
    {C : CallRel} (hA : AllOk C rd σ (resLoopA lvl lv ++ osLoopTailA (resLoopR lvl lv))) :
    ResIter rd (resP lv D) (resH lv hsv) lv.posOff qpos chain mu x ∧
      σ (.n (resLoopR lvl lv + 2)) = x * gen + N ∧
      (.n (resLoopR lvl lv + 4) :: (List.range (7 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, qpos, bd, hs, chain, mu] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · unfold resLoopA at hA
    simp only at hA
    set pp := osMat 2 lv.posOff 7
    set y := pp.2.2 + batchLen
    set st := osResSteps y 3 (lvl * ligColsCap) 4 (lvl * hsStride) lv.vanish lv.logCols lv.folds
      lv.highBits 6 (List.range resBatch) (y + 3) (y + 4) (y + 5)
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, holds_load,
      osMul, osLd] at hA
    obtain ⟨⟨⟨⟨hpp, hpw⟩, m3, m4, m5, l6, l7⟩, hst⟩, s1, s2⟩ := hA
    have hD' : ∀ s < lv.logCols, LoadHolds rd (σ (.n 3)) (lvl * ligColsCap + s) (D s) := by
      rw [h3]; exact hR.D
    have hH' : ∀ c < lv.folds, LoadHolds rd (σ (.n 4)) (lvl * hsStride + c) (hsv.getD c 0) := by
      rw [h4]; exact hR.hs
    have hP : σ (.n y) = qpos * gen ^ lv.posOff * x ^ resBatch := by
      rw [m3, osMat_val hpo hpp, osBatchPow_val _ hpw, h0, h2]
    have hC : σ (.n (y + 2)) = chain * x ^ 2 := by rw [m5, m4, h5, h0]; ring
    obtain ⟨ps, hF, hv⟩ := osResSteps_val hR.cols hR.nhs hR.b3 hR.bn hD' hR.len hH' _ _ _ _ hst
    obtain ⟨hl, hF⟩ := forall₂_range_to _ _ hF
    rw [hP] at hF
    rw [hC] at l6 l7 s1 s2
    rw [h6] at hv
    refine ⟨(σ (.n (y + 3)), σ (.n (y + 4))), ps, hl, hF, l6, l7, ?_, ?_⟩
    · have := congrArg Prod.fst hv; simp only at this
      show LoadHolds _ _ _ (resFold (fun x ↦ residualProd (osVals lv.vanish lv.logCols) x D lv.logCols)
        (fun x ↦ residualChain (osVals lv.vanish lv.logCols) x lv.logCols *
          novelSum hsv (residualChain (osVals lv.vanish lv.logCols) x) lv.folds lv.highBits)
        mu _ ps).1
      rw [← this]; exact s1
    · have := congrArg Prod.snd hv; simp only at this
      show LoadHolds _ _ _ (resFold (fun x ↦ residualProd (osVals lv.vanish lv.logCols) x D lv.logCols)
        (fun x ↦ residualChain (osVals lv.vanish lv.logCols) x lv.logCols *
          novelSum hsv (residualChain (osVals lv.vanish lv.logCols) x) lv.folds lv.highBits)
        mu _ ps).2
      rw [← this]; exact s2
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5, h6]

/-- **The residual loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`, the
iteration's meaning holds at every `g^j`, `j < n`. -/
theorem resLoop_sound {name : String} {fn : Fn} (hf : P.find? name = some fn)
    (lvl : ℕ) (lv : OsLv) (hps : fn.params = osParams 7)
    (hb : fn.body = resLoopBody lvl lv name) (hpo : lv.posOff < u128Bound) {D : ℕ → E}
    {hsv : List E} {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (qpos bd hs chain mu : E)
    (hR : ResRead rd lvl lv bd hs D hsv)
    (hg : 1 + gen ^ n ≠ 0 → P.Rel rd name [1, gen ^ n, qpos, bd, hs, chain, mu] []) :
    ∀ j < n, ResIter rd (resP lv D) (resH lv hsv) lv.posOff qpos chain mu (gen ^ j) := by
  rw [resLoopBody_split] at hb
  refine loop_guarded (rest := [qpos, bd, hs, chain, mu]) hn0 hn rfl
    (loop_sound_flat hf (resLoopA_flat lvl lv) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact resLoop_step lvl lv hpo σ x (gen ^ n) qpos bd hs chain mu hp hR hA

/-- **The chains**: from `chain[0] = chain[1] = 0`, after `j ≤ n` iterations `chain[2j]`,
`chain[2j + 1]` are the chains over the first `resBatch·j` positions `Pos` in memory. -/
theorem resChain {P H : E → E} {po : ℕ} {qpos chain mu : E} {n : ℕ} {Pos : ℕ → E}
    (hP : ∀ i < resBatch * n, LoadHolds rd qpos (po + i) (Pos i))
    (h0 : LoadHolds rd chain 0 0) (h1 : LoadHolds rd chain 1 0)
    (hit : ∀ j < n, ResIter rd P H po qpos chain mu (gen ^ j)) :
    ∀ j ≤ n, LoadHolds rd chain (2 * j)
        (resFold P H mu (0, 0) ((List.range (resBatch * j)).map Pos)).1 ∧
      LoadHolds rd chain (2 * j + 1)
        (resFold P H mu (0, 0) ((List.range (resBatch * j)).map Pos)).2 := by
  intro j
  induction j with
  | zero => intro _; simpa [resFold] using ⟨h0, h1⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, ps, hl, hps, la, lb, lc, ld⟩ := hit j (by omega)
    obtain ⟨i0, i1⟩ := ih (by omega)
    have hx : (gen ^ j) ^ resBatch = gen ^ (resBatch * j) := by rw [← pow_mul, Nat.mul_comm]
    have hx2 : (gen ^ j) ^ 2 = gen ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
    rw [hx2, loadHolds_mul_gen_pow] at la lb lc ld
    have ea : a = (resFold P H mu (0, 0) ((List.range (resBatch * j)).map Pos)) := by
      have e1 := loadHolds_unique la (by simpa using i0)
      have e2 := loadHolds_unique lb (by simpa using i1)
      exact Prod.ext e1 e2
    have eps : ps = (List.range resBatch).map fun i ↦ Pos (resBatch * j + i) := by
      refine List.ext_getElem (by simp [hl]) fun i h1 h2 ↦ ?_
      have := hps i (by omega)
      rw [hx, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ h1] at this
      simp only [List.getElem_map, List.getElem_range]
      exact loadHolds_unique this (by
        have := hP (resBatch * j + i) (by simp at h2; nlinarith)
        rwa [← Nat.add_assoc] at this)
    rw [ea, eps, ← resFold_append] at lc ld
    rw [show resBatch * (j + 1) = resBatch * j + resBatch by ring, List.range_add, List.map_append,
      List.map_map]
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact lc
    · rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]; exact ld

end
end LeanVM.Guest.B1.Whir
