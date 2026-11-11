/-
  LeanVM.Guest.B1.Whir.SpecTrace

  The honest trace of an accepting run with no zero challenge: one `SpLv` per level, chained, at
  every candidate's configuration.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.SpecInv
public import LeanVM.Guest.B1.Whir.Open

/-!
# The honest trace

`SpChain logN lane index cfg ws F xs os R Ls res`: the levels `cfg` (from `index`) of a run from
the state `ws`, the sponge `F`, the words `xs`, the openings `os` and the commitments `R` are the
`SpLv`s `Ls` in order: each reads its words and openings and the next starts where it ends
(`Fend`, `wsEnd`, its next commitment read); the last one's tail rounds (`tailTr`) end the run at
`res`, its `WhirEnd` the formula `whirLevelsOpen` returns.

* `nz_chain`: an accepting run of `whirLevelsOpenNZ` at a configuration whose facts the guest's
  `LevelsOk` gives is such a chain.
* **`nz_trace`**: on an accepting run of `whirOpen μ r target` with no zero challenge
  (`NoZeroChallenge`), at a candidate's facts (`CandFacts`): the words are the first quadratic's
  `c0, c2` then the chain's, from `⟨capOf S, [c0, c2]⟩` and `⟨target, [c0, target + c2, c2], [], []⟩`,
  the root committed; the chain ends at `w` with nothing left; the NZ program's query steps are
  `whirOpen`'s (`CapsAgree` speaks of them).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The end the last level's tail rounds give: the point in witness order, the glued weight, the
residual's value, the final claim. -/
def SpLv.wend (L : SpLv) (lane : ℕ) (xsR : List E) : WhirEnd :=
  ⟨(L.wsEnd.folds ++ (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1).drop lane ++
      (L.wsEnd.folds ++ (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1).take lane,
    L.wsEnd.glued.foldl (fun weight claim ↦ weight + claim.scalar *
      claim.weightAt (L.wsEnd.folds.drop claim.foldStart ++
        (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1)) 0,
    multilinearEval L.ms (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1,
    (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.2⟩

/-- **The honest chain of levels.** -/
def SpChain (logN lane : ℕ) : ℕ → List Whir.Level → WhirStateT → Fs → List E → List (List Opening) →
    List (Digest × ℕ × ℕ) → List SpLv → WhirEnd × FSt → Prop
  | index, [level], ws, F, xs, os, R, [L], res =>
    L.logN = logN ∧ L.index = index ∧ L.level = level ∧ L.fin = true ∧ L.ws = ws ∧ L.F = F ∧
      L.Ok R (Vector.replicate 4 0) ∧ ∃ (xsR : List E) (osR : List (List Opening)),
        xs = L.words ++ xsR ∧ os = L.os :: osR ∧ 2 * (L.ml - 1) ≤ xsR.length ∧
        (∀ c ∈ (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1, c ≠ 0) ∧
        res = (L.wend lane xsR, ⟨(tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).1,
          xsR.drop (2 * (L.ml - 1)), osR, R⟩)
  | index, level :: next :: rest, ws, F, xs, os, R, L :: Ls, res =>
    L.logN = logN ∧ L.index = index ∧ L.level = level ∧ L.fin = false ∧ L.ws = ws ∧ L.F = F ∧
      ∃ (d : Digest) (xsR : List E) (osR : List (List Opening)), L.Ok R d ∧ xs = L.words ++ xsR ∧
        os = L.os :: osR ∧
        SpChain logN lane (index + 1) (next :: rest) L.wsEnd L.Fend xsR osR
          (R ++ [(d, levelShape L.ml next (3 * 2 ^ next.fold))]) Ls res
  | _, _, _, _, _, _, _, _, _ => False

theorem glue_folds (lam : E) (s : WhirStateT) (pending : List (E × List E × (List E → E))) :
    (glueT lam s pending).folds = s.folds := by
  unfold glueT
  generalize (1 : E) = e
  induction pending generalizing s e with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons]
    exact ih _ _

theorem SpLv.wsEnd_folds (L : SpLv) : L.wsEnd.folds = L.ws.folds ++ L.chs := by
  rw [SpLv.wsEnd, glue_folds]; rfl

/-- **The levels of an accepting run, chained.** -/
theorem nz_chain {c : OsCfg} {logN lane : ℕ} : ∀ (lvs : List OsLv) (cfg : List Whir.Level)
    (index : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : WhirEnd × FSt),
    LevelsOk c logN index lvs cfg → ws.folds.length = (lvs.headD default).foldsOff →
    F.pend.length = 2 → index < R.length →
    runF (whirLevelsOpenNZ logN lane index cfg ws) ⟨F, xs, os, R⟩ = some res →
    ∃ Ls : List SpLv, Ls.length = cfg.length ∧ SpChain logN lane index cfg ws F xs os R Ls res ∧
      ∀ L ∈ Ls, (L.height, L.qs.zip L.os) ∈
        queryStepsOf (whirLevelsOpenNZ logN lane index cfg ws) ⟨F, xs, os, R⟩
  | [lv], [level], index, ws, F, xs, os, R, res, hok, hfo, hF, hR, h => by
    obtain ⟨hcfg, hfold, -, hml, -, -⟩ := hok
    have hd : 1 ≤ 192 / (logN - (ws.folds.length + level.fold) + level.logInvRate) := by
      simp only [List.headD_cons] at hfo
      rw [hfo, hfold, hml, ← hcfg.depth]; exact hcfg.per
    obtain ⟨L, xsR, osR, e1, e2, e3, e4, e5, e6, hOk, hxs, hos, htl, htnz, hres, hq⟩ :=
      level_fin_inv hd h
    refine ⟨[L], rfl, ⟨e1, e2, e3, e4, e5, e6, hOk, xsR, osR, hxs, hos, htl, htnz, hres⟩, ?_⟩
    intro L' hL'
    simp only [List.mem_singleton] at hL'
    subst hL'
    rw [hq]
    exact List.mem_singleton_self _
  | lv :: lv' :: lvs, level :: next :: cfg, index, ws, F, xs, os, R, res, hok, hfo, hF, hR, h => by
    obtain ⟨hcfg, hfold, -, hml, hm, -, -, hoff', -, hrest⟩ := hok
    simp only [List.headD_cons] at hfo
    have e : logN - (ws.folds.length + level.fold) = lv.logCols := by rw [hfo, hfold, hml]
    have hd : 1 ≤ 192 / (logN - (ws.folds.length + level.fold) + level.logInvRate) := by
      rw [e, ← hcfg.depth]; exact hcfg.per
    obtain ⟨L, d, xsR, osR, e1, e2, e3, e4, e5, e6, hOk, hxs, hos, h', hq⟩ :=
      level_nf_inv hF hR (by rw [e]; exact hm) hd h
    have hfo' : L.wsEnd.folds.length = ((lv' :: lvs).headD default).foldsOff := by
      rw [SpLv.wsEnd_folds, List.length_append, SpLv.chs_length, e5, e3, hfo, hfold,
        List.headD_cons, hoff']
    obtain ⟨Ls, hl, hc, hm⟩ := nz_chain (lv' :: lvs) (next :: cfg) (index + 1) _ _ _ _ _ res hrest
      hfo' (SpLv.Fend_pend L) (by simp; omega) h'
    refine ⟨L :: Ls, by simp [hl], ⟨e1, e2, e3, e4, e5, e6, d, xsR, osR, hOk, hxs, hos, hc⟩, ?_⟩
    intro L' hL'
    rw [hq]
    rcases List.mem_cons.mp hL' with rfl | hL'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hm L' hL')
  | [], _, _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], [], _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], _ :: _ :: _, _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [], _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [_], _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [LevelsOk] at hok

theorem start_absorb (S : KeccakState) (c0 c2 : E) :
    (((⟨capOf S, []⟩ : Fs).absorb c0 dsObserve).absorb c2 dsObserve) =
      ⟨capOf S, [(c0, dsObserve), (c2, dsObserve)]⟩ := by
  simp [Fs.absorb, rateScalars]

/-- **The honest trace of an accepting run with no zero challenge**, at a candidate's facts. -/
theorem nz_trace {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg)
    {target : E} {S : KeccakState} {xs : List E} {os : List (List Opening)} {root : Digest} {w : WhirEnd}
    {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s'
      roots')
    (hnz : NoZeroChallenge μ r target S xs os root) :
    ∃ (c0 c2 : E) (xs' : List E) (Ls : List SpLv), xs = c0 :: c2 :: xs' ∧
      Ls.length = cfg.length ∧
      SpChain μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [c0, target + c2, c2], [], []⟩
        ⟨capOf S, [(c0, dsObserve), (c2, dsObserve)]⟩ xs' os [(root, stackShape μ r)] Ls
        (w, ⟨s', [], [], roots'⟩) ∧
      ∀ L ∈ Ls, (L.height, L.qs.zip L.os) ∈
        queryStepsOf (whirOpen μ r target) (osStart μ r S xs os root) := by
  obtain ⟨h, hq⟩ := nz_run hrun hnz
  obtain ⟨cfg', c0, c2, xs', hdc, hxs, h1, hq1⟩ := head_inv h
  rw [hF.dc] at hdc
  cases hdc
  rw [start_absorb] at h1 hq1
  obtain ⟨Ls, hl, hc, hm⟩ := nz_chain c.levels cfg 0 _ _ _ _ _ _ hF.lok
    (by simpa using hF.off0.symm) rfl (by simp) h1
  refine ⟨c0, c2, xs', Ls, hxs, hl, hc, fun L hL ↦ ?_⟩
  rw [← hq]
  show _ ∈ queryStepsOf (whirOpenNZ μ r target) ⟨⟨capOf S, []⟩, xs, os, [(root, stackShape μ r)]⟩
  rw [hq1]
  exact hm L hL

end
end LeanVM.Guest.B1.Whir
