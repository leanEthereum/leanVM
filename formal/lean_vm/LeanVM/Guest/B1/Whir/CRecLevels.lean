/-
  LeanVM.Guest.B1.Whir.CRecLevels

  The stacked opening's query steps are its honest run's levels, and their Merkle hints are, stream by stream, what each level's `level_queries` pops at the honest witness, level 0 first.
-/

module

public import LeanVM.Guest.B1.Whir.CStepsEq
public import LeanVM.Guest.B1.Whir.CRecQueries
public import LeanVM.Guest.B1.Whir.CHonLevelPops

/-!
# The levels' steps and their hints

* `honRunS_of`: `honRun_of`, with the run's query steps `lvSteps μ 0 Ls` of its levels;
* `lvSteps_eq_range`: the steps level by level;
* `lvPops Ls μ r l`: level `l`'s `level_queries` entries at the honest witness (`osHonest_run`'s);
* `HonRun.steps_sameStreams`: `stepsHints true` of the levels' steps is, stream by stream, their entries in order.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **Every accepting run has its honest data, its query steps its levels'.** -/
theorem honRunS_of {μ r : ℕ} (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) {S : KeccakState}
    {root : Digest} {target : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : NoZeroChallenge μ r target S xs os root) (hca : CapsAgree μ r target S xs os root) :
    ∃ cfg Ls, HonRun μ r target S root xs os w cfg Ls ∧
      Limits.queryStepsOf (whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, stackShape μ r)]⟩ =
        lvSteps μ 0 Ls := by
  obtain ⟨cfg, hcfg, hL⟩ := whirOpen_honest h1 h2 h3 h4 hrun hnz
  obtain ⟨ds, hD⟩ := LvsRun.data _ _ _ _ _ _ _ _ _ _ hL
  obtain ⟨cfg', hcfg', hC⟩ := candB_sound (candB_all (μ - minOpenLog) (r - 1)
    (by unfold ligNSizes minOpenLog at *; omega) (by omega))
  rw [show μ - minOpenLog + minOpenLog = μ by omega, show r - 1 + 1 = r by omega, hcfg] at hcfg'
  rw [show μ - minOpenLog + minOpenLog = μ by omega, show r - 1 + 1 = r by omega] at hC
  cases hcfg'
  have hA := whirOpen_agree (ladderOk_of h1 h2 h3 h4) hcfg hD hrun hca
  refine ⟨cfg, _, ⟨by unfold minOpenLog at *; omega, by omega, hcfg, hC, lvsAt_run _ _ _ _ _ _ _ _ _ _ _ hD,
    fun i hi ↦ ?_⟩, ?_⟩
  · have := lvsAt_agree _ _ _ _ _ _ _ _ _ _ _ hD hA i hi
    simpa using this
  · have e := runT_of_runsWith hrun (carries_capOf S) [] []
    simp only [List.append_nil] at e
    refine (qstT_eq _ ⟨⟨capOf S, []⟩, none, xs, os, [(root, stackShape μ r)]⟩ ⟨S, [], none⟩
      ⟨rfl, rfl, rfl⟩).trans ?_
    unfold whirOpen at e ⊢
    obtain ⟨cfg', hc', e⟩ := rT_liftOption e
    rw [hcfg, Option.some.injEq] at hc'
    subst hc'
    rw [hcfg]
    exact lvSteps_of_run μ _ cfg 0 _ _ _ xs os w ds _ (carries_capOf S) (ladderOk_of h1 h2 h3 h4 cfg hcfg) hD e

/-- **The levels' steps, level by level.** -/
theorem lvSteps_eq_range (logN : ℕ) : ∀ (Ls : List LvAt) (index : ℕ),
    lvSteps logN index Ls = (List.range Ls.length).map fun l =>
      (((Ls.getD l default).R.getD (index + l) default).2.1,
        ((Ls.getD l default).qs logN).zip (Ls.getD l default).phase)
  | [], _ => rfl
  | L :: Ls, index => by
    rw [lvSteps, lvSteps_eq_range logN Ls (index + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.getD_cons_zero, Nat.add_zero, List.cons.injEq, true_and]
    refine List.map_congr_left fun l _ ↦ ?_
    simp only [Function.comp_apply, List.getD_cons_succ, show index + 1 + l = index + (l + 1) by omega]

/-- The Merkle hints of steps `g k`, `g (k + 1)`, …: each one's level. -/
theorem stepsHints_range' (g : ℕ → ℕ × List (ℕ × Opening)) : ∀ (n k : ℕ),
    stepsHints (decide (k = 0)) ((List.range' k n).map g) =
      (List.range' k n).flatMap fun l ↦ Hints.levelHints (decide (l = 0)) (g l).1 (g l).2.length
        ((g l).2.map Prod.snd)
  | 0, _ => rfl
  | n + 1, k => by
    have ih := stepsHints_range' g n (k + 1)
    rw [show decide (k + 1 = 0) = false by simp] at ih
    rw [List.range'_succ, List.map_cons, List.flatMap_cons, stepsHints, ih]

theorem sameStreams_flatMap' {β : Type} {f g : β → List Pop} :
    ∀ {l : List β}, (∀ x ∈ l, SameStreams (f x) (g x)) → SameStreams (l.flatMap f) (l.flatMap g)
  | [], _ => SameStreams.refl _
  | x :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (h x List.mem_cons_self).append (sameStreams_flatMap' fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **Level `l`'s `level_queries` entries at the honest witness**: its cap and flags, then its queries' rows and
walks' children. -/
noncomputable def lvPops (Ls : List LvAt) (μ r l : ℕ) : List Pop :=
  lqCapE (HonRun.capW Ls μ r l) (HonRun.flW Ls μ r l) ++
    oqPops (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l)
      (oqW (fun k ↦ ((Ls.getD l default).qs μ).getD k 0)
        (fun k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k [])
        (fun k ↦ ((Ls.getD l default).phase.map (fun o ↦ o.path.take
          (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
            ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k []))
      (oqQA (osCfgR (μ - minOpenLog) (r - 1)) l)

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}

/-- **The levels' steps' Merkle hints are their entries**, stream by stream, level 0 first. -/
theorem steps_sameStreams (hR : HonRun μ r target S root xs os w cfg Ls) :
    SameStreams ((List.range (osCfgR (μ - minOpenLog) (r - 1)).levels.length).flatMap (lvPops Ls μ r))
      (stepsHints true (lvSteps μ 0 Ls)) := by
  rw [lvSteps_eq_range, hR.len, List.range_eq_range']
  rw [show stepsHints true _ = _ from stepsHints_range' _ _ 0]
  refine sameStreams_flatMap' fun l hl ↦ ?_
  have hl' : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length := by
    rw [List.mem_range'] at hl; omega
  have hidx := hR.idx hl'
  have hplen : (Ls.getD l default).phase.length = ((Ls.getD l default).qs μ).length := by
    rw [← hidx, List.length_map]
  have hh : ((Ls.getD l default).R.getD (0 + l) default).2.1 =
      ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth := by
    rw [Nat.zero_add]; exact hR.height_eq hl'
  simp only
  rw [hh, levelHints_zip _ _ hplen]
  exact hR.sameStreams hl'

end HonRun

end
end LeanVM.Guest.B1.Whir
