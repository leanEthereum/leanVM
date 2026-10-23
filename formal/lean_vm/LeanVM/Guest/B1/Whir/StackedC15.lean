/-
  LeanVM.Guest.B1.Whir.StackedC15

  The stacked opening's run, inverted into the head's words, the levels' data and the tail's.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC14

/-!
# The opening's data (TRIAGE #36)

`os_open_inv`: a run of `whirOpen μ r target` at a configuration matching its ladder reads the
first quadratic at the stream's first two words, then has the levels' data (`OsChain`) from level
`0`; `os_chain_tail`: the last level's tail runs the tail rounds as `yrLog - 1` fold rounds and a
closing challenge, to the run's end.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The spec's state at level `0`. -/
def osW0 (target : E) (xs : List E) : WhirState :=
  ⟨target, [xs.getD 0 0, target + xs.getD 1 0, xs.getD 1 0], [], []⟩

/-- **The opening's run, inverted at the head**. -/
theorem os_open_inv {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {target : E} {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest}
    {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (h : RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots') :
    2 ≤ xs.length ∧ ∃ Hs : List OsLvH, Hs.length = cfg.levels.length ∧
      OsChain cfg μ (cfg.lv 0).folds xs Lall w ⟨cv', [], [], roots'⟩
        (queriesOf (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) 0
        (obsCv (obsCv cv (xs.getD 0 0)) (xs.getD 1 0)) 2 (osW0 target xs) os
        [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)] Hs := by
  have hr := h [] []
  simp only [List.append_nil] at hr
  have hr' : Runs (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩ w ⟨cv', [], [], roots'⟩ := hr
  unfold whirOpen at hr'
  obtain ⟨cfg', s1, h1, h2⟩ := os_inv_bind hr'
  rw [hok.config] at h1
  simp only [Verifier.liftOption] at h1
  obtain ⟨hcfg, rfl⟩ := os_inv_ret h1
  subst cfg'
  obtain ⟨q, s2, h3, h4⟩ := os_inv_bind h2
  obtain ⟨c0, c2, rest, hs, rfl, rfl⟩ := os_inv_roundPoly3 h3
  simp only at hs
  have hlen := congrArg List.length hs
  simp only [List.length_cons] at hlen
  have hx : xs.drop 0 = c0 :: c2 :: rest := by simpa using hs
  obtain ⟨e0, e1, hrest⟩ := os_drop_cons2 hx
  subst hrest
  have hq := os_queriesOf_bind (sumcheckRoundPoly 3 target none)
    (fun quad => whirLevelsOpen μ ((Lall.head?.map (·.fold)).getD 0) 0 Lall ⟨target, quad, [], []⟩) _ h3
  rw [os_queriesOf_noQ _ (os_noQ_roundPoly3 _), List.nil_append] at hq
  have eQ : queriesOf (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩ =
      queriesOf ((sumcheckRoundPoly 3 target none).bind (fun quad =>
        whirLevelsOpen μ ((Lall.head?.map (·.fold)).getD 0) 0 Lall ⟨target, quad, [], []⟩))
        ⟨cv, xs, os, [(root, stackShape μ r)]⟩ := by
    unfold whirOpen; rw [hok.config]; rfl
  rw [hok.lane, hok.shape] at h4
  refine ⟨by omega, ?_⟩
  have hn := hok.len2
  subst e0 e1
  obtain ⟨Hs, hHl, hch⟩ := os_chain_of_run (xs := xs) (e := w) (sp' := ⟨cv', [], [], roots'⟩)
    (Q := queriesOf (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) hok.len hok.spec
    hok.yrLevel (cfg.levels.length - 1) 0 _ 2 (osW0 target xs) os [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)]
    (by rw [hok.len]; omega)
    (by rw [hok.off0]; rfl) rfl ⟨root, by simp [oqR]⟩ (fun b hb => by
      rw [eQ, hq, hok.lane, hok.shape]
      rw [List.drop_zero] at hb
      exact hb) (by
      rw [List.drop_zero]
      exact h4)
  exact ⟨Hs, by rw [hHl]; omega, hch⟩

/-- The last level's index, stream position, roots and data. -/
def osLvsLast (cfg : OsCfg) (xs : List E) :
    ℕ → ℕ → List (Digest × ℕ × ℕ) → List OsLvH → ℕ × ℕ × List (Digest × ℕ × ℕ) × OsLvH
  | lvl, p, roots, [] => (lvl, p, roots, default)
  | lvl, p, roots, [H] => (lvl, p, roots, H)
  | lvl, p, roots, H :: H' :: Hs => osLvsLast cfg xs (lvl + 1) (osHPEnd cfg lvl p) (osHRootsEnd cfg lvl roots H) (H' :: Hs)

/-- **The last level's tail**: from the levels' data, the tail runs from where the levels end. -/
theorem os_chain_tail {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ)
      (w : WhirState) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)), OsChain cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      Runs (osTailOpen (μ - osLevelF cfg (osLvsLast cfg xs lvl p roots Hs).1) lane
          (osLvsEnd cfg xs lvl cv p w roots Hs).2.2
          (osHMs cfg (osLvsLast cfg xs lvl p roots Hs).1 xs (osLvsLast cfg xs lvl p roots Hs).2.1))
        ⟨(osLvsEnd cfg xs lvl cv p w roots Hs).1, xs.drop (osLvsEnd cfg xs lvl cv p w roots Hs).2.1,
          (osLvsLast cfg xs lvl p roots Hs).2.2.2.osq, (osLvsLast cfg xs lvl p roots Hs).2.2.1⟩ e sp'
  | [], _, _, _, _, _, _, h => h.elim
  | [H], lvl, cv, p, w, osp, roots, h => by
    obtain ⟨-, -, hl, hn⟩ := h
    by_cases hy : lvl = cfg.yrLevel
    · exact (hl hy).2
    · exact (hn hy).elim
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, h => by
    obtain ⟨-, -, hl, hn⟩ := h
    by_cases hy : lvl = cfg.yrLevel
    · exact absurd (hl hy).1 (by simp)
    · exact os_chain_tail (H' :: Hs) (lvl + 1) _ _ _ _ _ (hn hy)

end
end LeanVM.Guest.B1
