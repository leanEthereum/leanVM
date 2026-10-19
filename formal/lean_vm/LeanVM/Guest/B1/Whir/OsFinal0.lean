/-
  LeanVM.Guest.B1.Whir.OsFinal0

  A run of the stacked opening, as `open_stacked`'s data and the facts its completeness uses.
-/

module

public import LeanVM.Guest.B1.Whir.OsAsm3

/-!
# A run's kit (TRIAGE #36)

`OsRunKit cfg μ Lall d w`: the levels' data along the run (`OsChain`) with the openings agreeing at
each cap, the tail's fold rounds, and the run's end in terms of `d`. `os_kit_of_run`: a run of
`whirOpen μ r target` with its queries agreeing gives one, `d` holding the run's words, state,
claim and root.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The state after the levels, of a run's data. -/
def OsData.endL (cfg : OsCfg) (d : OsData) : Digest × ℕ × WhirState :=
  osLvsEnd cfg d.xs 0 d.cv0 2 (osW0 d.target d.xs) (d.roots0 cfg) d.Hs

/-- **What `open_stacked`'s completeness uses of a run.** -/
structure OsRunKit (cfg : OsCfg) (μ : ℕ) (Lall : List Whir.Level) (d : OsData) (w : WhirEnd) : Prop where
  x2 : 2 ≤ d.xs.length
  len : d.Hs.length = cfg.levels.length
  chain : ∃ (sp' : St) (Q : List (ℕ × List (ℕ × Opening))), (∀ x ∈ Q, BatchAgrees x.1 x.2) ∧
    OsChain cfg μ (cfg.lv 0).folds d.xs Lall w sp' Q 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs
  tail : ∃ (ospT : List Opening) (rootsT : List (Digest × ℕ × ℕ)),
    Runs (foldRounds (cfg.yrLog - 1) ⟨(d.endL cfg).2.2.target, (d.endL cfg).2.2.quad, [], []⟩ [])
      ⟨(d.endL cfg).1, d.xs.drop (d.endL cfg).2.1, ospT, rootsT⟩ (d.w1t, d.chst)
      ⟨d.cv1t, d.xs.drop ((d.endL cfg).2.1 + 2 * (cfg.yrLog - 1)), ospT, rootsT⟩
  chst : d.chst.length = cfg.yrLog - 1
  w : w = ⟨((d.endL cfg).2.2.folds ++ d.tf).drop (cfg.lv 0).folds ++ ((d.endL cfg).2.2.folds ++ d.tf).take (cfg.lv 0).folds,
    (d.endL cfg).2.2.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt ((d.endL cfg).2.2.folds.drop c.foldStart ++ d.tf)) 0,
    multilinearEval (d.fmsgC cfg) d.tf, polyEval d.w1t.quad d.last⟩

/-- **A run's kit.** -/
theorem os_kit_of_run {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {target : E}
    {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest} {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (h : RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots')
    (hcap : CapAgrees μ r root cv xs os target) :
    ∃ d : OsData, d.xs = xs ∧ d.cv = cv ∧ d.target = target ∧ d.root = root ∧ OsRunKit cfg μ Lall d w := by
  obtain ⟨hx2, Hs, hHl, hch⟩ := os_open_inv hok h
  obtain ⟨w1, chs, cv1, ospT, rootsT, hr, hcl, hw⟩ := os_tail_data hok hHl hch
  refine ⟨⟨xs, cv, target, root, os, Hs, w1, chs, cv1⟩, rfl, rfl, rfl, rfl, hx2, hHl,
    ⟨_, _, fun x hx => hcap x hx, hch⟩, ⟨ospT, rootsT, hr⟩, hcl, ?_⟩
  rw [hw]; rfl

end
end LeanVM.Guest.B1
