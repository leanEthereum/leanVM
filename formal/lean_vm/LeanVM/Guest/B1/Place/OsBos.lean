/-
  LeanVM.Guest.B1.Place.OsBos

  open_stacked's frame-size bound: its frame, its buffers, a bound per callee.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.Memory.Uniform

/-!
# The frame-size bound

`osSizesF c`: the heap buffers' sizes at f128's layout. `osCallB fs Bk f`: a call of `f`, entered
within `Bk f` words or skipped (its frame `fs f`).
`osKidsB fs Bk c`: the body's (`Whir.osBody c`) calls' total, one `osCallB` per call statement,
whatever `σ` (a call's callee is its statement's; `mkCalls_sumB`). `osBos fs Bk name c`: the frame `fs name`, the buffers, the
callees.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **`open_stacked`'s heap buffers' sizes**, in allocation order (`Whir.osHead`, `osLevel`,
`osFinish`; `lean_ethereum.py`'s `open_stacked` at 71205cca4): the head's thirteen (`merkle_caps`,
`merkle_cap_active`, `final_msg`, `level_roots`, `fold_challenges`, `round_coefs`, `level_betas`,
`level_mus`, `level_hs`, `ood_z`, `ood_scalars`, `query_positions`, `query_win_ptrs`); per level
the message `sent` (a non-final one), the squeeze run `sqz`, the normalized lane `hs` (the final
one); `tail_challenges`, `point`, `point1`, `basis_d`, `level_scale`, `level_after`,
`inner_chain`; each non-final level's residual chain. -/
def osSizesF (c : OsCfg) : List ℕ :=
  let n := c.levels.length
  [4 * c.capLen, c.capLen, c.yrLen + (c.levels.getD c.yrLevel default).folds, 2 * n, c.nFolds,
    2 * c.nFolds, n, n, n * hsStride, n * ligColsCap, n, c.posLen,
    c.posLen] ++
  (List.range n).flatMap (fun i ↦
    (if i = c.yrLevel then [] else [2 + (c.levels.getD i default).folds]) ++ [(c.maxSq + 1) * 5] ++
      (if i = c.yrLevel then [c.yrLen + (c.levels.getD i default).folds] else [])) ++
  [yrLogCap, pointCap, pointCap, n * ligColsCap, n, n, 2 * n] ++
  (List.range c.yrLevel).map fun i ↦ 2 * ((c.levels.getD i default).queries / resBatch + 1)

/-- A call of `f`: entered within `Bk f` words, or skipped. -/
def osCallB (fs Bk : String → ℕ) (f : String) : ℕ := max (fs f) (Bk f)

/-- The body's callees' total, one `osCallB` per call statement. -/
def osKidsB (fs Bk : String → ℕ) (c : OsCfg) : ℕ :=
  (((osBody c).filterMap Stmt.callS).map fun x ↦ osCallB fs Bk x.2.1).sum

/-- **`open_stacked`'s frame-size bound** at a configuration. -/
def osBos (fs Bk : String → ℕ) (name : String) (c : OsCfg) : ℕ :=
  fs name + (osSizesF c).sum + osKidsB fs Bk c

theorem mkCall_f (σ : Val) (x : Option V × String × List V × List V) :
    (mkCall σ x).f = x.2.1 := by
  obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl

theorem mkCalls_sumB (fs Bk : String → ℕ) (σ : Val) :
    ∀ xs : List (Option V × String × List V × List V),
      ((xs.map (mkCall σ)).map fun c' ↦ osCallB fs Bk c'.f).sum =
        (xs.map fun x ↦ osCallB fs Bk x.2.1).sum
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, mkCall_f, mkCalls_sumB fs Bk σ xs]

/-- `CompleteAtB` on fewer words read. -/
theorem completeAtB_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : Main.Layout} {args : List E} {Out : List E → Main.Layout → Prop} {B : ℕ}
    (h : CompleteAtB fs cert κ f Lin args Out B) (hsub : ∀ q ∈ Lin, q ∈ Lin') :
    CompleteAtB fs cert κ f Lin' args Out B := fun fp ↦ by
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm ↦ ?_⟩
  obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
  have h3 : Main.MemL rd Lin := fun q hq ↦ h2 q (hsub q hq)
  exact (hr rd hl (Main.memL_append.mpr ⟨h1, h3⟩)).mono fun i ⟨q, hq, hq1, hq2⟩ ↦
    ⟨q, hsub q hq, hq1, hq2⟩

end
end LeanVM.Guest.B1
