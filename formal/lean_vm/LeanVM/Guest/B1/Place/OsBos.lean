/-
  LeanVM.Guest.B1.Place.OsBos

  open_stacked's frame-size bound at each stack size: its frame, its buffers, a bound per call
  statement.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.Memory.Uniform

/-!
# The frame-size bound of an opening arm

The arm of size `m` (`open_stacked__L{m}`, stack log `μ = minOpenLog + m`) has the body
`osBody (osCfg m)` (`Whir/Template.lean`, checked equal to the core IR by `Whir/Data*.lean`):
straight-line atoms, calls and dispatches on the rate's selector, then its `ret`. A rate is a
dispatch's arm, so a static bound of the body covers every rate.

* `osSizesL c`: the sizes of the body's `HeapBuf`s, in allocation order.
* `osCallees c`: each call statement's callees, in order: a call's one, a dispatch's every arm.
  `osCalleeNames c`: all of them.
* `osCallB fs Bk names`: a call statement entered within `Bk f` words or skipped (its frame `fs f`)
  at its costliest callee; `osKidsB`, their total; `osBos fs Bk name c`: the frame `fs name`, the
  buffers, the calls.
* `Whir.segAt`: a buffer split by levels at offsets, `segAt_at` reading a level's word back where
  the segments are disjoint; `chain_disj`: segments in order are disjoint.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The buffers and the calls -/

/-- **`open_stacked`'s heap buffers' sizes**, in allocation order (`Whir.osHead`, `osLevel`,
`osTail`, `osFinish`): the head's eleven (`final_msg`, `level_roots`, `fold_challenges`,
`round_coefs`, `level_scales`, `level_lam_invs`, `level_hs`, `ood_z`, `ood_scalars`, `query_positions`,
`query_win_ptrs`); each non-final level's message `sent`; the final level's normalized lane `hs`;
`tail_challenges`, `point`, `point1`, `basis_d`, `level_scale`, `level_after`, `inner_chain`. -/
def osSizesL (c : OsCfg) : List ℕ :=
  let n := c.levels.length
  let lane := c.yrLen + (c.levels.getD c.yrLevel default).folds
  [lane, 2 * n, c.nFolds, 2 * c.nFolds, n, n, c.nFolds, c.colsTotal, n, c.posTotal, c.posTotal] ++
  ((c.levels.take c.yrLevel).map fun lv ↦ 2 + lv.folds) ++
  [lane, yrLogCap, pointCap, pointCap, c.colsTotal, n, n, 2 * n]

/-- The callees of a call statement: a call's, a conditional call's, a dispatch's arms. -/
def Stmt.calleesS : Stmt → Option (List String)
  | .call f _ _ => some [f]
  | .callIf _ f _ => some [f]
  | .dispatch _ fs _ _ => some fs
  | _ => none

/-- The body's call statements' callees, in order. -/
def osCallees (c : OsCfg) : List (List String) := (osBody c).filterMap Stmt.calleesS

/-- Every callee of the body. -/
def osCalleeNames (c : OsCfg) : List String := (osCallees c).flatten

/-! ## The bound -/

/-- A call statement: entered within `Bk f` words or skipped (its frame `fs f`), at its costliest
callee. -/
def osCallB (fs Bk : String → ℕ) (names : List String) : ℕ :=
  (names.map fun f ↦ max (fs f) (Bk f)).foldl max 0

/-- The body's calls' total, one `osCallB` per call statement. -/
def osKidsB (fs Bk : String → ℕ) (c : OsCfg) : ℕ := ((osCallees c).map (osCallB fs Bk)).sum

/-- **`open_stacked`'s frame-size bound** at a configuration. -/
def osBos (fs Bk : String → ℕ) (name : String) (c : OsCfg) : ℕ :=
  fs name + (osSizesL c).sum + osKidsB fs Bk c

theorem le_foldl_max_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a
  | [], _ => le_rfl
  | y :: l, a => le_trans (le_max_left a y) (le_foldl_max_init l (max a y))

theorem le_foldl_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → ∀ a : ℕ, x ≤ l.foldl max a
  | [], _, h, _ => absurd h List.not_mem_nil
  | y :: l, x, h, a => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a x) (le_foldl_max_init l _)
    · exact le_foldl_max h _

/-- **A callee within its statement's bound.** -/
theorem le_osCallB {fs Bk : String → ℕ} {names : List String} {f : String} (h : f ∈ names) :
    max (fs f) (Bk f) ≤ osCallB fs Bk names :=
  le_foldl_max (List.mem_map.mpr ⟨f, h, rfl⟩ : max (fs f) (Bk f) ∈ names.map fun f ↦ max (fs f) (Bk f)) 0

/-! ## Buffers split by levels -/

namespace Whir

/-- A buffer split by levels: word `e` is level `l`'s word `e - off l` where `l < n` is the first
level whose segment `[off l, off l + span l)` holds `e`, else `0`. -/
def segAt (n : ℕ) (off span : ℕ → ℕ) (val : ℕ → ℕ → E) (e : ℕ) : E :=
  match (List.range n).find? (fun l ↦ decide (off l ≤ e ∧ e < off l + span l)) with
  | some l => val l (e - off l)
  | none => 0

/-- **A level's word of a split buffer**, the segments disjoint. -/
theorem segAt_at {n : ℕ} {off span : ℕ → ℕ} {val : ℕ → ℕ → E}
    (hd : ∀ l l', l < n → l' < n → l < l' → off l + span l ≤ off l')
    {l k : ℕ} (hl : l < n) (hk : k < span l) : segAt n off span val (off l + k) = val l k := by
  unfold segAt
  have hs : ((List.range n).find? (fun l' ↦ decide (off l' ≤ off l + k ∧ off l + k < off l' + span l'))).isSome := by
    rw [List.find?_isSome]
    exact ⟨l, List.mem_range.mpr hl, by simp; omega⟩
  obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp hs
  rw [hl']
  have hm := List.find?_some hl'
  have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hl')
  simp only [decide_eq_true_eq] at hm
  obtain rfl : l' = l := by
    rcases Nat.lt_trichotomy l' l with h | h | h
    · have := hd l' l hmem hl h; omega
    · exact h
    · have := hd l l' hl hmem h; omega
  simp

/-- **Segments in order are disjoint.** -/
theorem chain_disj {n top : ℕ} {a w : ℕ → ℕ}
    (h : ∀ l < n, a l + w l ≤ (if l + 1 < n then a (l + 1) else top)) :
    (∀ l l', l < n → l' < n → l < l' → a l + w l ≤ a l') ∧ ∀ l < n, a l + w l ≤ top := by
  have step : ∀ l, l + 1 < n → a l + w l ≤ a (l + 1) := fun l hl ↦ by
    have := h l (by omega); simpa only [hl, ↓reduceIte] using this
  have up : ∀ d l, l + d < n → a l + w l ≤ a (l + d) + w (l + d) := by
    intro d
    induction d with
    | zero => intro l _; exact le_rfl
    | succ d ih =>
      intro l hl
      have h1 := ih l (by omega)
      have h2 := step (l + d) (by omega)
      rw [show l + (d + 1) = l + d + 1 by omega]
      omega
  refine ⟨fun l l' _ hl' hll ↦ ?_, fun l hl ↦ ?_⟩
  · have h1 := up (l' - 1 - l) l (by omega)
    have h2 := step (l + (l' - 1 - l)) (by omega)
    rw [show l + (l' - 1 - l) + 1 = l' by omega] at h2
    omega
  · have h1 := up (n - 1 - l) l (by omega)
    have h2 := h (l + (n - 1 - l)) (by omega)
    simp only [show ¬ (l + (n - 1 - l) + 1 < n) by omega, ↓reduceIte] at h2
    omega

end Whir

end
end LeanVM.Guest.B1
