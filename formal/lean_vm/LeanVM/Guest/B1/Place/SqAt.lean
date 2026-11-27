/-
  LeanVM.Guest.B1.Place.SqAt

  `open_stacked`'s squeeze loop placed (`RelAtIn`): one iteration, its decode call before
  its tail's, and the loop from its first iteration `g^e`, its decoders' frame runs its data.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.SqLoop
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«level_positions__L_loop0»
import LeanVM.Guest.StmtsAppend

/-!
# The squeeze loop, placed

A squeeze loop helper's body (`sqLoopBody lv name`) is straight-line: before its `ret []`
(`sqLoopPre`) it allocates nothing, has no `frameAddr`, calls
`decode_query_windows__L{depth}_L{capDepth}` (`sqDecName`, at `sqDecArgs`) and its tail
(`sqLoopPre_calls`), and loads only through the row `sqz·x^5`, at offsets below `10`
(`sqLoopPre_loads`). A loop entered at `fp` has its `m + 1` frames at `fp + t·fs L`, then its
iterations' decoders in order, decoder `t` at `sqDecAt`; from iteration `t` on it takes
`(m - t + 1)·fs L + (m - t)·fs D` words (`sqTot`).

`SqIterC lv`: one iteration's honest values on a memory holding its row and the next (the loop's
body at them with every call unconstrained), what `Whir/CSqLoop` proves; `SqAtE.lean` places the loop entered
at `g^e` with the bound `g^n`, `e < n`, from `decode_query_windows`' placed completeness
(`QwDecodeAtDE`), on every memory holding the capacity chain at `sqz`, the window table at `tabs`
and, at `qpos` and `qbp`, what each decoder stores: the positions and the pointers into its
`wins` run (`qwPtrAt`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The body's statements -/

/-- The decoder a level's squeeze loop calls. -/
def sqDecName (lv : OsLv) : String :=
  "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- The positions' pointer of an iteration. -/
def sqP1 (lv : OsLv) : List Stmt × ℕ × ℕ := osMat 3 lv.posOff (33 + osPowLen (128 / lv.depth))

/-- The window pointers' pointer of an iteration. -/
def sqP2 (lv : OsLv) : List Stmt × ℕ × ℕ := osMat 4 lv.posOff ((sqP1 lv).2.2 + 1)

/-- The decoder call's arguments. -/
def sqDecArgs (lv : OsLv) : List V := [.n (valf% «level_positions» «_loop0» "nxt[0]"), .n (sqP1 lv).2.2, .n (sqP2 lv).2.2, .n (valf% «level_positions» «_loop0» "tabs")]

/-- The tail call's arguments. -/
def sqTailArgs (lv : OsLv) : List V :=
  .n (sqLoopE lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)

/-- The squeeze loop's body before its final `ret []`. -/
def sqLoopPre (lv : OsLv) (name : String) : List Stmt :=
  (sqLoopA lv ++ osLoopTailA (sqLoopE lv)) ⧺ [.callIf (.n (sqLoopE lv + 2)) name (sqTailArgs lv)]

theorem sqLoopBody_pre (lv : OsLv) (name : String) :
    sqLoopBody lv name = sqLoopPre lv name ⧺ [.ret []] := by
  rw [sqLoopBody_split, sqLoopPre, sqTailArgs]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem os_powSteps_straight (x : ℕ) : ∀ ds acc k,
    (osPowSteps x ds acc k).1.all Main.Stmt.straight = true := by
  intro ds
  induction ds with
  | nil => intro _ _; rfl
  | cons d ds ih =>
    intro acc k
    cases d <;> simp [osPowSteps, ih, Main.Stmt.straight]

theorem os_mat_straight (b o k : ℕ) : (osMat b o k).1.all Main.Stmt.straight = true := by
  unfold osMat; split_ifs <;> rfl

theorem sqLoopPre_flat (lv : OsLv) (name : String) : (sqLoopPre lv name).all Stmt.flat = true := by
  rw [sqLoopPre, List.all_append, sqLoopA_flat lv]
  rfl

theorem sqLoopPre_straight (lv : OsLv) (name : String) :
    (sqLoopPre lv name).all Main.Stmt.straight = true := by
  rw [sqLoopPre, List.all_append]
  simp [sqLoopA, osKeccak, osLoopTailA, os_powSteps_straight, os_mat_straight, Main.Stmt.straight]

theorem osPowSteps_mem_mul (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), ∀ s ∈ (osPowSteps x ds acc k).1,
    ∃ d a b, s = osMul d a b
  | [], _, _, s, hs => by simp [osPowSteps] at hs
  | true :: ds, acc, k, s, hs => by
    simp only [osPowSteps, ↓reduceIte, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact osPowSteps_mem_mul x ds _ _ s hs
  | false :: ds, acc, k, s, hs => by
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨_, _, _, rfl⟩
    · exact osPowSteps_mem_mul x ds _ _ s hs

theorem osMat_mem (b o k : ℕ) : ∀ s ∈ (osMat b o k).1,
    (∃ d c, s = osCst d c) ∨ ∃ d a b, s = osMul d a b := by
  intro s hs
  unfold osMat at hs
  split_ifs at hs
  · simp at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl⟩

theorem fm_pow_nil {α : Type} (F : Stmt → Option α) (hm : ∀ d a b, F (osMul d a b) = none)
    (x : ℕ) (ds : List Bool) (acc k : ℕ) : (osPowSteps x ds acc k).1.filterMap F = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs => by
    obtain ⟨d, a, b, rfl⟩ := osPowSteps_mem_mul x ds acc k s hs; exact hm d a b

theorem fm_mat_nil {α : Type} (F : Stmt → Option α) (hm : ∀ d a b, F (osMul d a b) = none)
    (hc : ∀ d c, F (osCst d c) = none) (b o k : ℕ) : (osMat b o k).1.filterMap F = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs => by
    rcases osMat_mem b o k s hs with ⟨d, c, rfl⟩ | ⟨d, a, b, rfl⟩
    · exact hc d c
    · exact hm d a b

theorem sqLoopPre_allocs (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Main.Stmt.allocSz = [] := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Main.Stmt.allocSz (fun _ _ _ => rfl),
    fm_mat_nil Main.Stmt.allocSz (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem sqLoopPre_addrs (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Main.Stmt.addrS = [] := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Main.Stmt.addrS (fun _ _ _ => rfl),
    fm_mat_nil Main.Stmt.addrS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

/-- The calls of the squeeze loop's body: the decoder, then the tail. -/
def sqCallsS (lv : OsLv) (name : String) : List (Option V × String × List V × List V) :=
  [(none, sqDecName lv, sqDecArgs lv, []), (some (.n (sqLoopE lv + 2)), name, sqTailArgs lv, [])]

theorem sqLoopPre_calls (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Main.Stmt.callS = sqCallsS lv name := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Main.Stmt.callS (fun _ _ _ => rfl),
    fm_mat_nil Main.Stmt.callS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem sqLoopPre_loadsEq (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Stmt.loadS =
      (List.range 10).map fun i => ((.n (valf% «level_positions» «_loop0» "row") : V), i) := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Stmt.loadS (fun _ _ _ => rfl),
    fm_mat_nil Stmt.loadS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem sqLoopPre_loads (lv : OsLv) (name : String) :
    ∀ q ∈ (sqLoopPre lv name).filterMap Stmt.loadS, q.1 = .n (valf% «level_positions» «_loop0» "row") ∧ q.2 < 10 := by
  intro q hq
  rw [sqLoopPre_loadsEq] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, List.mem_range.mp hi⟩

/-! ## One iteration -/

/-- **One iteration's honest values** at `x = X`, on a memory holding its row's capacity `cap`
and the next row its squeeze's: the loop's body before its tail call holds with every call
unconstrained, the row at `sqz·X^5`, the decoder at the squeeze's word and the positions' and
window pointers' slots `g^po·X^(128/d)` on, the guard `X·g + N`, the tail at `X·g`. -/
def SqIterC (lv : OsLv) : Prop :=
  ∀ (rd : Reader) (X N sqz qpos qbp tabs : E) (cap : List E), cap.length = 5 →
    (∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0)) →
    (∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((⟨cap, []⟩ : Fs).squeeze.2.cap.getD i 0)) →
    ∃ σ : Val, (osParams 6).map σ = [X, N, sqz, qpos, qbp, tabs] ∧
      AllOk (fun _ _ _ ↦ True) rd σ (sqLoopA lv ++ osLoopTailA (sqLoopE lv)) ∧
      σ (.n (valf% «level_positions» «_loop0» "row")) = sqz * X ^ 5 ∧
      (sqDecArgs lv).map σ = [(⟨cap, []⟩ : Fs).squeeze.1,
        qpos * gen ^ lv.posOff * X ^ (128 / lv.depth), qbp * gen ^ lv.posOff * X ^ (128 / lv.depth),
        tabs] ∧
      σ (.n (sqLoopE lv + 2)) = X * gen + N ∧
      (sqTailArgs lv).map σ = [X * gen, N, sqz, qpos, qbp, tabs]

/-! ## The loop -/

/-- The words of the squeeze loop of `m` iterations from iteration `t`: each iteration's frame
and decoder, then the skipped tail's (`fs (tailKey name)`). -/
def sqTot (fs : String → ℕ) (lv : OsLv) (name : String) (m t : ℕ) : ℕ :=
  (m - t) * fs name + fs (Memory.tailKey name) + (m - t) * fs (sqDecName lv)

/-- Iteration `t`'s decoder, the loop of `m` iterations entered at `fp`: after the loop's frames,
the earlier iterations' decoders. -/
def sqDecAt (fs : String → ℕ) (lv : OsLv) (name : String) (m fp t : ℕ) : ℕ :=
  fp + m * fs name + fs (Memory.tailKey name) + t * fs (sqDecName lv)

theorem sqDecAt_succ (fs : String → ℕ) (lv : OsLv) (name : String) (m fp t : ℕ) :
    sqDecAt fs lv name m fp (t + 1) = sqDecAt fs lv name m fp t + fs (sqDecName lv) := by
  unfold sqDecAt; ring

theorem sqDecAt_le (fs : String → ℕ) (lv : OsLv) (name : String) {m t : ℕ} (fp : ℕ) (ht : t < m) :
    sqDecAt fs lv name m fp t + fs (sqDecName lv) ≤ fp + sqTot fs lv name m 0 := by
  unfold sqDecAt sqTot
  have h1 := Nat.mul_le_mul_right (fs (sqDecName lv)) (show t + 1 ≤ m by omega)
  rw [Nat.succ_mul] at h1
  rw [Nat.sub_zero]
  omega

/-- The decoders' frame runs from iteration `t`, decoder `t'` decoding `w t'`. -/
def sqRuns (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (name : String) (m fp : ℕ)
    (w : ℕ → E) (t : ℕ) : Layout :=
  ((List.range (m - t)).map fun i =>
    qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp (t + i)) lv.depth lv.capDepth (w (t + i))).flatten

theorem regionL_sqRuns {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {name : String}
    {m fp : ℕ} {w : ℕ → E} {t i : ℕ} : RegionL (sqRuns fs cert lv name m fp w t) i ↔
      ∃ t', t ≤ t' ∧ t' < m ∧
        RegionL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name m fp t') lv.depth lv.capDepth (w t')) i := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
    obtain ⟨_, ⟨s, hs, rfl⟩, hq⟩ := hq
    exact ⟨t + s, by omega, by omega, q, hq, h1, h2⟩
  · rintro ⟨t', h1, h2, q, hq, h3, h4⟩
    refine ⟨q, ?_, h3, h4⟩
    simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
    exact ⟨_, ⟨t' - t, by omega, by rw [show t + (t' - t) = t' by omega]⟩, hq⟩

/-- Blocks in pairwise disjoint windows, each disjoint, are disjoint: the first parts, then the
second parts. -/
theorem os_disj_windows {m : ℕ} (A B : ℕ → Layout) (lo len : ℕ → ℕ)
    (hD : ∀ j < m, DisjL (A j ++ B j)) (hW : ∀ j < m, Within (A j ++ B j) (lo j) (len j))
    (hsep : ∀ i < m, ∀ j < m, i ≠ j → lo i + len i ≤ lo j ∨ lo j + len j ≤ lo i) :
    DisjL (((List.range m).map A).flatten ++ ((List.range m).map B).flatten) := by
  have hwin : ∀ i < m, ∀ j < m, i ≠ j → ∀ x ∈ A i ++ B i, ∀ y ∈ A j ++ B j,
      x.1 + x.2.length ≤ y.1 ∨ y.1 + y.2.length ≤ x.1 := fun i hi j hj hij x hx y hy => by
    have h1 := hW i hi x hx; have h2 := hW j hj y hy; have := hsep i hi j hj hij; omega
  have hpr : ∀ (C : ℕ → Layout), (∀ j < m, ∀ x ∈ C j, x ∈ A j ++ B j) → (∀ j < m, DisjL (C j)) →
      DisjL ((List.range m).map C).flatten := fun C hC hCD => by
    unfold DisjL
    rw [List.pairwise_flatten, List.pairwise_map]
    refine ⟨fun l hl => ?_, (List.pairwise_lt_range (n := m)).imp_of_mem fun hi hj hij x hx y hy => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
      exact hCD j (List.mem_range.mp hj)
    · exact hwin _ (List.mem_range.mp hi) _ (List.mem_range.mp hj) (by omega) x
        (hC _ (List.mem_range.mp hi) x hx) y (hC _ (List.mem_range.mp hj) y hy)
  unfold DisjL
  rw [List.pairwise_append]
  refine ⟨hpr A (fun j _ x hx => List.mem_append_left _ hx)
      (fun j hj => (List.pairwise_append.mp (hD j hj)).1),
    hpr B (fun j _ x hx => List.mem_append_right _ hx)
      (fun j hj => (List.pairwise_append.mp (hD j hj)).2.1), fun x hx y hy => ?_⟩
  obtain ⟨_, hl1, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl1
  obtain ⟨_, hl2, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl2
  rw [List.mem_range] at hi hj
  by_cases hij : i = j
  · subst hij
    exact (List.pairwise_append.mp (hD i hi)).2.2 x hx y hy
  · exact hwin i hi j hj hij x (List.mem_append_left _ hx) y (List.mem_append_right _ hy)

end
end LeanVM.Guest.B1
