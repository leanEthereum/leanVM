/-
  LeanVM.Guest.Local.Pos

  Pre-order positions of a core body, each statement's block and innermost branch, the positions
  a path runs, and a walk of every position that the kernel evaluates.
-/

module

public import LeanVM.Guest.Memory.Fresh

/-!
# Positions in a core body

A local certificate check visits a body's statements one at a time and reads facts about other
statements by their position: the place that dominates a use, the arm a value lives in, the end
of a scope. This module numbers the statements and says what a path runs, in those numbers.

**Positions.** A block starting at position `p` puts its first statement at `p`, and each
statement `s` takes `size s` positions: itself, then the statements of its blocks in order (an
`ite`'s zero block, then its nonzero block; a `match`'s arms in order). So a statement's blocks,
and so its whole subtree, fill the interval `[p, p + size s)`: positions are pre-order indices.

**Contexts.** `AtL c p ss q s c'` says that position `q` of the block `ss` starting at `p`, whose
own context is `c`, holds the statement `s`, and that `s` is a top-level statement of a block
whose context is `c'`: `c'.e` is that block's end (one past its last position); if the block is
an arm, `c'.t` is the position of its branch (`ite` or `match`) and `c'.a` the arm's first
position. A top-level statement of `ss` itself has context `c`, which the caller chooses (and
for which `c.e = p + sizeL ss` makes `e` exact; a `t`, `a` with `a ≤ t + 1` gives an empty arm
interval).

**Paths.** `RunsL σ p ss q` says that the path `walk σ ss` runs the statement at position `q`:
the statements before it in its block fall through, and each branch around it takes its arm. The
facts that matter to a certificate:

* `walk_evs`, `walk_ret`: each event of `walk σ ss`, and its `ret`, comes from a run position
  whose statement makes it (`EvOf`), so every value a path names is named by a run statement
  (`evOf_uses`).
* `runs_dom` (**dominance**): if `q` runs and `q'` is a top-level statement of a block with
  `q' ≤ q < e` (`e` the block's end), then `q'` runs: a position runs whenever a later position
  of its block's range does.
* `runs_arm` (**exclusive arms**): if `y` runs in the arm starting at `a` of the branch at `t`,
  no position strictly between `t` and `a` runs: those are the earlier arms'.

**The kernel's walk.** `foldL step` visits every position in pre-order with its statement and
context, threading a state through `step`. Written with `Stmt.rec`, it reads each arm's end from
a list the certificate gives (in the order the arms start) and checks it when the arm ends, so it
never computes a size. `foldL_spec`: if it succeeds, there are states `f q` before each position
`q` such that `step (f q) q s c' = some (f (q + 1))` wherever `AtL c p ss q s c'`.
-/

namespace LeanVM.Guest.Local

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Positions -/

mutual
/-- The positions a statement takes: itself and its blocks' statements. -/
def size : Stmt → ℕ
  | .ite _ z n => sizeL z + sizeL n + 1
  | .match_ _ arms => sizeA arms + 1
  | _ => 1

/-- The positions a block takes. -/
def sizeL : List Stmt → ℕ
  | [] => 0
  | s :: ss => size s + sizeL ss

/-- The positions a list of arms takes. -/
def sizeA : List (List Stmt) → ℕ
  | [] => 0
  | b :: bs => sizeL b + sizeA bs
end

theorem size_pos (s : Stmt) : 0 < size s := by
  cases s <;> simp [size]

/-- A block's context: its end, and, for an arm, its branch's position and its first position. -/
structure Ctx where
  e : ℕ
  t : ℕ
  a : ℕ

mutual
/-- Position `q` of block `ss` (starting at `p`, context `c`) holds `s`, top-level in a block of
context `c'`. -/
inductive AtL : Ctx → ℕ → List Stmt → ℕ → Stmt → Ctx → Prop
  | head (c : Ctx) (p : ℕ) (s : Stmt) (ss : List Stmt) : AtL c p (s :: ss) p s c
  | inside {c : Ctx} {p : ℕ} {s : Stmt} {ss : List Stmt} {q : ℕ} {s' : Stmt} {c' : Ctx} :
      AtS p s q s' c' → AtL c p (s :: ss) q s' c'
  | tail {c : Ctx} {p : ℕ} {s : Stmt} {ss : List Stmt} {q : ℕ} {s' : Stmt} {c' : Ctx} :
      AtL c (p + size s) ss q s' c' → AtL c p (s :: ss) q s' c'

/-- Position `q`, inside a block of statement `s` at position `p`, holds `s'` of context `c'`. -/
inductive AtS : ℕ → Stmt → ℕ → Stmt → Ctx → Prop
  | zero {p : ℕ} {x : V} {z n : List Stmt} {q : ℕ} {s : Stmt} {c : Ctx} :
      AtL ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z q s c → AtS p (.ite x z n) q s c
  | nonzero {p : ℕ} {x : V} {z n : List Stmt} {q : ℕ} {s : Stmt} {c : Ctx} :
      AtL ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n q s c →
        AtS p (.ite x z n) q s c
  | arm {p : ℕ} {x : V} {arms : List (List Stmt)} {q : ℕ} {s : Stmt} {c : Ctx} :
      AtA p (p + 1) arms q s c → AtS p (.match_ x arms) q s c

/-- Position `q`, in the arms `bs` of the branch at `t` starting at `a`, holds `s` of context
`c`. -/
inductive AtA : ℕ → ℕ → List (List Stmt) → ℕ → Stmt → Ctx → Prop
  | here {t a : ℕ} {b : List Stmt} {bs : List (List Stmt)} {q : ℕ} {s : Stmt} {c : Ctx} :
      AtL ⟨a + sizeL b, t, a⟩ a b q s c → AtA t a (b :: bs) q s c
  | next {t a : ℕ} {b : List Stmt} {bs : List (List Stmt)} {q : ℕ} {s : Stmt} {c : Ctx} :
      AtA t (a + sizeL b) bs q s c → AtA t a (b :: bs) q s c
end

mutual
theorem atL_range : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {q : ℕ} {s : Stmt} {c' : Ctx},
    AtL c p ss q s c' → p ≤ q ∧ q < p + sizeL ss
  | _, _, _ :: _, _, _, _, .head .. => by
      have := size_pos ‹Stmt›; simp only [sizeL]; omega
  | _, _, _ :: _, _, _, _, .inside h => by
      have := atS_range h; simp only [sizeL]; omega
  | _, _, _ :: _, _, _, _, .tail h => by
      have := atL_range h; simp only [sizeL]; omega

theorem atS_range : ∀ {p : ℕ} {s : Stmt} {q : ℕ} {s' : Stmt} {c' : Ctx},
    AtS p s q s' c' → p < q ∧ q < p + size s
  | _, .ite .., _, _, _, .zero h => by have := atL_range h; simp only [size]; omega
  | _, .ite .., _, _, _, .nonzero h => by have := atL_range h; simp only [size]; omega
  | _, .match_ .., _, _, _, .arm h => by have := atA_range h; simp only [size]; omega

theorem atA_range : ∀ {t a : ℕ} {bs : List (List Stmt)} {q : ℕ} {s : Stmt} {c : Ctx},
    AtA t a bs q s c → a ≤ q ∧ q < a + sizeA bs
  | _, _, _ :: _, _, _, _, .here h => by have := atL_range h; simp only [sizeA]; omega
  | _, _, _ :: _, _, _, _, .next h => by have := atA_range h; simp only [sizeA]; omega
end

mutual
/-- **A position's context**: the block's own, or an arm's inside it, around the position. -/
theorem atL_ctx : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {q : ℕ} {s : Stmt} {c' : Ctx},
    AtL c p ss q s c' → c' = c ∨ (p ≤ c'.t ∧ c'.t < c'.a ∧ c'.a ≤ q ∧ q < c'.e ∧ c'.e ≤ p + sizeL ss)
  | _, _, _ :: _, _, _, _, .head .. => .inl rfl
  | _, _, _ :: _, _, _, _, .inside h => by
      have := atS_ctx h; simp only [sizeL]; right; omega
  | _, _, _ :: _, _, _, _, .tail h => by
      rcases atL_ctx h with h' | h'
      · exact .inl h'
      · simp only [sizeL]; right; omega

theorem atS_ctx : ∀ {p : ℕ} {s : Stmt} {q : ℕ} {s' : Stmt} {c' : Ctx},
    AtS p s q s' c' → p ≤ c'.t ∧ c'.t < c'.a ∧ c'.a ≤ q ∧ q < c'.e ∧ c'.e ≤ p + size s
  | _, .ite .., _, _, _, .zero h => by
      have := atL_range h
      rcases atL_ctx h with rfl | h'
      · simp only [size]; omega
      · simp only [size]; omega
  | _, .ite .., _, _, _, .nonzero h => by
      have := atL_range h
      rcases atL_ctx h with rfl | h'
      · simp only [size]; omega
      · simp only [size]; omega
  | _, .match_ .., _, _, _, .arm h => by
      have := atA_ctx h (Nat.lt_succ_self _); simp only [size]; omega

theorem atA_ctx : ∀ {t a : ℕ} {bs : List (List Stmt)} {q : ℕ} {s : Stmt} {c : Ctx},
    AtA t a bs q s c → t < a → t ≤ c.t ∧ c.t < c.a ∧ c.a ≤ q ∧ q < c.e ∧ c.e ≤ a + sizeA bs
  | _, _, _ :: _, _, _, _, .here h, hta => by
      have := atL_range h
      rcases atL_ctx h with rfl | h'
      · simp only [sizeA]; omega
      · simp only [sizeA]; omega
  | _, _, _ :: _, _, _, _, .next h, hta => by
      have := atA_ctx h (by omega); simp only [sizeA]; omega
end

/-- A top-level statement's context end, when the block's is exact, bounds the position. -/
theorem atL_e {c : Ctx} {p : ℕ} {ss : List Stmt} {q : ℕ} {s : Stmt} {c' : Ctx}
    (hc : c.e = p + sizeL ss) (h : AtL c p ss q s c') : q < c'.e ∧ c'.e ≤ p + sizeL ss := by
  have := atL_range h
  rcases atL_ctx h with rfl | h' <;> omega

/-! ## The positions a path runs -/

/-- An outcome that falls through. -/
def Falls (o : Out) : Prop := ∃ es, o = .fall es

mutual
/-- The path runs position `q` of statement `s` at position `p`: `s` itself, or a position of
the arm it takes. -/
def RunsS (σ : Val) (p : ℕ) : Stmt → ℕ → Prop
  | .ite c z n, q => q = p ∨ (σ c = 0 ∧ RunsL σ (p + 1) z q) ∨
      (σ c ≠ 0 ∧ RunsL σ (p + 1 + sizeL z) n q)
  | .match_ x arms, q => q = p ∨ RunsA σ x 0 (p + 1) arms q
  | _, q => q = p

/-- The path runs position `q` of block `ss` at `p`: the statements before it fall through. -/
def RunsL (σ : Val) (p : ℕ) : List Stmt → ℕ → Prop
  | [], _ => False
  | s :: ss, q => RunsS σ p s q ∨ (Falls (walk1 σ s) ∧ RunsL σ (p + size s) ss q)

/-- The path runs position `q` of the arms `bs` (the first numbered `j`) starting at `p`: of the
first arm `x` selects. -/
def RunsA (σ : Val) (x : V) (j p : ℕ) : List (List Stmt) → ℕ → Prop
  | [], _ => False
  | b :: bs, q => (σ x = ofK (addressOfIndex j) ∧ RunsL σ p b q) ∨
      (σ x ≠ ofK (addressOfIndex j) ∧ RunsA σ x (j + 1) (p + sizeL b) bs q)
end

theorem runsS_self (σ : Val) (p : ℕ) (s : Stmt) : RunsS σ p s p := by
  cases s <;> simp [RunsS]

variable {σ : Val}

mutual
theorem runsS_range : ∀ {p : ℕ} {s : Stmt} {q : ℕ}, RunsS σ p s q → p ≤ q ∧ q < p + size s
  | p, .ite c z n, q, h => by
      simp only [RunsS] at h
      simp only [size]
      rcases h with rfl | ⟨-, h⟩ | ⟨-, h⟩
      · omega
      · have := runsL_range h; omega
      · have := runsL_range h; omega
  | p, .match_ x arms, q, h => by
      simp only [RunsS] at h
      simp only [size]
      rcases h with rfl | h
      · omega
      · have := runsA_range h; omega
  | p, .atom _, q, h => by simp only [RunsS] at h; simp only [size]; omega
  | p, .call .., q, h => by simp only [RunsS] at h; simp only [size]; omega
  | p, .callIf .., q, h => by simp only [RunsS] at h; simp only [size]; omega
  | p, .dispatch .., q, h => by simp only [RunsS] at h; simp only [size]; omega
  | p, .ret _, q, h => by simp only [RunsS] at h; simp only [size]; omega

theorem runsL_range : ∀ {p : ℕ} {ss : List Stmt} {q : ℕ}, RunsL σ p ss q → p ≤ q ∧ q < p + sizeL ss
  | _, [], _, h => by simp [RunsL] at h
  | p, s :: ss, q, h => by
      simp only [RunsL] at h
      simp only [sizeL]
      rcases h with h | ⟨-, h⟩
      · have := runsS_range h; omega
      · have := runsL_range h; omega

theorem runsA_range : ∀ {x : V} {j p : ℕ} {bs : List (List Stmt)} {q : ℕ},
    RunsA σ x j p bs q → p ≤ q ∧ q < p + sizeA bs
  | _, _, _, [], _, h => by simp [RunsA] at h
  | x, j, p, b :: bs, q, h => by
      simp only [RunsA] at h
      simp only [sizeA]
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · have := runsL_range h; omega
      · have := runsA_range h; omega
end

/-! ## Dominance -/

mutual
/-- **Dominance**: a run position runs the top-level statements of its block's range before
it. -/
theorem runs_dom : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {q' : ℕ} {s' : Stmt} {c' : Ctx} {q : ℕ},
    c.e = p + sizeL ss → AtL c p ss q' s' c' → q' ≤ q → q < c'.e → RunsL σ p ss q → RunsL σ p ss q'
  | _, p, s :: ss, _, _, _, q, _, .head .., _, _, _ => .inl (runsS_self σ p s)
  | c, p, s :: ss, q', s', c', q, hc, .inside h, h1, h2, hr => by
      have hb := atS_ctx h
      simp only [RunsL] at hr ⊢
      rcases hr with hr | ⟨-, hr⟩
      · exact .inl (runsS_dom h h1 h2 hr)
      · have := runsL_range hr; omega
  | c, p, s :: ss, q', s', c', q, hc, .tail h, h1, h2, hr => by
      have hq' := atL_range h
      simp only [RunsL] at hr ⊢
      rcases hr with hr | ⟨hf, hr⟩
      · have := runsS_range hr; omega
      · exact .inr ⟨hf, runs_dom (by simp only [sizeL] at hc; omega) h h1 h2 hr⟩

theorem runsS_dom : ∀ {p : ℕ} {s : Stmt} {q' : ℕ} {s' : Stmt} {c' : Ctx} {q : ℕ},
    AtS p s q' s' c' → q' ≤ q → q < c'.e → RunsS σ p s q → RunsS σ p s q'
  | p, .ite x z n, q', s', c', q, .zero h, h1, h2, hr => by
      have hq' := atL_range h
      have he := atL_e rfl h
      simp only [RunsS] at hr ⊢
      rcases hr with rfl | ⟨h0, hr⟩ | ⟨-, hr⟩
      · omega
      · exact .inr (.inl ⟨h0, runs_dom rfl h h1 h2 hr⟩)
      · have := runsL_range hr; omega
  | p, .ite x z n, q', s', c', q, .nonzero h, h1, h2, hr => by
      have hq' := atL_range h
      have he := atL_e rfl h
      simp only [RunsS] at hr ⊢
      rcases hr with rfl | ⟨-, hr⟩ | ⟨h0, hr⟩
      · omega
      · have := runsL_range hr; omega
      · exact .inr (.inr ⟨h0, runs_dom rfl h h1 h2 hr⟩)
  | p, .match_ x arms, q', s', c', q, .arm h, h1, h2, hr => by
      have hq' := atA_range h
      simp only [RunsS] at hr ⊢
      rcases hr with rfl | hr
      · omega
      · exact .inr (runsA_dom h h1 h2 hr)

theorem runsA_dom : ∀ {t a : ℕ} {bs : List (List Stmt)} {q' : ℕ} {s' : Stmt} {c' : Ctx} {q : ℕ}
    {x : V} {j : ℕ}, AtA t a bs q' s' c' → q' ≤ q → q < c'.e → RunsA σ x j a bs q → RunsA σ x j a bs q'
  | t, a, b :: bs, q', s', c', q, x, j, .here h, h1, h2, hr => by
      have he := atL_e rfl h
      simp only [RunsA] at hr ⊢
      rcases hr with ⟨h0, hr⟩ | ⟨-, hr⟩
      · exact .inl ⟨h0, runs_dom rfl h h1 h2 hr⟩
      · have := runsA_range hr; omega
  | t, a, b :: bs, q', s', c', q, x, j, .next h, h1, h2, hr => by
      have hq' := atA_range h
      simp only [RunsA] at hr ⊢
      rcases hr with ⟨-, hr⟩ | ⟨h0, hr⟩
      · have := runsL_range hr; omega
      · exact .inr ⟨h0, runsA_dom h h1 h2 hr⟩
end

/-! ## Exclusive arms -/

mutual
/-- **Exclusive arms**: if `y` runs, top-level in the arm starting at `c'.a` of the branch at
`c'.t`, a run position strictly between them is in the block's own arm interval. -/
theorem runs_arm : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {y : ℕ} {s : Stmt} {c' : Ctx} {z : ℕ},
    AtL c p ss y s c' → RunsL σ p ss y → RunsL σ p ss z → c'.t < z → z < c'.a → c.t < z ∧ z < c.a
  | _, _, _ :: _, _, _, _, _, .head .., _, _, h1, h2 => ⟨h1, h2⟩
  | c, p, s :: ss, y, s', c', z, .inside h, hy, hz, h1, h2 => by
      have hb := atS_ctx h
      have hr := atS_range h
      simp only [RunsL] at hy hz
      rcases hy with hy | ⟨-, hy⟩
      · rcases hz with hz | ⟨-, hz⟩
        · exact (runsS_arm h hy hz h1 h2).elim
        · have := runsL_range hz; omega
      · have := runsL_range hy; omega
  | c, p, s :: ss, y, s', c', z, .tail h, hy, hz, h1, h2 => by
      have hr := atL_range h
      simp only [RunsL] at hy hz
      rcases hy with hy | ⟨-, hy⟩
      · have := runsS_range hy; omega
      · rcases hz with hz | ⟨-, hz⟩
        · have := runsS_range hz
          rcases atL_ctx h with rfl | h'
          · exact ⟨h1, h2⟩
          · omega
        · exact runs_arm h hy hz h1 h2

theorem runsS_arm : ∀ {p : ℕ} {s : Stmt} {y : ℕ} {s' : Stmt} {c' : Ctx} {z : ℕ},
    AtS p s y s' c' → RunsS σ p s y → RunsS σ p s z → c'.t < z → z < c'.a → False
  | p, .ite x zb nb, y, s', c', z, .zero h, hy, hz, h1, h2 => by
      have hb := atS_ctx (.zero (x := x) (n := nb) h)
      have hr := atL_range h
      simp only [RunsS] at hy hz
      rcases hy with rfl | ⟨h0, hy⟩ | ⟨-, hy⟩
      · omega
      · rcases hz with rfl | ⟨-, hz⟩ | ⟨h0', -⟩
        · omega
        · have := runs_arm h hy hz h1 h2; simp at this; omega
        · exact h0' h0
      · have := runsL_range hy; omega
  | p, .ite x zb nb, y, s', c', z, .nonzero h, hy, hz, h1, h2 => by
      have hb := atS_ctx (.nonzero (x := x) (z := zb) h)
      have hr := atL_range h
      simp only [RunsS] at hy hz
      rcases hy with rfl | ⟨-, hy⟩ | ⟨h0, hy⟩
      · omega
      · have := runsL_range hy; omega
      · rcases hz with rfl | ⟨h0', -⟩ | ⟨-, hz⟩
        · omega
        · exact h0 h0'
        · have := runs_arm h hy hz h1 h2; have := runsL_range hz; simp at *; omega
  | p, .match_ x arms, y, s', c', z, .arm h, hy, hz, h1, h2 => by
      have hb := atA_ctx h (Nat.lt_succ_self _)
      have hr := atA_range h
      simp only [RunsS] at hy hz
      rcases hy with rfl | hy
      · omega
      · rcases hz with rfl | hz
        · omega
        · exact runsA_arm h hy hz h1 h2 (by omega)

theorem runsA_arm : ∀ {t a : ℕ} {bs : List (List Stmt)} {y : ℕ} {s' : Stmt} {c' : Ctx} {z : ℕ}
    {x : V} {j : ℕ}, AtA t a bs y s' c' → RunsA σ x j a bs y → RunsA σ x j a bs z →
      c'.t < z → z < c'.a → a ≤ z → False
  | t, a, b :: bs, y, s', c', z, x, j, .here h, hy, hz, h1, h2, h3 => by
      have hr := atL_range h
      simp only [RunsA] at hy hz
      rcases hy with ⟨h0, hy⟩ | ⟨-, hy⟩
      · rcases hz with ⟨-, hz⟩ | ⟨h0', -⟩
        · have := runs_arm h hy hz h1 h2; simp at this; omega
        · exact h0' h0
      · have := runsA_range hy; omega
  | t, a, b :: bs, y, s', c', z, x, j, .next h, hy, hz, h1, h2, h3 => by
      have hr := atA_range h
      simp only [RunsA] at hy hz
      rcases hy with ⟨-, hy⟩ | ⟨h0, hy⟩
      · have := runsL_range hy; omega
      · rcases hz with ⟨h0', -⟩ | ⟨-, hz⟩
        · exact h0 h0'
        · exact runsA_arm h hy hz h1 h2 (runsA_range hz).1
end

/-- **Exclusive arms**, for a block whose own arm interval is empty (`c.a ≤ c.t + 1`, as for a
body): no position strictly between a run position's branch and arm start runs. -/
theorem runs_arm' {c : Ctx} {p : ℕ} {ss : List Stmt} {y : ℕ} {s : Stmt} {c' : Ctx} {z : ℕ}
    (hc : c.a ≤ c.t + 1) (h : AtL c p ss y s c') (hy : RunsL σ p ss y) (h1 : c'.t < z)
    (h2 : z < c'.a) : ¬ RunsL σ p ss z := fun hz ↦ by
  have := runs_arm h hy hz h1 h2; omega

/-! ## Events -/

/-- The events statement `s` makes at its own position. -/
def EvOf : Stmt → Ev → Prop
  | .atom a, e => e = .atom a
  | .ite c _ _, e => e = .inK c
  | .call f args rets, e => e = .call f args rets
  | .callIf c f args, e => e = .inK c ∨ e = .skip f args ∨ e = .call f args []
  | .dispatch _ fs args rets, e => ∃ f ∈ fs, e = .call f args rets
  | _, _ => False

/-- The values statement `s` names at its own position (its blocks' apart). -/
def names : Stmt → List V
  | .atom a => atomUses a
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs

theorem evOf_uses {s : Stmt} {e : Ev} (h : EvOf s e) {v : V} (hv : v ∈ e.uses) : v ∈ names s := by
  cases s with
  | atom a => simp only [EvOf] at h; subst h; exact hv
  | ite c z n => simp only [EvOf] at h; subst h; simpa [Ev.uses, names] using hv
  | match_ x arms => simp [EvOf] at h
  | call f args rets => simp only [EvOf] at h; subst h; simpa [Ev.uses, names] using hv
  | callIf c f args =>
    simp only [EvOf] at h
    rcases h with rfl | rfl | rfl <;> simp_all [Ev.uses, names]
  | dispatch x fs args rets =>
    simp only [EvOf] at h
    obtain ⟨f, -, rfl⟩ := h
    simp only [Ev.uses, List.mem_append] at hv
    simp only [names, List.mem_cons, List.mem_append]
    tauto
  | ret vs => simp [EvOf] at h

theorem evOf_tmps {s : Stmt} {e : Ev} (h : EvOf s e) {v : V} (hv : v ∈ e.tmps) :
    ∃ a, s = .atom a ∧ v ∈ atomTmps a := by
  cases s <;> simp only [EvOf] at h
  case atom a => subst h; exact ⟨a, rfl, hv⟩
  all_goals first
    | (subst h; simp [Ev.tmps] at hv)
    | (rcases h with rfl | rfl | rfl <;> simp [Ev.tmps] at hv)
    | (obtain ⟨_, -, rfl⟩ := h; simp [Ev.tmps] at hv)

theorem pick_evs {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {e : Ev},
    e ∈ (pick σ x args rets j fs).evs → ∃ f ∈ fs, e = .call f args rets
  | [], _, _, h => by simp [pick, Out.evs] at h
  | f :: fs, j, e, h => by
      unfold pick at h
      split_ifs at h
      · simp only [Out.evs, List.mem_singleton] at h; exact ⟨f, List.mem_cons_self, h⟩
      · obtain ⟨g, hg, rfl⟩ := pick_evs fs (j + 1) h
        exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩

theorem pick_ret {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {es : List Ev}
    {vs : List V}, pick σ x args rets j fs ≠ .ret es vs
  | [], _, _, _, h => by simp [pick] at h
  | f :: fs, j, _, _, h => by
      unfold pick at h
      split_ifs at h
      exact pick_ret fs (j + 1) h

theorem evs_pre {es : List Ev} {o : Out} {e : Ev} (h : e ∈ (o.pre es).evs) : e ∈ es ∨ e ∈ o.evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

theorem evs_seq {o k : Out} {e : Ev} (h : e ∈ (o.seq k).evs) :
    e ∈ o.evs ∨ (Falls o ∧ e ∈ k.evs) := by
  cases o with
  | fall es =>
    simp only [Out.seq] at h
    rcases evs_pre h with h | h
    · exact .inl h
    · exact .inr ⟨⟨es, rfl⟩, h⟩
  | ret es vs => exact .inl h
  | stuck => simp [Out.seq, Out.evs] at h

mutual
/-- **Every event of a path is made by a run statement.** -/
theorem walk1_evs : ∀ (p : ℕ) (s : Stmt) {e : Ev}, e ∈ (walk1 σ s).evs →
    EvOf s e ∨ ∃ q s' c', AtS p s q s' c' ∧ RunsS σ p s q ∧ EvOf s' e
  | p, .atom a, e, h => by simp only [walk1, Out.evs, List.mem_singleton] at h; exact .inl h
  | p, .ite c z n, e, h => by
      simp only [walk1] at h
      rcases evs_pre h with h | h
      · simp only [List.mem_singleton] at h; exact .inl h
      · right
        split_ifs at h with h0
        · obtain ⟨q, s', c', h1, h2, h3⟩ := walk_evs ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z h
          exact ⟨q, s', c', .zero h1, by simp only [RunsS]; exact .inr (.inl ⟨h0, h2⟩), h3⟩
        · obtain ⟨q, s', c', h1, h2, h3⟩ :=
            walk_evs ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n h
          exact ⟨q, s', c', .nonzero h1, by simp only [RunsS]; exact .inr (.inr ⟨h0, h2⟩), h3⟩
  | p, .match_ x arms, e, h => by
      simp only [walk1] at h
      obtain ⟨q, s', c', h1, h2, h3⟩ := walkArms_evs p x arms 0 (p + 1) h
      exact .inr ⟨q, s', c', .arm h1, by simp only [RunsS]; exact .inr h2, h3⟩
  | p, .call f args rets, e, h => by
      simp only [walk1, Out.evs, List.mem_singleton] at h; exact .inl h
  | p, .callIf c f args, e, h => by
      simp only [walk1, Out.evs] at h
      left
      simp only [EvOf]
      split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> tauto
  | p, .dispatch x fs args rets, e, h => by
      simp only [walk1] at h
      exact .inl (pick_evs fs 0 h)
  | p, .ret vs, e, h => by simp [walk1, Out.evs] at h

theorem walk_evs : ∀ (c : Ctx) (p : ℕ) (ss : List Stmt) {e : Ev}, e ∈ (walk σ ss).evs →
    ∃ q s c', AtL c p ss q s c' ∧ RunsL σ p ss q ∧ EvOf s e
  | c, p, [], e, h => by simp [walk, Out.evs] at h
  | c, p, s :: ss, e, h => by
      simp only [walk] at h
      rcases evs_seq h with h | ⟨hf, h⟩
      · rcases walk1_evs p s h with h | ⟨q, s', c', h1, h2, h3⟩
        · exact ⟨p, s, c, .head c p s ss, .inl (runsS_self σ p s), h⟩
        · exact ⟨q, s', c', .inside h1, .inl h2, h3⟩
      · obtain ⟨q, s', c', h1, h2, h3⟩ := walk_evs c (p + size s) ss h
        exact ⟨q, s', c', .tail h1, .inr ⟨hf, h2⟩, h3⟩

theorem walkArms_evs : ∀ (t : ℕ) (x : V) (bs : List (List Stmt)) (j a : ℕ) {e : Ev},
    e ∈ (walkArms σ x j bs).evs → ∃ q s c', AtA t a bs q s c' ∧ RunsA σ x j a bs q ∧ EvOf s e
  | t, x, [], j, a, e, h => by simp [walkArms, Out.evs] at h
  | t, x, b :: bs, j, a, e, h => by
      unfold walkArms at h
      split_ifs at h with h0
      · obtain ⟨q, s, c', h1, h2, h3⟩ := walk_evs ⟨a + sizeL b, t, a⟩ a b h
        exact ⟨q, s, c', .here h1, by simp only [RunsA]; exact .inl ⟨h0, h2⟩, h3⟩
      · obtain ⟨q, s, c', h1, h2, h3⟩ := walkArms_evs t x bs (j + 1) (a + sizeL b) h
        exact ⟨q, s, c', .next h1, by simp only [RunsA]; exact .inr ⟨h0, h2⟩, h3⟩
end

mutual
/-- **A path's `ret` is a run statement.** -/
theorem walk1_ret : ∀ (p : ℕ) (s : Stmt) {es : List Ev} {vs : List V}, walk1 σ s = .ret es vs →
    s = .ret vs ∨ ∃ q c', AtS p s q (.ret vs) c' ∧ RunsS σ p s q
  | p, .atom a, _, _, h => by simp [walk1] at h
  | p, .ite c z n, es, vs, h => by
      simp only [walk1] at h
      right
      split_ifs at h with h0
      · cases hz : walk σ z <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq, Out.ret.injEq] at h
        obtain ⟨q, c', h1, h2⟩ := walk_ret ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z (by rw [hz, h.2])
        exact ⟨q, c', .zero h1, by simp only [RunsS]; exact .inr (.inl ⟨h0, h2⟩)⟩
      · cases hz : walk σ n <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq, Out.ret.injEq] at h
        obtain ⟨q, c', h1, h2⟩ :=
          walk_ret ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n (by rw [hz, h.2])
        exact ⟨q, c', .nonzero h1, by simp only [RunsS]; exact .inr (.inr ⟨h0, h2⟩)⟩
  | p, .match_ x arms, es, vs, h => by
      simp only [walk1] at h
      obtain ⟨q, c', h1, h2⟩ := walkArms_ret p x arms 0 (p + 1) h
      exact .inr ⟨q, c', .arm h1, by simp only [RunsS]; exact .inr h2⟩
  | p, .call .., _, _, h => by simp [walk1] at h
  | p, .callIf .., _, _, h => by simp [walk1] at h
  | p, .dispatch x fs args rets, _, _, h => by simp only [walk1] at h; exact (pick_ret fs 0 h).elim
  | p, .ret vs', es, vs, h => by simp only [walk1, Out.ret.injEq] at h; exact .inl (by rw [h.2])

theorem walk_ret : ∀ (c : Ctx) (p : ℕ) (ss : List Stmt) {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∃ q c', AtL c p ss q (.ret vs) c' ∧ RunsL σ p ss q
  | c, p, [], _, _, h => by simp [walk] at h
  | c, p, s :: ss, es, vs, h => by
      simp only [walk] at h
      cases h1 : walk1 σ s with
      | fall es1 =>
        rw [h1] at h
        cases h2 : walk σ ss <;> rw [h2] at h <;> simp only [Out.seq, Out.pre, reduceCtorEq, Out.ret.injEq] at h
        obtain ⟨q, c', h3, h4⟩ := walk_ret c (p + size s) ss (by rw [h2, h.2])
        exact ⟨q, c', .tail h3, .inr ⟨⟨es1, h1⟩, h4⟩⟩
      | ret es1 vs1 =>
        rw [h1] at h
        simp only [Out.seq, Out.ret.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases walk1_ret p s h1 with rfl | ⟨q, c', h3, h4⟩
        · exact ⟨p, c, .head c p _ ss, .inl (runsS_self σ p _)⟩
        · exact ⟨q, c', .inside h3, .inl h4⟩
      | stuck => rw [h1] at h; simp [Out.seq] at h

theorem walkArms_ret : ∀ (t : ℕ) (x : V) (bs : List (List Stmt)) (j a : ℕ) {es : List Ev} {vs : List V},
    walkArms σ x j bs = .ret es vs → ∃ q c', AtA t a bs q (.ret vs) c' ∧ RunsA σ x j a bs q
  | t, x, [], j, a, _, _, h => by simp [walkArms] at h
  | t, x, b :: bs, j, a, es, vs, h => by
      unfold walkArms at h
      split_ifs at h with h0
      · obtain ⟨q, c', h1, h2⟩ := walk_ret ⟨a + sizeL b, t, a⟩ a b h
        exact ⟨q, c', .here h1, by simp only [RunsA]; exact .inl ⟨h0, h2⟩⟩
      · obtain ⟨q, c', h1, h2⟩ := walkArms_ret t x bs (j + 1) (a + sizeL b) h
        exact ⟨q, c', .next h1, by simp only [RunsA]; exact .inr ⟨h0, h2⟩⟩
end

/-- **Every value a returning path names** (its events' and its returned values) is named by a
run statement. -/
theorem walk_names {c : Ctx} {p : ℕ} {ss : List Stmt} {es : List Ev} {vs : List V}
    (hw : walk σ ss = .ret es vs) {v : V} (hv : v ∈ es.flatMap Ev.uses ++ vs) :
    ∃ q s c', AtL c p ss q s c' ∧ RunsL σ p ss q ∧ v ∈ names s := by
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have he' : e ∈ (walk σ ss).evs := by rw [hw]; exact he
    obtain ⟨q, s, c', h1, h2, h3⟩ := walk_evs c p ss he'
    exact ⟨q, s, c', h1, h2, evOf_uses h3 hv⟩
  · obtain ⟨q, c', h1, h2⟩ := walk_ret c p ss hw
    exact ⟨q, _, c', h1, h2, hv⟩

end
end LeanVM.Guest.Local
