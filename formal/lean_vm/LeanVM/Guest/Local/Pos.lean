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
* `runsL_loc` (**localization**): a run position inside the subtree of the statement at `t` is run by that
  statement; so a run position in an `ite`'s zero (nonzero) branch has its guard `0` (not `0`), `runs_zero`
  (`runs_nonzero`), and one in arm `i` of a `match` its selector `g^i` (`runs_sel`).
* `runsL_after`: a run position past a statement's subtree, in its block, follows the statement falling through;
  `runsL_of_falls`: a block falling through runs its top-level statements (with `falls_ite`, `walkArms_falls`: the
  arm taken falls through). Together, a fact every falling arm establishes holds after the branch (a join).
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

theorem sizeA_take_le : ∀ (bs : List (List Stmt)) (i : ℕ), sizeA (bs.take i) ≤ sizeA bs
  | [], _ => by simp [sizeA]
  | _ :: _, 0 => by simp [sizeA]
  | b :: bs, i + 1 => by simp only [List.take_succ_cons, sizeA]; have := sizeA_take_le bs i; omega

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

mutual
/-- A top-level statement's whole subtree fits in its block. -/
theorem atL_sub : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {q : ℕ} {s : Stmt} {c' : Ctx},
    AtL c p ss q s c' → q + size s ≤ p + sizeL ss
  | _, _, _ :: _, _, _, _, .head .. => by simp only [sizeL]; omega
  | _, _, _ :: _, _, _, _, .inside h => by have := atS_sub h; simp only [sizeL]; omega
  | _, _, _ :: _, _, _, _, .tail h => by have := atL_sub h; simp only [sizeL]; omega

theorem atS_sub : ∀ {p : ℕ} {s : Stmt} {q : ℕ} {s' : Stmt} {c' : Ctx},
    AtS p s q s' c' → q + size s' ≤ p + size s
  | _, .ite .., _, _, _, .zero h => by have := atL_sub h; simp only [size]; omega
  | _, .ite .., _, _, _, .nonzero h => by have := atL_sub h; simp only [size]; omega
  | _, .match_ .., _, _, _, .arm h => by have := atA_sub h; simp only [size]; omega

theorem atA_sub : ∀ {t a : ℕ} {bs : List (List Stmt)} {q : ℕ} {s : Stmt} {c : Ctx},
    AtA t a bs q s c → q + size s ≤ a + sizeA bs
  | _, _, _ :: _, _, _, _, .here h => by have := atL_sub h; simp only [sizeA]; omega
  | _, _, _ :: _, _, _, _, .next h => by have := atA_sub h; simp only [sizeA]; omega
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

/-! ## Localization -/

mutual
/-- **Localization**: a run position inside the subtree of the statement at `t` is run by that statement (it runs
`t` and the arms leading to the position). -/
theorem runsL_loc : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {t : ℕ} {s : Stmt} {c' : Ctx} {q : ℕ},
    AtL c p ss t s c' → t ≤ q → q < t + size s → RunsL σ p ss q → RunsS σ t s q
  | _, p, s :: ss, _, _, _, q, .head .., _, _, hr => by
      simp only [RunsL] at hr
      rcases hr with hr | ⟨-, hr⟩
      · exact hr
      · have := runsL_range hr; omega
  | _, p, s :: ss, t, s', c', q, .inside h, h1, h2, hr => by
      have := atS_sub h
      simp only [RunsL] at hr
      rcases hr with hr | ⟨-, hr⟩
      · exact runsS_loc h h1 h2 hr
      · have := runsL_range hr; omega
  | _, p, s :: ss, t, s', c', q, .tail h, h1, h2, hr => by
      have := atL_range h
      simp only [RunsL] at hr
      rcases hr with hr | ⟨-, hr⟩
      · have := runsS_range hr; omega
      · exact runsL_loc h h1 h2 hr

theorem runsS_loc : ∀ {p : ℕ} {s : Stmt} {t : ℕ} {s' : Stmt} {c' : Ctx} {q : ℕ},
    AtS p s t s' c' → t ≤ q → q < t + size s' → RunsS σ p s q → RunsS σ t s' q
  | p, .ite x z n, t, s', c', q, .zero h, h1, h2, hr => by
      have := atL_range h; have := atL_sub h
      simp only [RunsS] at hr
      rcases hr with rfl | ⟨-, hr⟩ | ⟨-, hr⟩
      · omega
      · exact runsL_loc h h1 h2 hr
      · have := runsL_range hr; omega
  | p, .ite x z n, t, s', c', q, .nonzero h, h1, h2, hr => by
      have := atL_range h; have := atL_sub h
      simp only [RunsS] at hr
      rcases hr with rfl | ⟨-, hr⟩ | ⟨-, hr⟩
      · omega
      · have := runsL_range hr; omega
      · exact runsL_loc h h1 h2 hr
  | p, .match_ x arms, t, s', c', q, .arm h, h1, h2, hr => by
      have := atA_range h
      simp only [RunsS] at hr
      rcases hr with rfl | hr
      · omega
      · exact runsA_loc h h1 h2 hr

theorem runsA_loc : ∀ {t0 a : ℕ} {bs : List (List Stmt)} {t : ℕ} {s : Stmt} {c' : Ctx} {q : ℕ} {x : V} {j : ℕ},
    AtA t0 a bs t s c' → t ≤ q → q < t + size s → RunsA σ x j a bs q → RunsS σ t s q
  | _, a, b :: bs, t, s, c', q, x, j, .here h, h1, h2, hr => by
      have := atL_sub h
      simp only [RunsA] at hr
      rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
      · exact runsL_loc h h1 h2 hr
      · have := runsA_range hr; omega
  | _, a, b :: bs, t, s, c', q, x, j, .next h, h1, h2, hr => by
      have := atA_range h
      simp only [RunsA] at hr
      rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
      · have := runsL_range hr; omega
      · exact runsA_loc h h1 h2 hr
end

/-- **A run position in an `ite`'s zero branch**: its guard is `0`. -/
theorem runs_zero {c : Ctx} {p : ℕ} {ss : List Stmt} {t : ℕ} {x : V} {z n : List Stmt} {c' : Ctx} {q : ℕ}
    (h : AtL c p ss t (.ite x z n) c') (h1 : t + 1 ≤ q) (h2 : q < t + 1 + sizeL z) (hr : RunsL σ p ss q) :
    σ x = 0 := by
  have hs := runsL_loc h (by omega) (by simp only [size]; omega) hr
  simp only [RunsS] at hs
  rcases hs with rfl | ⟨h0, -⟩ | ⟨-, hr⟩
  · omega
  · exact h0
  · have := runsL_range hr; omega

/-- **A run position in an `ite`'s nonzero branch**: its guard is not `0`. -/
theorem runs_nonzero {c : Ctx} {p : ℕ} {ss : List Stmt} {t : ℕ} {x : V} {z n : List Stmt} {c' : Ctx} {q : ℕ}
    (h : AtL c p ss t (.ite x z n) c') (h1 : t + 1 + sizeL z ≤ q) (h2 : q < t + 1 + sizeL z + sizeL n)
    (hr : RunsL σ p ss q) : σ x ≠ 0 := by
  have hs := runsL_loc h (by omega) (by simp only [size]; omega) hr
  simp only [RunsS] at hs
  rcases hs with rfl | ⟨-, hr⟩ | ⟨h0, -⟩
  · omega
  · have := runsL_range hr; omega
  · exact h0

/-- A run position in arm `i` of the arms from `a` (the first numbered `j`): the selector is `g^(j + i)`. -/
theorem runsA_sel {x : V} : ∀ {j a : ℕ} {bs : List (List Stmt)} {q : ℕ} (i : ℕ), RunsA σ x j a bs q →
    a + sizeA (bs.take i) ≤ q → q < a + sizeA (bs.take (i + 1)) → σ x = ofK (addressOfIndex (j + i))
  | _, _, [], _, _, hr, _, _ => by simp [RunsA] at hr
  | j, a, b :: bs, q, 0, hr, _, h2 => by
      simp only [RunsA] at hr
      rcases hr with ⟨h0, -⟩ | ⟨-, hr⟩
      · exact h0
      · have := runsA_range hr; simp [sizeA] at h2; omega
  | j, a, b :: bs, q, i + 1, hr, h1, h2 => by
      simp only [RunsA] at hr
      simp only [List.take_succ_cons, sizeA] at h1 h2
      rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
      · have := runsL_range hr; omega
      · rw [show j + (i + 1) = j + 1 + i by omega]
        exact runsA_sel i hr (by omega) (by omega)

/-- **A run position in arm `i` of a `match`**: its selector is `g^i`. -/
theorem runs_sel {c : Ctx} {p : ℕ} {ss : List Stmt} {t : ℕ} {x : V} {arms : List (List Stmt)} {c' : Ctx} {q : ℕ}
    (h : AtL c p ss t (.match_ x arms) c') (i : ℕ) (h1 : t + 1 + sizeA (arms.take i) ≤ q)
    (h2 : q < t + 1 + sizeA (arms.take (i + 1))) (hr : RunsL σ p ss q) : σ x = ofK (addressOfIndex i) := by
  have hle : sizeA (arms.take (i + 1)) ≤ sizeA arms := sizeA_take_le arms (i + 1)
  have hs := runsL_loc h (by omega) (by simp only [size]; omega) hr
  simp only [RunsS] at hs
  rcases hs with rfl | hs
  · omega
  · have := runsA_sel i hs h1 h2; rwa [Nat.zero_add] at this

/-! ## Falling through -/

theorem falls_seq {o k : Out} (h : Falls (o.seq k)) : Falls o ∧ Falls k := by
  obtain ⟨es, h⟩ := h
  cases o with
  | fall es1 =>
    refine ⟨⟨es1, rfl⟩, ?_⟩
    cases k with
    | fall es2 => exact ⟨es2, rfl⟩
    | ret _ _ => cases h
    | stuck => cases h
  | ret _ _ => cases h
  | stuck => cases h

theorem falls_pre {o : Out} {es : List Ev} (h : Falls (o.pre es)) : Falls o := by
  obtain ⟨es', h⟩ := h
  cases o with
  | fall es1 => exact ⟨es1, rfl⟩
  | ret _ _ => cases h
  | stuck => cases h

/-- **A block that falls through runs its top-level statements** (those of its own context `c`, whose branch is
before it). -/
theorem runsL_of_falls : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {q : ℕ} {s : Stmt}, Falls (walk σ ss) →
    AtL c p ss q s c → c.t < p → RunsL σ p ss q
  | c, p, s :: ss, _, _, _, .head .., _ => .inl (runsS_self σ p s)
  | c, p, s :: ss, q, s', _, .inside h, _ => by have := atS_ctx h; omega
  | c, p, s :: ss, q, s', hf, .tail h, hct => by
      have hf' := falls_seq hf
      exact .inr ⟨hf'.1, runsL_of_falls hf'.2 h (by omega)⟩

/-- An `ite` falling through: the branch taken falls through. -/
theorem falls_ite {x : V} {z n : List Stmt} (h : Falls (walk1 σ (.ite x z n))) :
    (σ x = 0 → Falls (walk σ z)) ∧ (σ x ≠ 0 → Falls (walk σ n)) := by
  simp only [walk1] at h
  have h := falls_pre h
  exact ⟨fun h0 ↦ by rwa [ite_eq_left h0] at h, fun h0 ↦ by rwa [ite_eq_right h0] at h⟩

/-- Arms falling through: the arm `i` taken, `x = g^(j + i)`, falls through. -/
theorem walkArms_falls {x : V} : ∀ {j : ℕ} {bs : List (List Stmt)}, Falls (walkArms σ x j bs) →
    ∃ i b, bs[i]? = some b ∧ σ x = ofK (addressOfIndex (j + i)) ∧ Falls (walk σ b)
  | _, [], h => by obtain ⟨_, h⟩ := h; cases h
  | j, b :: bs, h => by
      unfold walkArms at h
      split_ifs at h with h0
      · exact ⟨0, b, rfl, by rwa [Nat.add_zero], h⟩
      · obtain ⟨i, b', hb, hx, hf⟩ := walkArms_falls h
        exact ⟨i + 1, b', by simpa using hb, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hx, hf⟩

theorem sizeA_take_succ : ∀ {bs : List (List Stmt)} {i : ℕ} {b : List Stmt}, bs[i]? = some b →
    sizeA (bs.take (i + 1)) = sizeA (bs.take i) + sizeL b
  | [], _, _, h => by cases h
  | b' :: bs, 0, b, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp [sizeA]
  | b' :: bs, i + 1, b, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.take_succ_cons, sizeA, sizeA_take_succ h]; omega

mutual
/-- **A statement a path runs past falls through**: a run position after the subtree of the statement at `t`, in its
block, follows the statement falling through. -/
theorem runsL_after : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {t : ℕ} {s : Stmt} {c' : Ctx} {q : ℕ},
    AtL c p ss t s c' → t + size s ≤ q → q < c'.e → RunsL σ p ss q → Falls (walk1 σ s)
  | _, p, s :: ss, _, _, _, q, .head .., h1, _, hr => by
      simp only [RunsL] at hr
      rcases hr with hr | ⟨hf, -⟩
      · have := runsS_range hr; omega
      · exact hf
  | _, p, s :: ss, t, s', c', q, .inside h, h1, h2, hr => by
      have := atS_ctx h
      simp only [RunsL] at hr
      rcases hr with hr | ⟨-, hr⟩
      · exact runsS_after h h1 h2 hr
      · have := runsL_range hr; omega
  | _, p, s :: ss, t, s', c', q, .tail h, h1, h2, hr => by
      have := atL_range h
      simp only [RunsL] at hr
      rcases hr with hr | ⟨-, hr⟩
      · have := runsS_range hr; omega
      · exact runsL_after h h1 h2 hr

theorem runsS_after : ∀ {p : ℕ} {s : Stmt} {t : ℕ} {s' : Stmt} {c' : Ctx} {q : ℕ},
    AtS p s t s' c' → t + size s' ≤ q → q < c'.e → RunsS σ p s q → Falls (walk1 σ s')
  | p, .ite x z n, t, s', c', q, .zero h, h1, h2, hr => by
      have := atL_range h; have := atL_e rfl h; have := size_pos s'
      simp only [RunsS] at hr
      rcases hr with rfl | ⟨-, hr⟩ | ⟨-, hr⟩
      · omega
      · exact runsL_after h h1 h2 hr
      · have := runsL_range hr; omega
  | p, .ite x z n, t, s', c', q, .nonzero h, h1, h2, hr => by
      have := atL_range h; have := atL_e rfl h; have := size_pos s'
      simp only [RunsS] at hr
      rcases hr with rfl | ⟨-, hr⟩ | ⟨-, hr⟩
      · omega
      · have := runsL_range hr; omega
      · exact runsL_after h h1 h2 hr
  | p, .match_ x arms, t, s', c', q, .arm h, h1, h2, hr => by
      have := atA_range h; have := size_pos s'
      simp only [RunsS] at hr
      rcases hr with rfl | hr
      · omega
      · exact runsA_after h h1 h2 hr

theorem runsA_after : ∀ {t0 a : ℕ} {bs : List (List Stmt)} {t : ℕ} {s : Stmt} {c' : Ctx} {q : ℕ} {x : V} {j : ℕ},
    AtA t0 a bs t s c' → t + size s ≤ q → q < c'.e → RunsA σ x j a bs q → Falls (walk1 σ s)
  | _, a, b :: bs, t, s, c', q, x, j, .here h, h1, h2, hr => by
      have := atL_e rfl h
      simp only [RunsA] at hr
      rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
      · exact runsL_after h h1 h2 hr
      · have := runsA_range hr; omega
  | _, a, b :: bs, t, s, c', q, x, j, .next h, h1, h2, hr => by
      have := atA_range h
      simp only [RunsA] at hr
      rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
      · have := runsL_range hr; omega
      · exact runsA_after h h1 h2 hr
end

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

/-! ## Every position holds a statement -/

mutual
theorem atL_exists : ∀ (c : Ctx) (p : ℕ) (ss : List Stmt) (q : ℕ), p ≤ q → q < p + sizeL ss →
    ∃ s c', AtL c p ss q s c'
  | _, _, [], _, h1, h2 => by simp [sizeL] at h2; omega
  | c, p, s :: ss, q, h1, h2 => by
      simp only [sizeL] at h2
      by_cases hq : q = p
      · subst hq; exact ⟨s, c, .head c q s ss⟩
      by_cases hs : q < p + size s
      · obtain ⟨s', c', h⟩ := atS_exists p s q (by omega) hs
        exact ⟨s', c', .inside h⟩
      · obtain ⟨s', c', h⟩ := atL_exists c (p + size s) ss q (by omega) (by omega)
        exact ⟨s', c', .tail h⟩

theorem atS_exists : ∀ (p : ℕ) (s : Stmt) (q : ℕ), p < q → q < p + size s → ∃ s' c', AtS p s q s' c'
  | p, .ite x z n, q, h1, h2 => by
      simp only [size] at h2
      by_cases hz : q < p + 1 + sizeL z
      · obtain ⟨s', c', h⟩ := atL_exists ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z q (by omega) hz
        exact ⟨s', c', .zero h⟩
      · obtain ⟨s', c', h⟩ := atL_exists ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n q
          (by omega) (by omega)
        exact ⟨s', c', .nonzero h⟩
  | p, .match_ x arms, q, h1, h2 => by
      simp only [size] at h2
      obtain ⟨s', c', h⟩ := atA_exists p (p + 1) arms q (by omega) (by omega)
      exact ⟨s', c', .arm h⟩
  | p, .atom _, q, h1, h2 => by simp only [size] at h2; omega
  | p, .call .., q, h1, h2 => by simp only [size] at h2; omega
  | p, .callIf .., q, h1, h2 => by simp only [size] at h2; omega
  | p, .dispatch .., q, h1, h2 => by simp only [size] at h2; omega
  | p, .ret _, q, h1, h2 => by simp only [size] at h2; omega

theorem atA_exists : ∀ (t a : ℕ) (bs : List (List Stmt)) (q : ℕ), a ≤ q → q < a + sizeA bs →
    ∃ s c', AtA t a bs q s c'
  | _, _, [], _, h1, h2 => by simp [sizeA] at h2; omega
  | t, a, b :: bs, q, h1, h2 => by
      simp only [sizeA] at h2
      by_cases hb : q < a + sizeL b
      · obtain ⟨s, c', h⟩ := atL_exists ⟨a + sizeL b, t, a⟩ a b q h1 hb
        exact ⟨s, c', .here h⟩
      · obtain ⟨s, c', h⟩ := atA_exists t (a + sizeL b) bs q (by omega) (by omega)
        exact ⟨s, c', .next h⟩
end

/-! ## A run atom is an event -/

theorem pre_ne_stuck {es : List Ev} {o : Out} (h : o.pre es ≠ .stuck) : o ≠ .stuck := by
  rintro rfl; exact h rfl

theorem evs_pre_right {es : List Ev} {o : Out} {e : Ev} (h : e ∈ o.evs) : e ∈ (o.pre es).evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

mutual
/-- **A run atom is an event** of a path that does not get stuck. -/
theorem runs_atom : ∀ {c : Ctx} {p : ℕ} {ss : List Stmt} {q : ℕ} {a : Core.Atom} {c' : Ctx},
    AtL c p ss q (.atom a) c' → RunsL σ p ss q → walk σ ss ≠ .stuck → Ev.atom a ∈ (walk σ ss).evs
  | _, _, _ :: ss, _, _, _, .head .., _, hw => by
      simp only [walk, walk1, Out.seq] at hw ⊢
      cases h2 : walk σ ss <;> simp_all [Out.pre, Out.evs]
  | _, p, s :: ss, q, a, c', .inside h, hr, hw => by
      have hb := atS_range h
      simp only [RunsL] at hr
      rcases hr with hr | ⟨-, hr⟩
      · simp only [walk] at hw ⊢
        have h1' := runsS_atom h hr
        cases h1 : walk1 σ s with
        | fall es =>
          have := h1' (by rw [h1]; exact fun h ↦ nomatch h); rw [h1] at this
          simp only [h1, Out.seq] at hw ⊢
          cases h2 : walk σ ss <;> simp_all [Out.pre, Out.evs]
        | ret es vs =>
          have := h1' (by rw [h1]; exact fun h ↦ nomatch h); rw [h1] at this
          simpa [h1, Out.seq] using this
        | stuck => simp [h1, Out.seq] at hw
      · have := runsL_range hr; omega
  | _, p, s :: ss, q, a, c', .tail h, hr, hw => by
      have hb := atL_range h
      simp only [RunsL] at hr
      rcases hr with hr | ⟨⟨es, hf⟩, hr⟩
      · have := runsS_range hr; omega
      · simp only [walk, hf, Out.seq] at hw ⊢
        exact evs_pre_right (runs_atom h hr (pre_ne_stuck hw))

theorem runsS_atom : ∀ {p : ℕ} {s : Stmt} {q : ℕ} {a : Core.Atom} {c' : Ctx},
    AtS p s q (.atom a) c' → RunsS σ p s q → walk1 σ s ≠ .stuck → Ev.atom a ∈ (walk1 σ s).evs
  | p, .ite x z n, q, a, c', .zero h, hr, hw => by
      have hb := atL_range h
      simp only [RunsS] at hr
      rcases hr with rfl | ⟨h0, hr⟩ | ⟨-, hr⟩
      · omega
      · simp only [walk1, h0, ↓reduceIte] at hw ⊢
        exact evs_pre_right (runs_atom h hr (pre_ne_stuck hw))
      · have := runsL_range hr; omega
  | p, .ite x z n, q, a, c', .nonzero h, hr, hw => by
      have hb := atL_range h
      simp only [RunsS] at hr
      rcases hr with rfl | ⟨-, hr⟩ | ⟨h0, hr⟩
      · omega
      · have := runsL_range hr; omega
      · simp only [walk1, h0, ↓reduceIte] at hw ⊢
        exact evs_pre_right (runs_atom h hr (pre_ne_stuck hw))
  | p, .match_ x arms, q, a, c', .arm h, hr, hw => by
      have hb := atA_range h
      simp only [RunsS] at hr
      rcases hr with rfl | hr
      · omega
      · simp only [walk1] at hw ⊢
        exact runsA_atom h hr hw

theorem runsA_atom : ∀ {t a : ℕ} {bs : List (List Stmt)} {q : ℕ} {at' : Core.Atom} {c' : Ctx} {x : V} {j : ℕ},
    AtA t a bs q (.atom at') c' → RunsA σ x j a bs q → walkArms σ x j bs ≠ .stuck →
      Ev.atom at' ∈ (walkArms σ x j bs).evs
  | t, a, b :: bs, q, at', c', x, j, .here h, hr, hw => by
      have hb := atL_range h
      simp only [RunsA] at hr
      rcases hr with ⟨h0, hr⟩ | ⟨-, hr⟩
      · unfold walkArms at hw ⊢
        simp only [h0, ↓reduceIte] at hw ⊢
        exact runs_atom h hr hw
      · have := runsA_range hr; omega
  | t, a, b :: bs, q, at', c', x, j, .next h, hr, hw => by
      have hb := atA_range h
      simp only [RunsA] at hr
      rcases hr with ⟨-, hr⟩ | ⟨h0, hr⟩
      · have := runsL_range hr; omega
      · unfold walkArms at hw ⊢
        simp only [h0, ↓reduceIte] at hw ⊢
        exact runsA_atom h hr hw
end

/-! ## A body's values, by position -/

mutual
/-- **Every value a block names is named at a position** (its statement's own values). -/
theorem uses_at : ∀ (c : Ctx) (p : ℕ) (ss : List Stmt) {v : V}, v ∈ Stmt.usesList ss →
    ∃ q s c', AtL c p ss q s c' ∧ v ∈ names s
  | _, _, [], _, h => by simp [Stmt.usesList] at h
  | c, p, s :: ss, v, h => by
      simp only [Stmt.usesList, List.mem_append] at h
      rcases h with h | h
      · rcases usesS_at p s h with h | ⟨q, s', c', h1, h2⟩
        · exact ⟨p, s, c, .head c p s ss, h⟩
        · exact ⟨q, s', c', .inside h1, h2⟩
      · obtain ⟨q, s', c', h1, h2⟩ := uses_at c (p + size s) ss h
        exact ⟨q, s', c', .tail h1, h2⟩

theorem usesS_at : ∀ (p : ℕ) (s : Stmt) {v : V}, v ∈ Stmt.uses s →
    v ∈ names s ∨ ∃ q s' c', AtS p s q s' c' ∧ v ∈ names s'
  | p, .ite x z n, v, h => by
      simp only [Stmt.uses, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact .inl (by simp [names])
      · obtain ⟨q, s', c', h1, h2⟩ := uses_at ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z h
        exact .inr ⟨q, s', c', .zero h1, h2⟩
      · obtain ⟨q, s', c', h1, h2⟩ := uses_at ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n h
        exact .inr ⟨q, s', c', .nonzero h1, h2⟩
  | p, .match_ x arms, v, h => by
      simp only [Stmt.uses, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl (by simp [names])
      · obtain ⟨q, s', c', h1, h2⟩ := usesA_at p (p + 1) arms h
        exact .inr ⟨q, s', c', .arm h1, h2⟩
  | p, .atom _, v, h => .inl (by simpa [Stmt.uses, names] using h)
  | p, .call .., v, h => .inl (by simpa [Stmt.uses, names] using h)
  | p, .callIf .., v, h => .inl (by simpa [Stmt.uses, names] using h)
  | p, .dispatch .., v, h => .inl (by simpa [Stmt.uses, names] using h)
  | p, .ret _, v, h => .inl (by simpa [Stmt.uses, names] using h)

theorem usesA_at : ∀ (t a : ℕ) (bs : List (List Stmt)) {v : V}, v ∈ Stmt.usesArms bs →
    ∃ q s c', AtA t a bs q s c' ∧ v ∈ names s
  | _, _, [], _, h => by simp [Stmt.usesArms] at h
  | t, a, b :: bs, v, h => by
      simp only [Stmt.usesArms, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, s, c', h1, h2⟩ := uses_at ⟨a + sizeL b, t, a⟩ a b h
        exact ⟨q, s, c', .here h1, h2⟩
      · obtain ⟨q, s, c', h1, h2⟩ := usesA_at t (a + sizeL b) bs h
        exact ⟨q, s, c', .next h1, h2⟩
end

mutual
/-- **Every temporary of a block is an atom's at a position.** -/
theorem tmps_at : ∀ (c : Ctx) (p : ℕ) (ss : List Stmt) {v : V}, v ∈ Stmt.tmpsList ss →
    ∃ q a c', AtL c p ss q (.atom a) c' ∧ v ∈ atomTmps a
  | _, _, [], _, h => by simp [Stmt.tmpsList] at h
  | c, p, s :: ss, v, h => by
      simp only [Stmt.tmpsList, List.mem_append] at h
      rcases h with h | h
      · rcases tmpsS_at p s h with ⟨a, rfl, h⟩ | ⟨q, a, c', h1, h2⟩
        · exact ⟨p, a, c, .head c p _ ss, h⟩
        · exact ⟨q, a, c', .inside h1, h2⟩
      · obtain ⟨q, a, c', h1, h2⟩ := tmps_at c (p + size s) ss h
        exact ⟨q, a, c', .tail h1, h2⟩

theorem tmpsS_at : ∀ (p : ℕ) (s : Stmt) {v : V}, v ∈ Stmt.tmps s →
    (∃ a, s = .atom a ∧ v ∈ atomTmps a) ∨ ∃ q a c', AtS p s q (.atom a) c' ∧ v ∈ atomTmps a
  | p, .ite x z n, v, h => by
      simp only [Stmt.tmps, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, a, c', h1, h2⟩ := tmps_at ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z h
        exact .inr ⟨q, a, c', .zero h1, h2⟩
      · obtain ⟨q, a, c', h1, h2⟩ := tmps_at ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n h
        exact .inr ⟨q, a, c', .nonzero h1, h2⟩
  | p, .match_ x arms, v, h => by
      simp only [Stmt.tmps] at h
      obtain ⟨q, a, c', h1, h2⟩ := tmpsA_at p (p + 1) arms h
      exact .inr ⟨q, a, c', .arm h1, h2⟩
  | p, .atom a, v, h => .inl ⟨a, rfl, by simpa [Stmt.tmps] using h⟩
  | p, .call .., v, h => by simp [Stmt.tmps] at h
  | p, .callIf .., v, h => by simp [Stmt.tmps] at h
  | p, .dispatch .., v, h => by simp [Stmt.tmps] at h
  | p, .ret _, v, h => by simp [Stmt.tmps] at h

theorem tmpsA_at : ∀ (t a : ℕ) (bs : List (List Stmt)) {v : V}, v ∈ Stmt.tmpsArms bs →
    ∃ q at' c', AtA t a bs q (.atom at') c' ∧ v ∈ atomTmps at'
  | _, _, [], _, h => by simp [Stmt.tmpsArms] at h
  | t, a, b :: bs, v, h => by
      simp only [Stmt.tmpsArms, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, s, c', h1, h2⟩ := tmps_at ⟨a + sizeL b, t, a⟩ a b h
        exact ⟨q, s, c', .here h1, h2⟩
      · obtain ⟨q, s, c', h1, h2⟩ := tmpsA_at t (a + sizeL b) bs h
        exact ⟨q, s, c', .next h1, h2⟩
end

end
end LeanVM.Guest.Local
