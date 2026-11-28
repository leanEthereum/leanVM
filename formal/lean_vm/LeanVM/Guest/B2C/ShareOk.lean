/-
  LeanVM.Guest.B2C.ShareOk

  What the sharing check gives of a compiled function: one word per cell on every returning
  path, its values' cells, its lists of temporaries and frame runs, its cells apart.
-/

module

public import LeanVM.Guest.B2C.ShareFacts
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.CheckWinC

/-!
# What the sharing check gives

`ShareOk j` is the structure of what the completeness proofs read of function `j`'s sharing
check (`B2C/ShareL.lean`, linked by `B2C/ShareLink.lean`): on every returning path a word per
cell that every value the path names holds, a fixed cell's constant (`path`); each value's cell in
the frame or a tail call's next frame, in no fixed frame pointer's cell nor another temporary's
(`vals`, `param`); its temporaries and frame runs listed (`static`, `FnStatic`); its fixed cells,
temporaries, runs, call sites and table targets apart (`apart`, `Apart`); its lists in the frame
(`lists`). The lemmas below state each part as the proofs use it.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-- **The cells apart**: the fixed cells from the temporaries', the call sites' and the table
targets' from the temporaries', the runs', the fixed cells and every value's, the table targets'
from the sites', the fixed cells, the sites and the targets each once, the entry environment's
cells fixed frame pointer cells; in `main`, all below the jump table. -/
structure Apart (j : ℕ) : Prop where
  statTmp : ∀ q ∈ (plumbOf j).stat, ∀ p ∈ (plumbOf j).tmps, p.2 ≠ q.1
  site : ∀ c ∈ siteCells (plumbOf j), (∀ p ∈ (plumbOf j).tmps, p.2 ≠ c) ∧ (∀ p ∈ (plumbOf j).runs, p.2 ≠ c) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 ≠ c) ∧ c ∉ (certOf j).locs
  arm : ∀ a ∈ (plumbOf j).arms, (∀ p ∈ (plumbOf j).tmps, p.2 ≠ a.2.1) ∧ (∀ p ∈ (plumbOf j).runs, p.2 ≠ a.2.1) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 ≠ a.2.1) ∧ a.2.1 ∉ (certOf j).locs ∧ a.2.1 ∉ siteCells (plumbOf j)
  statNodup : ((plumbOf j).stat.map Prod.fst).Nodup
  siteNodup : (siteCells (plumbOf j)).Nodup
  armNodup : ((plumbOf j).arms.map fun a ↦ a.2.1).Nodup
  env : ∀ p ∈ (certOf j).facts.env, (p.1, PC.fpg 0) ∈ (plumbOf j).stat
  main : j = 1 → (∀ p ∈ (plumbOf j).tmps, p.2 < Data.mainCells) ∧ (∀ p ∈ (plumbOf j).runs, p.2 < Data.mainCells) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 < Data.mainCells) ∧ (∀ c ∈ (certOf j).locs, c < Data.mainCells) ∧
    (∀ c ∈ siteCells (plumbOf j), c < Data.mainCells) ∧ ∀ a ∈ (plumbOf j).arms, a.2.1 < Data.mainCells

/-- **What the sharing check gives statically** of function `j`: its temporaries and runs as
listed, the lists one value per cell in the frame, runs apart from temporaries. -/
structure FnStatic (j : ℕ) : Prop where
  tmp : ∀ t ∈ Stmt.tmpsList (coreOf j).body, t = V.n t.idx ∧ (t.idx, cellJ j t) ∈ (plumbOf j).tmps
  tmpsIn : ∀ p ∈ (plumbOf j).tmps, 2 ≤ p.2 ∧ p.2 < fsN j
  tmpsFun : ∀ p ∈ (plumbOf j).tmps, ∀ q ∈ (plumbOf j).tmps, p.2 = q.2 → p.1 = q.1
  run : ∀ p r rs, Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf j).body → ∀ (k : ℕ)
    (hk : k < (r :: rs).length), (r :: rs)[k] = V.n (r :: rs)[k].idx ∧
      cellJ j (r :: rs)[k] = cellJ j r + k ∧ ((r :: rs)[k].idx, cellJ j r + k) ∈ (plumbOf j).runs
  runsIn : ∀ p ∈ (plumbOf j).runs, 2 ≤ p.2 ∧ p.2 < fsN j
  runsFun : ∀ p ∈ (plumbOf j).runs, ∀ q ∈ (plumbOf j).runs, p.2 = q.2 → p.1 = q.1
  runsTmp : ∀ p ∈ (plumbOf j).runs, ∀ q ∈ (plumbOf j).tmps, q.2 ≠ p.2

/-- **What the sharing check gives of function `j`.** -/
structure ShareOk (j : ℕ) : Prop where
  /-- On a returning path, a word per cell: every value the path names holds its cell's, a fixed
  cell holds its constant. -/
  path : ∀ {rd : Reader} {σ : Val} {es : List Ev} {vs : List V}, walk σ (coreOf j).body = .ret es vs →
    (∀ e ∈ es, e.Holds rd σ) → ∃ Ψ : ℕ → E,
      (∀ v ∈ (coreOf j).params ++ es.flatMap Ev.uses ++ vs, 2 ≤ cellJ j v → σ v = Ψ (cellJ j v)) ∧
      ∀ o a b, (o, PC.k a b) ∈ (plumbOf j).stat → Ψ o = OffsetInstruction.immediateWord a b
  /-- Each value's cell. -/
  vals : ∀ v ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++ Stmt.tmpsList (coreOf j).body,
    v = V.n v.idx ∧ (cellJ j v < fsN j ∨ cellJ j v ∈ nextCells (certOf j).locs (fsN j) (tailArgs (coreOf j))) ∧
    bitN (fpgCells (plumbOf j)) (cellJ j v) = false ∧
    (bitN (tmpCells (plumbOf j)) (cellJ j v) = false ∨ (v.idx, cellJ j v) ∈ (plumbOf j).tmps)
  /-- The parameters' cells are in the frame. -/
  param : ∀ v ∈ (coreOf j).params, cellJ j v < fsN j
  static : FnStatic j
  apart : Apart j
  lists : listsOk (plumbOf j) (fsN j) = true

variable {j : ℕ}

/-- **The sharing check's conclusion on a path** of function `j` that returns: one word per cell
for every value the path names, a fixed cell's constant. -/
theorem shareOk_path (hS : ShareOk j)
    {rd : Reader} {σ : Val} {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs)
    (he : ∀ e ∈ es, e.Holds rd σ) : ∃ Ψ : ℕ → E, (∀ v ∈ (coreOf j).params ++ es.flatMap Ev.uses ++ vs,
      2 ≤ cellJ j v → σ v = Ψ (cellJ j v)) ∧
      ∀ o a b, (o, PC.k a b) ∈ (plumbOf j).stat → Ψ o = OffsetInstruction.immediateWord a b :=
  hS.path hw he

theorem apart_j (hS : ShareOk j) : Apart j := hS.apart

theorem fnStatic (hS : ShareOk j) : FnStatic j :=
  hS.static

/-- **A value's cell**: in the frame, or a tail call's argument at the next frame's parameter
cell. -/
theorem valOk_global (hS : ShareOk j) {v : V}
    (hv : v ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++ Stmt.tmpsList (coreOf j).body) :
    v = V.n v.idx ∧
      (cellJ j v < fsN j ∨ cellJ j v ∈ nextCells (certOf j).locs (fsN j) (tailArgs (coreOf j))) ∧
      bitN (fpgCells (plumbOf j)) (cellJ j v) = false ∧
      (bitN (tmpCells (plumbOf j)) (cellJ j v) = false ∨ (v.idx, cellJ j v) ∈ (plumbOf j).tmps) :=
  hS.vals v hv

/-- **A parameter's cell is in the frame.** -/
theorem valOk_param (hS : ShareOk j) {v : V}
    (hv : v ∈ (coreOf j).params) : cellJ j v < fsN j :=
  hS.param v hv

/-- The fixed cells lie in the frame. -/
theorem stat_in (hS : ShareOk j) {q : ℕ × PC} (hq : q ∈ (plumbOf j).stat) : 2 ≤ q.1 ∧ q.1 < fsN j := by
  have hlists := hS.lists
  simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
  have := (hlists.1.1.1.1.1 q hq).1
  simp only [Nat.ble_eq, Nat.blt_eq] at this
  exact this

end
end LeanVM.Guest.B2C
