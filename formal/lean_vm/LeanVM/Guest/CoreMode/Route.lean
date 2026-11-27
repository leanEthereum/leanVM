/-
  LeanVM.Guest.CoreMode.Route

  What ties a function's core data to the deployed guest's tables, so that the tree track's honest
  frames give its honest valuations.
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.CoreResG
public import LeanVM.Guest.CoreMode.LoopBC
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# Core data of the deployed guest

`CfOk Cf`: `Cf` is compiled function `j`'s: its entry, its core function (`coreOf j`), its
alignment's context (`Bridge.ctxOf j`), and its frame holds its values where the tree track's
honest frames have them (`honB`): its body the core route's shape, its parameters `V.n k` at cells `2 + k`, its returned values at
their cells, each dereferenced pointer at its certificate cell within the frame, no hint-only cell; not the prologue;
and its heap certificate's residuals of the families the honest frames make true (`resOk`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- A dereferenced pointer (`ptrOf`) at its certificate cell, within the frame, not a hint-only value. -/
noncomputable def ptrCellB (j : ℕ) : Stmt → Bool
  | .atom a => match ptrOf a with
    | some p => ((Bridge.extraOf j).lookup p.idx).isNone && decide (p.idx < 2 ^ 30) &&
      decide (2 ≤ B2C.cellJ j p) && decide (B2C.cellJ j p < B2C.fsN j)
    | none => true
  | _ => true

/-- A frame run's first value at its certificate cell, not a hint-only value. -/
noncomputable def faCellB (j : ℕ) : Stmt → Bool
  | .atom (.frameAddr _ (r :: _)) => ((Bridge.extraOf j).lookup r.idx).isNone && decide (r.idx < 2 ^ 30)
  | _ => true

/-- Where frame run cells are guaranteed (`faNeed`), the frame runs' first values at their cells (`HonB.fa`). -/
noncomputable def faOkB (j : ℕ) (Cf : CFun) : Bool := !faNeed Cf || stmtsAll (faCellB j) Cf.fn.body

/-- A `ret`'s values at their certificate cells, within the frame, not hint-only values. -/
noncomputable def retCellB (j : ℕ) : Stmt → Bool
  | .ret vs => vs.all fun v ↦ ((Bridge.extraOf j).lookup v.idx).isNone && decide (v.idx < 2 ^ 30) &&
      decide (2 ≤ B2C.cellJ j v) && decide (B2C.cellJ j v < B2C.fsN j)
  | _ => true

/-- A value at its certificate cell within the frame, not a hint-only value. -/
noncomputable def cellB (j : ℕ) (v : V) : Bool :=
  ((Bridge.extraOf j).lookup v.idx).isNone && decide (v.idx < 2 ^ 30) && decide (2 ≤ B2C.cellJ j v) &&
    decide (B2C.cellJ j v < B2C.fsN j)

/-- No `match` among the statements. -/
def noMatch (l : List Stmt) : Bool :=
  l.all fun s ↦ match s with
    | .match_ .. => false
    | _ => true

/-- No `dispatch` among the statements. -/
def noDsp (l : List Stmt) : Bool :=
  l.all fun s ↦ match s with
    | .dispatch .. => false
    | _ => true

/-- Statement `s` is the atom `b`. -/
def isAtom (b : Atom) : Stmt → Bool
  | .atom a => decide (a = b)
  | _ => false

/-- Atom `b` is once among the statements of `B`, nested ones included. -/
def onceB (B : List Stmt) (b : Atom) : Bool := Nat.beq ((Bridge.stmtsOf B).countP (isAtom b)) 1

/-- A top-level atom of `ss` that is once among the statements of `B`. -/
def onceAfter (B ss : List Stmt) : Bool :=
  ss.any fun s ↦ match s with
    | .atom b => onceB B b
    | _ => false

/-- **The `match`es of a branch of a top-level `ite`**, `B` the body: at the branch's top level, each on a
selector at its cell used by a top-level atom before it (`seen`, the body's then the branch's), no `match`
in its arms, and a top-level atom after it in the branch once in `B` (a path through the other branch walks
none of its events). -/
noncomputable def selBr (j : ℕ) (B : List Stmt) : List Atom → List Stmt → Bool
  | _, [] => true
  | seen, .atom a :: ss => selBr j B (a :: seen) ss
  | seen, .match_ x arms :: ss => cellB j x && seen.any (fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      noMatch (Bridge.stmtsArms arms) && onceAfter B ss && selBr j B seen ss
  | seen, .ite _ z n :: ss => noMatch (Bridge.stmtsOf z) && noMatch (Bridge.stmtsOf n) && selBr j B seen ss
  | seen, .ret _ :: ss => selBr j B seen ss
  | seen, .call .. :: ss => selBr j B seen ss
  | seen, .callIf .. :: ss => selBr j B seen ss
  | seen, .dispatch .. :: ss => selBr j B seen ss

/-- **Each `match` and `dispatch` of a body at its top level, or a `match` at the top level of a top-level
`ite`'s branch** (`selBr`), `B` the body: its selector used by a top-level atom before it (`seen`; a
dispatch's, or a parameter of `ps`) and at its certificate cell; no other `match` nested, none past a `ret`. -/
noncomputable def selGo (j : ℕ) (ps : List V) (B : List Stmt) : List Atom → List Stmt → Bool
  | _, [] => true
  | seen, .atom a :: ss => selGo j ps B (a :: seen) ss
  | seen, .match_ x arms :: ss => cellB j x && seen.any (fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      noMatch (Bridge.stmtsArms arms) && selGo j ps B seen ss
  | seen, .ite _ z n :: ss => selBr j B seen z && selBr j B seen n && selGo j ps B seen ss
  | _, .ret _ :: ss => noMatch (Bridge.stmtsOf ss) && noDsp (Bridge.stmtsOf ss)
  | seen, .call .. :: ss => selGo j ps B seen ss
  | seen, .callIf .. :: ss => selGo j ps B seen ss
  | seen, .dispatch x .. :: ss => cellB j x && (ps.contains x || seen.any fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      selGo j ps B seen ss

/-- Function `j`'s frame holds `fn`'s parameters at cells `2 + k` and its pointers and returned values
at their cells; `j` not the prologue. -/
noncomputable def honB (j : ℕ) (fn : Fn) : Bool :=
  (certOf j).locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) && (bodyCore fn.body || loopBC fn) &&
    stmtsAll (ptrCellB j) fn.body && paramsN fn.params 0 &&
    ((List.range fn.params.length).all fun k ↦ Nat.beq (B2C.cellJ j (V.n k)) (2 + k) && decide (2 + k < B2C.fsN j)) &&
    stmtsAll (retCellB j) fn.body && Nat.blt 0 j &&
    (selGo j fn.params fn.body [] fn.body || loopBC fn)

/-- `honB` but for its passes over the body (`bodyCore`, `ptrCellB`, `retCellB`, `selGo`), which a long body
checks apart. -/
noncomputable def honRest (j : ℕ) (fn : Fn) : Bool :=
  (certOf j).locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) && paramsN fn.params 0 &&
    ((List.range fn.params.length).all fun k ↦ Nat.beq (B2C.cellJ j (V.n k)) (2 + k) && decide (2 + k < B2C.fsN j)) &&
    Nat.blt 0 j

theorem honB_of {j : ℕ} {fn : Fn} (h1 : (bodyCore fn.body || loopBC fn) = true)
    (h2 : (Bridge.stmtsOf fn.body).all (ptrCellB j) = true) (h3 : (Bridge.stmtsOf fn.body).all (retCellB j) = true)
    (h4 : (selGo j fn.params fn.body [] fn.body || loopBC fn) = true) (h5 : honRest j fn = true) : honB j fn = true := by
  simp only [honRest, Bool.and_eq_true] at h5
  obtain ⟨⟨⟨r1, r2⟩, r3⟩, r4⟩ := h5
  simp only [honB, stmtsAll_eq, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨r1, h1⟩, h2⟩, r2⟩, r3⟩, h3⟩, r4⟩, h4⟩

/-- **Core data of the deployed guest's function `j`.** -/
def CfOk (Cf : CFun) : Prop :=
  ∃ j, j < nFns ∧ (fnOf j).entryPc = Cf.frame.entry ∧ coreOf j = Cf.fn ∧ Bridge.ctxOf j = Cf.X ∧
    (honB j Cf.fn && resOk Cf && glOk Cf && faOkB j Cf) = true


/-- **Core data of the deployed guest**, from the tables' entries of function `j` and its checks. -/
theorem cfOk_of {j : ℕ} {f : CompiledFunction} {cf : Fn} {C : Check.Cert} {P : B2C.Plumb} {ex : List (ℕ × ℕ)}
    {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {Cf : CFun} (hj : j < nFns)
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (Bridge.extraOf j, Bridge.entsOf j, Bridge.adviceOf j) = (ex, en, d)) (he : f.entryPc = Cf.frame.entry)
    (hfn : cf = Cf.fn)
    (hX : Bridge.AlignCtx.ofData C.locs ex f.entryPc (j == 1) P Data.powTree Data.jtTrie en Bridge.alignHalt
      f.instructionCount = Cf.X)
    (hb : (honB j Cf.fn && resOk Cf && glOk Cf && faOkB j Cf) = true) : CfOk Cf := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, -⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  refine ⟨j, hj, by rw [hf, he], by rw [hcf, hfn], ?_, hb⟩
  rw [← hX, Bridge.ctxOf, hl, hex, hen, hf, hP]

/-- `cfOk_of` from the tables at `j` as one fact (the glue's `Fn.«k».tie`, so the route names a function by its
key, its index only in the glue). -/
theorem cfOk_of_tie {j : ℕ} {f : CompiledFunction} {cf : Fn} {C : Check.Cert} {P : B2C.Plumb} {ex : List (ℕ × ℕ)}
    {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {Cf : CFun} (hj : j < nFns)
    (ht : fnOf j = f ∧ coreOf j = cf ∧ certOf j = C.withPows Data.powTree ∧ B2C.plumbOf j = P ∧
      (Bridge.extraOf j, Bridge.entsOf j, Bridge.adviceOf j) = (ex, en, d)) (he : f.entryPc = Cf.frame.entry)
    (hfn : cf = Cf.fn)
    (hX : Bridge.AlignCtx.ofData C.locs ex f.entryPc (j == 1) P Data.powTree Data.jtTrie en Bridge.alignHalt
      f.instructionCount = Cf.X)
    (hb : (honB j Cf.fn && resOk Cf && glOk Cf && faOkB j Cf) = true) : CfOk Cf :=
  cfOk_of hj ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 he hfn hX hb

end

end LeanVM.Guest.CoreMode
