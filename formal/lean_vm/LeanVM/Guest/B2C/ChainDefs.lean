/-
  LeanVM.Guest.B2C.ChainDefs

  The chained `match`es' static check (`B2C/Chain.lean` proves it sound), apart from the proofs
  so that its kernel family (`B2C/Chained/`) imports only what it evaluates.
-/

module

public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.B2C.Share
public import LeanVM.Guest.Memory.Fresh

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-! ## The check -/

/-- A chain `(p, x, ts, y, b)`. -/
abbrev Chain := ℕ × ℕ × List ℕ × ℕ × ℕ

/-- The chains in increasing statement order, each one's targets apart from the earlier ones'. -/
def chainsPw : List Chain → Bool
  | [] => true
  | ch :: rest => rest.all (fun ch' ↦ Nat.blt ch.1 ch'.1 &&
      ch'.2.2.1.all (fun t ↦ !(bitsOf ch.2.2.1).testBit t)) && chainsPw rest

/-- The fixed, temporaries', runs', call sites' and `match` targets' cells of function `j`. -/
noncomputable def fixedBits (j : ℕ) : ℕ :=
  bitsOf ((plumbOf j).stat.map Prod.fst ++ (plumbOf j).tmps.map Prod.snd ++
    (plumbOf j).runs.map Prod.snd ++ siteCells (plumbOf j) ++ (plumbOf j).arms.map (·.2.1))

/-- **The chains' static check of function `j`.** -/
noncomputable def chainFn (j : ℕ) : Bool :=
  chainsPw (plumbOf j).chains &&
  (plumbOf j).chains.all fun ch ↦
    ch.2.2.1.all (fun t ↦ !(fixedBits j).testBit t) && Nat.ble ch.2.2.1.length 65536 &&
    match (coreOf j).body[ch.1]?, (coreOf j).body[ch.1 + 1]? with
    | some (.match_ x arms), some (.match_ y arms') =>
      decide (x = V.n ch.2.1) && decide (y = V.n ch.2.2.2.1) && Nat.beq arms.length ch.2.2.1.length &&
        (List.range arms'.length).all fun e ↦ (glob.jt.get (ch.2.2.2.2 + e)).isSome
    | _, _ => false

/-- The values `vs` have cells in `loc`, none in the bits `F`. -/
def avoidL (loc : CLoc) (F : ℕ) (vs : List V) : Bool :=
  vs.all fun v ↦ match loc.get? v.idx with
    | some c => !F.testBit c
    | none => false

/-- The values `vs` of an arm of target `t` have cells in `loc`, none in the bits `F` but among
the arm's own chain's targets `own`, and none at `t`. -/
def avoidA (loc : CLoc) (F own t : ℕ) (vs : List V) : Bool :=
  vs.all fun v ↦ match loc.get? v.idx with
    | some c => !F.testBit c || (own.testBit c && decide (c ≠ t))
    | none => false

/-- Each arm's values apart from its target. -/
def chainArms (loc : CLoc) (F own : ℕ) : List (List Stmt) → List ℕ → Bool
  | [], [] => true
  | a :: as, t :: ts => avoidA loc F own t (Stmt.usesList a) && chainArms loc F own as ts
  | _, _ => false

/-- Top-level statement `s`'s values: apart from every target (`F`), or, the chained `match` of a
chain, its selector apart from every target and each arm's values apart from its target. -/
def chainStmt (chs : List Chain) (loc : CLoc) (F s : ℕ) (st : Stmt) : Bool :=
  match chs.find? (fun ch ↦ Nat.beq ch.1 s) with
  | none => avoidL loc F (Stmt.uses st)
  | some ch => match st with
    | .match_ x arms => decide (x = V.n ch.2.1) && avoidL loc F [x] &&
        chainArms loc F (bitsOf ch.2.2.1) arms ch.2.2.1
    | _ => false

/-- The statements from `s` on. -/
def chainStmts (chs : List Chain) (loc : CLoc) (F : ℕ) : ℕ → List Stmt → Bool
  | _, [] => true
  | s, st :: ss => chainStmt chs loc F s st && chainStmts chs loc F (s + 1) ss

/-- **The chains' check of window `i` of function `j`.** -/
noncomputable def chainWin (j i : ℕ) : Bool :=
  (plumbOf j).chains.isEmpty ||
  ((listElementOrDefault (certOf j).cells i []).all (fun c ↦ Nat.blt c 65536) &&
    natSeq (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))) fun F ↦ (clocW (certOf j) i).seq fun loc ↦
      (bif Nat.beq i 0 then avoidL loc F (coreOf j).params else true) &&
      chainStmts (plumbOf j).chains loc F ((certOf j).cutAt i).start ((certOf j).stmtsAt (coreOf j) i))

/-- **The chains' checks of function `j`.** -/
def ChainOk (j : ℕ) : Prop := chainFn j = true ∧ ∀ i ≤ (certOf j).cuts.length, chainWin j i = true

/-- A function without chains passes. -/
theorem chainOk_of_nil {j : ℕ} (h : (plumbOf j).chains.isEmpty = true) : ChainOk j := by
  have h' : (plumbOf j).chains = [] := List.isEmpty_iff.mp h
  refine ⟨?_, fun i _ ↦ ?_⟩
  · simp [chainFn, h', chainsPw]
  · simp [chainWin, h']

end
end LeanVM.Guest.B2C
