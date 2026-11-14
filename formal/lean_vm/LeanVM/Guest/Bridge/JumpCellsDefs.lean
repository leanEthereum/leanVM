/-
  LeanVM.Guest.Bridge.JumpCellsDefs

  What the deployed guest's jump cells rest on beyond the honest frames: the shape of the alignment contexts, and a check of each function's data, decided by the kernel.
-/

module

public import LeanVM.Guest.Bridge.AlignDefs
public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.Renumber

/-!
# The jump cells' data

`stmtsOf body`, `condsOf body`: every statement of a body, and every condition of its branches and conditional calls, nested ones included; the checks walk a body by its recursor (`blockB`, `noRetB`), which the kernel runs fast on `main_loop2`'s. `jcDataD p n C extra fn code main`, the facts of a function's data the jump cells need (`Bridge/JumpCells.lean`), decided by the kernel for every function on its own data (`Bridge/JumpCells/`, by `scripts/bridge-cert/align.py`):

- its fixed cells (`Plumb.stat`) and table jump targets (`armsOf`) in `[2, n)`, its constants below `2^64`;
- its call sites' callee frame cells and dispatch targets in `[2, n)`, no two sites of one argument and return list;
- its hint-only cells' values without a certificate cell; each branch's and conditional call's condition at a certificate cell in `[2, n)`, its number below `2^30`, each `match` selector a numbered value;
- a loop helper's body `pre ++ [callIf c f args, ret []]`, `pre` without `ret`, no site of the final call's arguments; `main` no loop helper;
- each jump's frame cell, if a next frame `fp·g^S`, `S ≠ 0`, only in a loop helper with `S = n`;
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B2C

@[expose] public section

mutual
/-- Every statement of a block, nested ones included. -/
def stmtsOf : List Stmt → List Stmt
  | [] => []
  | s :: ss => s :: (stmtsSub s ++ stmtsOf ss)

/-- The statements nested in a statement. -/
def stmtsSub : Stmt → List Stmt
  | .ite _ z n => stmtsOf z ++ stmtsOf n
  | .match_ _ arms => stmtsArms arms
  | _ => []

/-- The statements of arms. -/
def stmtsArms : List (List Stmt) → List Stmt
  | [] => []
  | a :: as => stmtsOf a ++ stmtsArms as
end

mutual
/-- The conditions of a block's branches and conditional calls, nested ones included. -/
def condsOf : List Stmt → List V
  | [] => []
  | s :: ss => condsSub s ++ condsOf ss

/-- A statement's conditions. -/
def condsSub : Stmt → List V
  | .ite c z n => c :: (condsOf z ++ condsOf n)
  | .match_ _ arms => condsArms arms
  | .callIf c _ _ => [c]
  | _ => []

/-- The conditions of arms. -/
def condsArms : List (List Stmt) → List V
  | [] => []
  | a :: as => condsOf a ++ condsArms as
end

/-- A cell in `[2, n)`. -/
def cellIn (n o : ℕ) : Bool := Nat.ble 2 o && Nat.blt o n

/-- No two sites of one argument and return list. -/
def sitesUniq : List Site → Bool
  | [] => true
  | s :: ss => ss.all (fun s' ↦ !(s'.args == s.args && s'.rets == s.rets)) && sitesUniq ss

/-- No `ret` in a block, nested ones included: by the recursor, for the kernel. -/
noncomputable def noRetB : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- A loop helper's shape: `pre ++ [callIf c f args, ret []]`, `pre` without `ret`, no site of the
final call's arguments. -/
noncomputable def loopChk (fn : Fn) (p : Plumb) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ _ args :: rpre =>
      noRetB rpre.reverse && p.sites.all fun s ↦ !(s.args == args.map (·.idx) && s.rets == [])
  | _ => false

/-- A jump's frame cell `q`, if a next frame `fp·g^S`, `S ≠ 0`: only in a loop helper, `S = n`. -/
def nextChk (p : Plumb) (n : ℕ) (loop : Bool) (q : ℕ) : Bool :=
  p.stat.all fun st ↦ !(st.1 == q) || match st.2 with
    | .fpg S => S == 0 || (loop && S == n)
    | _ => true

/-- A numbered value, `V.n v.idx`. -/
def numbered (v : V) : Bool := v.path.isEmpty && Nat.beq v.tag 0

/-- A statement's conditions pass `cOk`, its `match` selectors are numbered, nested ones included:
by the recursor, for the kernel. -/
noncomputable def stmtB (cOk : V → Bool) : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun c _ _ hz hn ↦ cOk c && hz && hn) (fun x _ ha ↦ numbered x && ha)
    (fun _ _ _ ↦ true) (fun c _ _ ↦ cOk c) (fun _ _ _ _ ↦ true) (fun _ ↦ true)
    true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- `stmtB` of a block. -/
noncomputable def blockB (cOk : V → Bool) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun c _ _ hz hn ↦ cOk c && hz && hn) (fun x _ ha ↦ numbered x && ha)
    (fun _ _ _ ↦ true) (fun c _ _ ↦ cOk c) (fun _ _ _ _ ↦ true) (fun _ ↦ true)
    true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- `stmtB` of arms. -/
noncomputable def armsB (cOk : V → Bool) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun c _ _ hz hn ↦ cOk c && hz && hn) (fun x _ ha ↦ numbered x && ha)
    (fun _ _ _ ↦ true) (fun c _ _ ↦ cOk c) (fun _ _ _ _ ↦ true) (fun _ ↦ true)
    true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- The window of value `i`: the last whose first value is at most `i`. -/
def winOf (los : List ℕ) (i : ℕ) : ℕ := (los.takeWhile (fun lo ↦ Nat.ble lo i)).length - 1

/-- The certificate cell of value `i`, read in its window of `C`. -/
noncomputable def cellW (C : Check.Cert) (i : ℕ) : Option ℕ :=
  bif Nat.ble (winOf C.los i) C.cuts.length && Nat.ble (listElementOrDefault C.los (winOf C.los i) 0) i then
    (listElementOrDefault C.cells (winOf C.los i) [])[i - listElementOrDefault C.los (winOf C.los i) 0]?
  else none

/-- A condition's certificate cell in `[2, n)`, its number below `2^30`. -/
noncomputable def condOk (C : Check.Cert) (n : ℕ) (c : V) : Bool :=
  Nat.blt c.idx (2 ^ 30) && match cellW C c.idx with
    | some x => cellIn n x
    | none => false

/-- The hint-only cells' values have no certificate cell (below `2`). -/
noncomputable def extraOk (C : Check.Cert) (extra : List (ℕ × ℕ)) : Bool :=
  extra.all fun p ↦ match cellW C p.1 with
    | some x => Nat.blt x 2
    | none => false

/-- **The facts of a function's data the jump cells need**: its `Plumb` `p`, frame size `n`,
certificate `C`, hint-only cells `extra`, core IR, code, and whether it is `main`. -/
noncomputable def jcDataD (p : Plumb) (n : ℕ) (C : Check.Cert) (extra : List (ℕ × ℕ)) (fn : Fn)
    (code : List OffsetInstruction) (main : Bool) : Bool :=
  p.stat.all (fun q ↦ cellIn n q.1 && match q.2 with
    | .k a b => Nat.blt a (2 ^ 64) && Nat.blt b (2 ^ 64)
    | .fpg _ => true) &&
  (armsOf p).all (fun a ↦ cellIn n a.1) &&
  p.sites.all (fun s ↦ cellIn n s.q && (s.tgt == 0 || cellIn n s.tgt)) &&
  sitesUniq p.sites &&
  extraOk C extra &&
  blockB (condOk C n) fn.body &&
  (!fn.loop || (!main && loopChk fn p)) &&
  (p.stat.all (fun q ↦ match q.2 with
    | .fpg S => S == 0 || (fn.loop && S == n)
    | _ => true) || code.all (fun
    | .jump _ _ q => nextChk p n fn.loop q
    | _ => true))

end

end LeanVM.Guest.Bridge
