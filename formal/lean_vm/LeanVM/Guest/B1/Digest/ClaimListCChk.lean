/-
  LeanVM.Guest.B1.Digest.ClaimListCChk

  `claim_list_digest`'s branches and its group loop `__loop16`, evaluated (by kernel evaluation), for its
  completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `claim_list_digest`, evaluated

`grpcOk`: a frame loop's block (`__loop16` here, the big `__loop15` in `ClaimListCBig`) evaluates
in order (`Fwd.chk`), its atoms are `loopAtoms`, its stores write the chain's last state at `.n 9`
from offset `13`, its side conditions are its loads. `clBrOk`: each branch of
`claim_list_digest`, its values padded by hints up to the final copies (`fillH`), evaluates in
order; the nonempty branch's stores are the zero state's, its other atoms need nothing.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A load through `.n p` at an offset below `bound`. -/
def isLoadBelow (p bound : ℕ) : Atom → Bool
  | .load _ q o => decide (q = .n p) && decide (o < bound)
  | _ => false

/-- A statement is an atom. -/
def isAtomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- Atom lists compared, words limb by limb. -/
def atomsEqbL : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => atomEqb x y && atomsEqbL xs ys
  | _, _ => false

theorem atomsEqbL_sound : ∀ {xs ys : List Atom}, atomsEqbL xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [atomsEqbL] at h
  | _ :: _, [], h => by simp [atomsEqbL] at h
  | x :: xs, y :: ys, h => by
    simp only [atomsEqbL, Bool.and_eq_true] at h
    rw [atomEqb_sound h.1, atomsEqbL_sound h.2]

/-- Hints defining the values `.n c`, …, `.n (m - 1)`. -/
def fillH (c m : ℕ) : List Stmt := (List.range (m - c)).map fun i => .atom (.hint (.alloc (.n (c + i)) 0))

/-- **`claim_list_last__L{k}`, evaluated**: in order, no store, its side conditions its loads. -/
def clcOk (k : ℕ) (f : Fn) : Bool :=
  (chk 2 f.body).isSome && (storesOf 2 f.body).isEmpty &&
  match splitBody f.body with
  | some (atoms, _) =>
    atoms.all (fun a => !needsSide a || isLoadBelow 0 13 a || isLoadBelow 1 (4 * k) a)
  | none => false

/-- **A frame loop of `m` claims, evaluated** (`grpOk`'s loop): in order, its atoms `loopAtoms`, its
stores the next state's cells at `.n 9` from offset `13`, its other side conditions the loads of the
state and the cells (`.n c0 …` through `.n ep`), its offsets and pointers products of pure atoms. -/
def grpcOk (fn : Fn) (f : String) (m c0 st0 ep : ℕ) : Bool :=
  let A := loopAtoms fn
  let S := storesOf 4 fn.body
  let F := A.filter fun a => decide (a ∉ S)
  loopShapeF fn f && (chk 4 fn.body).isSome && (loopPre fn).all isAtomS &&
  atomsEqbL (atomsIn (loopPre fn)) A &&
  S.all (fun a => (List.range 13).any fun c =>
    atomEqb a (.load ((grpSpec m c0 st0 A).outV ((grpSpec m c0 st0 A).nb - 1) c) (.n 9) (13 + c))) &&
  A.all (fun a => !needsSide a || decide (a ∈ S) || isLoadBelow 9 13 a || isLoadBelow ep (4 * m) a) &&
  stLoadsOk F (.n 9) (grpSt st0) 0 &&
  monoIs (A.filter pureB) (.n 9) (.n 2) (.n 0) 13 && monoIs (A.filter pureB) (.n ep) (.n 3) (.n 0) (4 * m)

/-- The nonempty branch but its two final copies. -/
noncomputable def clElsePre : List Stmt := cl23Else.dropLast.dropLast

/-- The head of `claim_list_digest`'s body. -/
def clHead : List Stmt := [.atom (.const (.n 2) (word 1 0)), .atom (.add (.n 3) (.n 1) (.n 2))]

/-- The final copies of `claim_list_digest`. -/
def clTail : List Stmt := [.atom (.copy (.n 76) (.n 10)), .atom (.copy (.n 77) (.n 11))]

/-- The empty list's run, evaluated. -/
noncomputable def clZEval : List Stmt :=
  clHead ++ cl23Zero ++ fillH ((chk 2 (clHead ++ cl23Zero)).getD 0) 76 ++ clTail

/-- The nonempty list's run, evaluated: the empty branch's values hinted (the digest at `.n 10`,
`.n 11`). -/
noncomputable def clEEval : List Stmt := clHead ++ fillH 4 12 ++ clElsePre ++ clTail

/-- `list_split`'s call in `claim_list_digest`. -/
def clSplitS : Stmt := .call "list_split" [.n 1] [.n 12, .n 13, .n 14]

/-- The big frames' loop call. -/
def clBigS : Stmt := .callIf (.n 38) "__loop15" [.n 39, .n 12, .n 23, .n 0]

/-- The groups' loop call. -/
def clGrpS : Stmt := .callIf (.n 58) "__loop16" [.n 59, .n 13, .n 45, .n 56]

/-- The dispatch on the rest. -/
def clDispS : Stmt := .dispatch (.n 14) clNames [.n 65, .n 73] [.n 74, .n 75]

/-- **`claim_list_digest`'s branches, evaluated.** -/
noncomputable def clBrOk : Bool :=
  let SE := storesOf 2 clEEval
  stmtsEqb cl23Else (clElsePre ++ [.atom (.copy (.n 10) (.n 74)), .atom (.copy (.n 11) (.n 75))]) &&
  (chk 2 clEEval).isSome &&
  SE.all (fun a => (List.range 13).any fun c => atomEqb a (.load (.n (24 + c)) (.n 23) c)) &&
  (atomsIn clEEval).all (fun a => !needsSide a || decide (a ∈ SE)) &&
  clElsePre.all (fun s => isAtomS s || stmtEqb s clSplitS || stmtEqb s clBigS || stmtEqb s clGrpS ||
    stmtEqb s clDispS) &&
  clElsePre.any (stmtEqb · clSplitS) && clElsePre.any (stmtEqb · clBigS) &&
  clElsePre.any (stmtEqb · clGrpS) && clElsePre.any (stmtEqb · clDispS) &&
  (List.range 13).all (fun c => (atomsIn clElsePre).any (isConstAt (.n (24 + c)) 0 0)) &&
  (atomsIn clElsePre).any (fun a => match a with
    | .hint (.allocDyn d _) => decide (d = .n 23)
    | _ => false) &&
  (chk 2 clZEval).isSome && (storesOf 2 clZEval).isEmpty &&
  (atomsIn clZEval).all (fun a => !needsSide a) && cl23Zero.all isAtomS

set_option maxRecDepth 100000 in
theorem clbr_ok : clBrOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem grpc_ok : grpcOk (coreProgram.getD 347 default) "__loop16" 17 18 86 17 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clc_lo : ∀ k < 9, clcOk k (coreProgram.getD (348 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clc_hi : ∀ k < 8, clcOk (9 + k) (coreProgram.getD (357 + k) default) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
