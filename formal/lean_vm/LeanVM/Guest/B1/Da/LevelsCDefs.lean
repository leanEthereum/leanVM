/-
  LeanVM.Guest.B1.Da.LevelsCDefs

  `da_levels`, completely: the honest tree memory, and the checks the completeness proof
  evaluates.
-/

module

public import LeanVM.Guest.B1.Da.LevelsTab
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `da_levels`, completely: definitions

`treeLvl leaves l`: level `l` of the tree (`cellLevel` iterated). `TreeMem rd tree k leaves`: the
memory an honest run of `da_levels(tree, 2^k, k)` reads and writes, every level's cells at its
offset. `lvlCOk`: a level loop evaluates (`Fwd.chk`), its keccak inputs are its four loaded cells,
its only other side conditions those loads and its two stores of the pair's digest through the
next level's pointer, and its pointers are products of pure atoms. `dlCEntryOk k`: the
specialization evaluates, its side conditions its two loads of the root, its calls the guarded
level loops, every loop checked.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

/-- Level `l` of the tree over `leaves`. -/
def treeLvl (leaves : List (E × E)) (l : ℕ) : List (E × E) := cellLevel^[l] leaves

/-- **The honest memory of `da_levels` over `2^k` leaves at `tree`**: level `l`'s cells at
`tree·g^(off k l)`. -/
def TreeMem (rd : Reader) (tree : E) (k : ℕ) (leaves : List (E × E)) : Prop :=
  ∀ l ≤ k, ReadsAt rd (tree * gen ^ off k l) (pairCells (treeLvl leaves l))

/-- A load of cell `c0 + i`, `i < 4`, through `p`. -/
def isLoadVia (p : V) (c0 : ℕ) : Atom → Bool
  | .load d q i => decide (q = p) && decide (d = .n (c0 + i)) && decide (i < 4)
  | _ => false

/-- The non-store atoms of a loop's block. -/
noncomputable def lvlA' (fn : Fn) : List Atom :=
  (atomsIn (loopPre fn)).filter (fun a => decide (a ∉ storesOf 3 fn.body))

/-- The chain of a level loop's pair hash, without the stores. -/
noncomputable def lvlSp (fn : Fn) (c0 : ℕ) : ChainSpec :=
  pairSpec (.n c0) (.n (c0 + 1)) (.n (c0 + 2)) (.n (c0 + 3)) (lvlA' fn)

/-- **A level loop, evaluated.** -/
noncomputable def lvlCOk (fn : Fn) (offA offB : ℕ) : Bool :=
  let A := atomsIn (loopPre fn)
  let pa := if offA = 0 then 5 else 7
  let pb := if offA = 0 then 9 else 11
  let c0 := if offA = 0 then 10 else 12
  (chk 3 fn.body).isSome &&
  (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  canonChk ((List.range 4).map (c0 + ·)) (lvlA' fn) &&
  A.all (fun a => !needsSide a || decide (a ∈ storesOf 3 fn.body) || isLoadVia (.n pa) c0 a) &&
  decide (storesOf 3 fn.body = [.load ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 0) (.n pb) 0,
    .load ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 1) (.n pb) 1]) &&
  ptrOk (A.filter pureB) (.n pa) (.n 2) (.n 0) offA 4 &&
  ptrOk (A.filter pureB) (.n pb) (.n 2) (.n 0) offB 2 &&
  (lvlSp fn c0).check (lvlA' fn)

/-- A level loop, found and evaluated. -/
noncomputable def loopCOk (f : String) (offA offB : ℕ) : Bool :=
  match coreProgram.indexOf? f with
  | some j => lvlCOk (coreProgram.getD j default) offA offB
  | none => false

/-- The guarded call of level `lvl`'s loop `f`. -/
def lvlCall (lvl : ℕ) (f : String) : Stmt :=
  .callIf (.n (5 * lvl + 3)) f [.n (5 * lvl + 4), .n (5 * lvl + 5), .n 0]

/-- **Entry `k` of `dlTab`, evaluated.** -/
noncomputable def dlCEntryOk (k : ℕ) : Bool :=
  let e := dlTab.getD k (0, "", 0, [])
  let fn := coreProgram.getD e.2.2.1 default
  (chk 1 fn.body).isSome && (storesOf 1 fn.body).isEmpty &&
  (match splitRet fn.body with
   | some (P, _) =>
     canonChk [] (atomsIn P) &&
     (atomsIn P).all (fun a => !needsSide a ||
       isLoadAt (.n (5 * k + 1)) (.n 0) (4 * 2 ^ k - 4) a ||
       isLoadAt (.n (5 * k + 2)) (.n 0) (4 * 2 ^ k - 3) a) &&
     P.all (fun s => match s with
       | .atom _ => true
       | .callIf .. => (List.range k).any fun lvl => stmtEqb s (lvlCall lvl (e.2.2.2.getD lvl ""))
       | _ => false)
   | none => false) &&
  (List.range k).all fun lvl => loopCOk (e.2.2.2.getD lvl "") (off k lvl) (off k (lvl + 1))

end
end LeanVM.Guest.B1.Da
