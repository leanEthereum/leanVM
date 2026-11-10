/-
  LeanVM.Guest.B1.Digest.ChildListCChk

  `child_claim_list_any`'s records, frame loops (`__loop17`, `__loop18`) and
  `child_claim_list_last__L{k}`, evaluated (by kernel evaluation), for their completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Digest.ChainFilter

/-!
# `child_claim_list_any`, evaluated

A claim record (`ChildListDefs.claimOk`), evaluated on its own atoms (`ccOwn`, eleven or
thirteen from its hint, as soundness's windows): its slot hinted (`isWitO`), its mark `marks`
(claim `0`) or the previous claim's mark times `g` (`markC`), its four cells read at
`entries · o^4` through a pointer no mark's (`isCellLd`), its side atoms (`sideW`): the range
check against `last`, the mark's store at `region · o`, the cells' reads (`recW`). No check
decides membership in the stores (`decide (a ∈ S)` on atoms is a costly kernel evaluation):
`edgeOk` checks the stores' pointers instead (`storesOk`: a mark's or the state's from offset
`13`), so a cell's read and a state's load are no store. `cccOk k`:
`child_claim_list_last__L{k}`. `anycOk`: a frame loop of `m` records, its parts (`anycHead`,
`anycEdge`, `recsWin` by windows of records) kernel checks of their own.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `o`'s witness hint. -/
def isWitO (o : V) : Atom → Bool
  | .hint (.witness _ (.stack [v])) => decide (v = o)
  | _ => false

/-- Claim `j`'s mark: `marks` for claim `0`, else the previous claim's mark times `g` (by the pure
atoms `F`). -/
def markC (F : List Atom) (P : ClaimVs) (o0 j : ℕ) : Bool :=
  if j = 0 then true else
    match mulOf F (ccMark o0 P.marks j) with
    | some (m, c) => decide (m = ccMark o0 P.marks (j - 1)) && F.any (isConstAt c 2 0)
    | none => false

/-- A mark's store pointer `region · o`: claim `0`'s at `o0 + 4`, claim `j`'s at `ccOV o0 j + 6`. -/
def markPtrB (o0 q : ℕ) : Bool := q == o0 + 4 || (decide (o0 + 18 ≤ q) && (q - (o0 + 18)) % 14 == 0)

/-- A store: a mark's (through a mark pointer) or the next state's (through `.n stp` from
offset `13`). -/
def storesOk (o0 stp : ℕ) : Atom → Bool
  | .load _ p off => (p.idx == stp && decide (13 ≤ off)) || markPtrB o0 p.idx
  | _ => false

/-- Claim `j`'s cell `c`, read through `entries · o^4` (a pointer no mark's: not a store). -/
def isCellLd (F : List Atom) (P : ClaimVs) (o0 j c : ℕ) : Atom → Bool
  | .load d p off => decide (d = .n (ccCell o0 j c)) && off == c && !markPtrB o0 p.idx &&
      (monoOf F 40 p).isPerm (P.entries :: List.replicate 4 (.n (ccOV o0 j)))
  | _ => false

/-- Claim `j`'s side atoms: the range check of its slot against `last`, the store of its mark at
`region · o`, the reads of its cells. -/
def sideW (F : List Atom) (P : ClaimVs) (o0 j : ℕ) : Atom → Bool
  | .rangeCheck x y _ _ k => decide (k.idx < y.idx) && decide (k = P.last) &&
      decide (x = .n (ccOV o0 j))
  | .load d p off => (off == 0 && decide (d = ccMark o0 P.marks j) &&
        (monoOf F 40 p).isPerm [P.region, .n (ccOV o0 j)]) ||
      (decide (off < 4) && isCellLd F P o0 j off (.load d p off))
  | _ => false

/-- Claim `j`'s own atoms: from its hint, eleven for the first claim, thirteen for each other. -/
def ccOwn (A : List Atom) (p0 j : ℕ) : List Atom :=
  (A.drop (ccPos p0 j)).take (ccPos p0 (j + 1) - ccPos p0 j)

/-- **Claim `j`'s record, evaluated on its own atoms `W`**: its slot hinted, its mark, its cells
read, its side atoms. -/
def recW (W : List Atom) (P : ClaimVs) (o0 j : ℕ) : Bool :=
  W.any (isWitO (.n (ccOV o0 j))) && markC (W.filter pureB) P o0 j &&
    (List.range 4).all (fun c => W.any (isCellLd (W.filter pureB) P o0 j c)) &&
    W.all (fun a => !needsSide a || sideW (W.filter pureB) P o0 j a)

/-- Records `lo ≤ j < lo + w` of `K` (those from `K` on pass). -/
def recsWin (A : List Atom) (P : ClaimVs) (o0 p0 K lo w : ℕ) : Bool :=
  (List.range' lo w).all fun j => decide (K ≤ j) || recW (ccOwn A p0 j) P o0 j

/-- A load of the state, through `.n stp` below offset `13`. -/
def isStLd (stp : ℕ) : Atom → Bool
  | .load _ p off => p.idx == stp && decide (off < 13)
  | _ => false

/-- A store of the next state `outs`, through `.n stp` from offset `13`. -/
def isStSt (outs : List V) (stp : ℕ) : Atom → Bool
  | .load d p off => p.idx == stp && decide (13 ≤ off) && decide (off < 13 + outs.length) &&
      decide (d = outs.getD (off - 13) default)
  | _ => false

/-- **The atoms around the records**: the stores marks' or the next state's, the state's
pointer no mark's; before the records nothing with a side condition, after them the state's
loads and the next state's stores. -/
def edgeOk (A S : List Atom) (o0 p0 K stp : ℕ) (outs : List V) : Bool :=
  S.all (storesOk o0 stp) && !markPtrB o0 stp && (A.take p0).all (fun a => !needsSide a) &&
    (A.drop (ccPos p0 K)).all (fun a => !needsSide a || isStLd stp a || isStSt outs stp a)

/-- **`child_claim_list_last__L{k}`, evaluated** (`[state, entries, region, marks, last]`): in
order, its records, around them the state's loads. -/
def cccOk (k : ℕ) (f : Fn) : Bool :=
  (chk 5 f.body).isSome &&
  match splitBody f.body with
  | some (A, _) =>
    edgeOk A (storesOf 5 f.body) 5 0 k 0 [] &&
      (List.range k).all (fun j => recW (ccOwn A 0 j) cclP 5 j) && stLoadsOk A (.n 0) (cclSt k) 0
  | none => false

/-- A frame loop's shape: in order, its block atoms, its stores loads. -/
def anycHead (fn : Fn) (f : String) : Bool :=
  loopShapeF fn f && (chk 7 fn.body).isSome && (loopPre fn).all isAtomS &&
    atomsEqbL (atomsIn (loopPre fn)) (loopAtoms fn) && (storesOf 7 fn.body).all isLoadB

/-- A frame loop's next state, the chain's last outputs. -/
def anyOuts (m o0 st0 : ℕ) (A : List Atom) : List V :=
  (List.range 13).map ((anySpec m o0 st0 A).outV ((anySpec m o0 st0 A).nb - 1))

/-- A frame loop's atoms around its records, its state's loads, its pointers `chain · x^13` and
the marks `base · x^m`. -/
def anycEdge (fn : Fn) (m o0 p0 mk st0 : ℕ) : Bool :=
  let A := loopAtoms fn
  edgeOk A (storesOf 7 fn.body) o0 p0 m 12 (anyOuts m o0 st0 A) &&
    stLoadsOk A (.n 12) (anySt st0) 0 &&
    monoIs (A.filter pureB) (.n 12) (.n 2) (.n 0) 13 && monoIs (A.filter pureB) (.n mk) (.n 5) (.n 0) m

/-- **A frame loop of `m` records, evaluated** (`[x, N, chain, entries, region, base, last]`). -/
def anycOk (fn : Fn) (f : String) (m o0 p0 mk st0 : ℕ) : Bool :=
  anycHead fn f && anycEdge fn m o0 p0 mk st0 &&
    recsWin (loopAtoms fn) (anyP mk) o0 p0 m 0 m

/-- `__loop17`'s atoms. -/
noncomputable def anyc136Atoms : List Atom := loopAtoms (coreProgram.getD 378 default)

/-- Window `i` of `__loop17`'s records: `9i … 9i + 8`. -/
noncomputable def anycWin (i : ℕ) : Bool := recsWin anyc136Atoms (anyP 21) 22 15 136 (9 * i) 9


set_option maxRecDepth 100000 in
theorem ccc_lo : ∀ k < 9, cccOk k (coreProgram.getD (380 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccc_hi : ∀ k < 8, cccOk (9 + k) (coreProgram.getD (389 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any17c_ok : anycOk (coreProgram.getD 379 default) "__loop18" 17 19 12 18 255 = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
