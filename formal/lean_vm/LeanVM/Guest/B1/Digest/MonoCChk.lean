/-
  LeanVM.Guest.B1.Digest.MonoCChk

  `child_claim_list_mono`'s claims, frame loops (`child_claim_list_mono_loop0`,
  `child_claim_list_mono_loop1`) and `child_claim_list_mono_last__L{k}`, evaluated (by kernel
  evaluation), for their completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk
public import LeanVM.Guest.B1.Digest.MonoDefs
public import LeanVM.Guest.Data.NameStrings

/-!
# `child_claim_list_mono`, evaluated

A claim of the gap walk, on its eleven atoms (`monoWin`), evaluated (`mRecW`): its gap hinted
(`isWitO`), its pointers by pure products (`mPtrOk`), its cells loaded, and its side atoms
(`mSide`): the gap's touch, the mark's store at the coverage pointer, the cells' reads at the
table pointer. Stores go through a coverage pointer or the record pointer from offset `15`
(`mStoresOk`), so a cell's read and a record's read below `15` are no store. A frame loop
(`mcOk`): its head (`mcHead`), its atoms around the claims reading or writing the record
(`mRecLd`, `mcEdge`), the claims. `mlcOk k`: `child_claim_list_mono_last__L{k}`, its atoms around
the claims reading the record, dividing out the region and range-checking the walk's end.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `.n q` is a coverage pointer of the walk from the gap at `g0`, `.n (g0 + 10 j + 2)`. -/
def covPtrB (g0 q : ℕ) : Bool := decide (g0 + 2 ≤ q) && (q - (g0 + 2)) % 10 == 0

/-- A store: a mark's (through a coverage pointer) or the next record's (through `.n stp` from
offset `15`). -/
def mStoresOk (g0 stp : ℕ) : Atom → Bool
  | .load _ p off => (p.idx == stp && decide (15 ≤ off)) || covPtrB g0 p.idx
  | _ => false

/-- Claim `j`'s side atoms, its gap at `.n gap`: the gap's touch, the mark's store, the cells'
reads. -/
def mSide (j gap : ℕ) (mark : V) : Atom → Bool
  | .touch _ p => decide (p = .n gap)
  | .load d p off => (decide (p = .n (gap + 2)) && off == j && decide (d = mark)) ||
      (decide (p = .n (gap + 5)) && decide (4 * j ≤ off) && decide (off < 4 * j + 4))
  | _ => false

/-- Claim `j`'s pointers by pure products: `cov = pc · gap`, `ent = pe · (gap²)²`. -/
def mPtrOk (F : List Atom) (gap pc pe : ℕ) : Bool :=
  decide (mulOf F (.n (gap + 2)) = some (.n pc, .n gap)) &&
  decide (mulOf F (.n (gap + 3)) = some (.n gap, .n gap)) &&
  decide (mulOf F (.n (gap + 4)) = some (.n (gap + 3), .n (gap + 3))) &&
  decide (mulOf F (.n (gap + 5)) = some (.n pe, .n (gap + 4)))

/-- **Claim `j` of the walk, evaluated on its atoms `W`**: its gap hinted, its pointers, its cells
loaded, its side atoms. -/
def mRecW (W : List Atom) (j gap pc pe : ℕ) (mark : V) : Bool :=
  W.any (isWitO (.n gap)) && mPtrOk (W.filter pureB) gap pc pe &&
    (List.range 4).all (fun c => W.any (isLoadAt (.n (gap + 6 + c)) (.n (gap + 5)) (4 * j + c))) &&
    W.all (fun a => !needsSide a || mSide j gap mark a)

/-- Claims `lo ≤ j < lo + w` of `n` (those from `n` on pass). -/
def mRecsC (A : List Atom) (p0 g0 cov0 ent0 : ℕ) (mark : V) (n lo w : ℕ) : Bool :=
  (List.range' lo w).all fun j => decide (n ≤ j) ||
    mRecW (monoWin A p0 j) j (g0 + 10 * j) (mCov g0 cov0 j) (mEnt g0 ent0 j) mark

/-- A read or write of the record through `.n stp`: below offset `15` a read, then the next state
`outs`, the next coverage pointer `.n o28` and table pointer `.n o29`. -/
def mRecLd (stp : ℕ) (outs : List V) (o28 o29 : ℕ) : Atom → Bool
  | .load d p off => p.idx == stp && (decide (off < 15) ||
      (decide (off < 28) && decide (d = outs.getD (off - 15) default)) ||
      (off == 28 && decide (d = .n o28)) || (off == 29 && decide (d = .n o29)))
  | _ => false

/-- `.n o = .n last · c`, `c` the constant `word w`, by pure products. -/
def mOutOk (F : List Atom) (o last w : ℕ) : Bool :=
  match mulOf F (.n o) with
  | some (a, c) => decide (a = .n last) && F.any (isConstAt c w 0)
  | none => false

/-- A frame loop's shape: in order, its block atoms, its stores loads. -/
def mcHead (fn : Fn) (f : String) : Bool :=
  loopShapeF fn f && (chk 4 fn.body).isSome && (loopPre fn).all isAtomS &&
    atomsEqbL (atomsIn (loopPre fn)) (loopAtoms fn) && (storesOf 4 fn.body).all isLoadB

/-- A frame loop's next state, the chain's last outputs. -/
def mOuts (m st0 : ℕ) (A : List Atom) : List V :=
  (List.range 13).map ((monoSpec m st0 A).outV ((monoSpec m st0 A).nb - 1))

/-- **A frame loop's atoms around its claims**: the stores the next record's or marks', the rest
with a side condition the record's reads and writes; the record at `chain · x^15`, the next
pointers `cov · g^m`, `ent · g^(4m)`. -/
def mcEdge (fn : Fn) (m p0 st0 cw ew : ℕ) : Bool :=
  (storesOf 4 fn.body).all (mStoresOk 13 10) &&
    ((loopAtoms fn).take p0).all (fun a => !needsSide a ||
      mRecLd 10 (mOuts m st0 (loopAtoms fn)) (14 + 10 * m) (16 + 10 * m) a) &&
    ((loopAtoms fn).drop (p0 + 11 * m)).all (fun a => !needsSide a ||
      mRecLd 10 (mOuts m st0 (loopAtoms fn)) (14 + 10 * m) (16 + 10 * m) a) &&
    monoIs ((loopAtoms fn).filter pureB) (.n 10) (.n 2) (.n 0) 15 &&
    mOutOk ((loopAtoms fn).filter pureB) (14 + 10 * m) (mCov 13 11 m) cw &&
    mOutOk ((loopAtoms fn).filter pureB) (16 + 10 * m) (mEnt 13 12 m) ew

/-- **A frame loop of `m` claims, evaluated** (`[x, N, chain, mark]`). -/
def mcOk (fn : Fn) (f : String) (m p0 st0 cw ew : ℕ) : Bool :=
  mcHead fn f && mcEdge fn m p0 st0 cw ew && mRecsC (loopAtoms fn) p0 13 11 12 (.n 3) m 0 m

/-- `child_claim_list_mono_last__L{k}`'s side atoms around its claims: the record's reads, the
division of the walk's end by the region, the range check of its quotient `t`. -/
def mlcSide (k : ℕ) (t : Option V) : Atom → Bool
  | .load _ p off => decide (p = .n 0) && decide (off < 15)
  | .mul d x y => decide (d = .n (mlEnd k)) && decide (y = .n 1) && decide (some x = t)
  | .rangeCheck x y _ _ kk => decide (kk = .n 3) && decide (kk.idx < y.idx) && decide (some x = t)
  | _ => false

/-- **`child_claim_list_mono_last__L{k}`, evaluated** (`[rec, region, mark, limit]`): in order,
its claims, around them the record's reads and the bound; the walk's end `cov · g^k`. -/
def mlcOk (k : ℕ) (f : Fn) : Bool :=
  (chk 4 f.body).isSome &&
  match splitBody f.body with
  | some (A, _) =>
    (storesOf 4 f.body).all (mStoresOk 6 0) &&
      (A.take 2).all (fun a => !needsSide a || mlcSide k (endOf A (.n (mlEnd k))) a) &&
      (A.drop (2 + 11 * k)).all (fun a => !needsSide a || mlcSide k (endOf A (.n (mlEnd k))) a) &&
      mRecsC A 2 6 4 5 (.n 2) k 0 k &&
      (if k = 0 then true else mOutOk (A.filter pureB) (mlEnd k) (mCov 6 4 k) (2 ^ k))
  | none => false

/-- Window `i` of `child_claim_list_mono_loop0`'s claims: `9i … 9i + 8`. -/
noncomputable def mcWin (i : ℕ) : Bool := mRecsC mono136Atoms 9 13 11 12 (.n 3) 136 (9 * i) 9

set_option maxRecDepth 100000 in
theorem mlc_lo : ∀ k < 9, mlcOk k (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k)
    default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mlc_hi : ∀ k < 8, mlcOk (9 + k) (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + (9 + k))
    default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mc17_ok : mcOk (coreProgram.getD idx% «child_claim_list_mono_loop1» default)
    name% «child_claim_list_mono_loop1» 17 9 187 131072 432 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mc136_head : mcHead (coreProgram.getD idx% «child_claim_list_mono_loop0» default)
    name% «child_claim_list_mono_loop0» = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mc136_edge : mcEdge (coreProgram.getD idx% «child_claim_list_mono_loop0» default) 136 9 1377
    83200 72058697844523035 = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
