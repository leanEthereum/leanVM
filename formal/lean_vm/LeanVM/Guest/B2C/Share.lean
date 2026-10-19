/-
  LeanVM.Guest.B2C.Share

  The sharing check: along every path of a core function, the values the certificate places in
  one frame cell hold one word, a fixed cell's constant if it has one.
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.Data.Snaps

/-!
# Values sharing a cell

The compiler places several values in one frame cell (pooled constants, repeated pure results
and loads, `assert ==` and copies): on the honest memory the cell holds one word, so every value
a path names there must hold it. `swL` walks a core block as `walk` does, along every path, with
what is known of the cells (`SSt`): the cells some value named so far may occupy (`occ`), the
constants known at shared cells (`cst`), facts `Ψ(c) = op(Ψ(c₁), …)` on the shared cells' words
(`keys`: sums, products, loads, compressions, by output cell), the values known to hold their
cell's word (`named`), and the values named at an occupied cell still to be shown to hold its
word (`pend`). A pending value is shown by a constant equal to its cell's, by a key of its own
atom matching one of its cell's, or by a copy or `assert ==` with a known value of its cell; none
may be pending at a branch, at the end of a block, or after a statement that may return. At a
join the walk goes on with the facts from before the branch, the values known in every branch,
and every cell a branch occupied as occupied.

The occupied cells and the known values are bit sets (`ℕ`), whose operations the kernel does in
one step each. A function is walked in windows, each within a window of its soundness certificate
and reading that window's cells (`locW`): window `k + 1` starts from a `Snap` of the state window
`k` ends in, which the end state must refine (`refines`).

The walk also confirms, per atom, the certificate's lists of temporaries and frame runs
(`Plumb.tmps`, `Plumb.runs`), from which the honest memory's cells are built.

Everything is structural recursion over lists and tries keyed by `ℕ`, for the kernel.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Bit sets -/

/-- Bit `n` of `s`. -/
def bitN (s n : ℕ) : Bool := Nat.beq (Nat.mod (Nat.shiftRight s n) 2) 1

/-- `s` with bit `n` set. -/
def setBit (s n : ℕ) : ℕ := Nat.lor s (Nat.shiftLeft 1 n)

/-- The bit set of a list. -/
def bitsOf (l : List ℕ) : ℕ := l.foldl setBit 0

/-! ## A window's cells -/

/-- The cells of a list packed, cell `m` in the `m`-th base-`2^16` digit. -/
def packCells : List ℕ → ℕ
  | [] => 0
  | c :: cs => Nat.add c (Nat.mul (packCells cs) 65536)

/-- A window's cells: those of the values `lo, …, lo + len - 1` packed in `pk`, and those of the
other values its statements name, by value (`ins`). -/
structure Loc where
  lo : ℕ
  len : ℕ
  pk : ℕ
  ins : Trie ℕ

/-- The cell of value number `v`, if the window has it. -/
noncomputable def Loc.get? (L : Loc) (v : ℕ) : Option ℕ :=
  bif Nat.ble L.lo v && Nat.blt v (Nat.add L.lo L.len) then
    some (Nat.mod (Nat.div L.pk (Nat.pow 65536 (Nat.sub v L.lo))) 65536)
  else getF L.ins v

/-- The cell of a value (`0` if the window has none). -/
noncomputable def Loc.cell (L : Loc) (v : V) : ℕ := (L.get? v.idx).getD 0

/-- `k L`, its packed cells evaluated first. -/
def Loc.seq {β : Type} (L : Loc) (k : Loc → β) : β :=
  match L with
  | ⟨lo, len, pk, ins⟩ => natSeq lo fun lo ↦ natSeq len fun len ↦ natSeq pk fun pk ↦ ins.seq fun ins ↦
      k ⟨lo, len, pk, ins⟩

theorem Loc.seq_eq {β : Type} (L : Loc) (k : Loc → β) : L.seq k = k L := by
  cases L
  simp only [Loc.seq, natSeq_eq, Trie.seq_eq]

/-- Window `i`'s cells in certificate `C`. -/
noncomputable def locW (C : Cert) (i : ℕ) : Loc :=
  ⟨nth C.los i 0, (nth C.cells i []).length, packCells (nth C.cells i []), insTrie (nth C.ins i []) .nil⟩

/-! ## The state -/

/-- A value pending to be shown to hold its cell's word, with the facts its atoms give it: a
constant, keys `(op, inputs)` of atoms of which it is an output, values it equals. -/
structure PF where
  v : ℕ
  c : ℕ
  kc : Option (ℕ × ℕ × ℕ)
  keys : List (ℕ × List ℕ)
  eqs : List ℕ

/-- What is known along a path. -/
structure SSt where
  occ : ℕ
  cst : Trie (ℕ × ℕ × ℕ)
  keys : Trie (List (ℕ × List ℕ))
  named : ℕ
  pend : List PF

/-- `k st`, its parts evaluated first. -/
def SSt.seq {β : Type} (st : SSt) (k : SSt → β) : β :=
  match st with
  | ⟨o, c, ky, n, p⟩ => natSeq o fun o ↦ c.seq fun c ↦ ky.seq fun ky ↦ natSeq n fun n ↦ k ⟨o, c, ky, n, p⟩

theorem SSt.seq_eq {β : Type} (st : SSt) (k : SSt → β) : st.seq k = k st := by
  cases st
  simp only [SSt.seq, Trie.seq_eq, natSeq_eq]

/-! ## Atoms -/

/-- The constant an atom gives value `v`. -/
noncomputable def constOf (a : Core.Atom) (v : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match a with
  | .const d x => bif Nat.beq d.idx v then some (limbNat x 0, limbNat x 1, limbNat x 2) else none
  | .assertNe _ _ p => bif Nat.beq p.idx v then some (1, 0, 0) else none
  | _ => none

/-- The keys an atom gives value `v` as an output: `0` a sum, `1` a product, `2`, `3` the
compression's two output words, `off + 4` a load at offset `off`. -/
def keysOf (a : Core.Atom) (v : ℕ) : List (ℕ × List ℕ) :=
  match a with
  | .add d x y => (bif Nat.beq d.idx v then [(0, [x.idx, y.idx])] else []) ++
      (bif Nat.beq x.idx v then [(0, [d.idx, y.idx])] else []) ++
      (bif Nat.beq y.idx v then [(0, [d.idx, x.idx])] else [])
  | .mul d x y => bif Nat.beq d.idx v then [(1, [x.idx, y.idx])] else []
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    (bif Nat.beq o0.idx v then [(2, [m0.idx, m1.idx, m2.idx, m3.idx, c0.idx, c1.idx, md.idx])] else []) ++
      (bif Nat.beq o1.idx v then [(3, [m0.idx, m1.idx, m2.idx, m3.idx, c0.idx, c1.idx, md.idx])] else [])
  | .load d p off => bif Nat.beq d.idx v then [(off + 4, [p.idx])] else []
  | _ => []

/-- The values an atom says `v` equals. -/
def eqsOf (a : Core.Atom) (v : ℕ) : List ℕ :=
  match a with
  | .copy d x => (bif Nat.beq d.idx v then [x.idx] else []) ++ (bif Nat.beq x.idx v then [d.idx] else [])
  | .assertEq d x => (bif Nat.beq d.idx v then [x.idx] else []) ++ (bif Nat.beq x.idx v then [d.idx] else [])
  | _ => []

/-- A key's input cells, a sum's and a product's two in order. -/
def keyCells (op : ℕ) (cs : List ℕ) : List ℕ :=
  match op, cs with
  | 0, [a, b] => bif Nat.ble a b then [a, b] else [b, a]
  | 1, [a, b] => bif Nat.ble a b then [a, b] else [b, a]
  | _, cs => cs

section Steps

variable (loc : Loc) (sh : ℕ)

/-- The cell of value number `v`. -/
noncomputable def cellN (v : ℕ) : ℕ := loc.cell (V.n v)

/-- The keys an atom gives the cells of its outputs: `(output cell, op, input cells)`. -/
noncomputable def cellKeys : Core.Atom → List (ℕ × ℕ × List ℕ)
  | .add d x y => [(loc.cell d, 0, keyCells 0 [loc.cell x, loc.cell y]),
      (loc.cell x, 0, keyCells 0 [loc.cell d, loc.cell y]),
      (loc.cell y, 0, keyCells 0 [loc.cell d, loc.cell x])]
  | .mul d x y => [(loc.cell d, 1, keyCells 1 [loc.cell x, loc.cell y])]
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    [(loc.cell o0, 2, [m0, m1, m2, m3, c0, c1, md].map loc.cell),
      (loc.cell o1, 3, [m0, m1, m2, m3, c0, c1, md].map loc.cell)]
  | .load d p off => [(loc.cell d, off + 4, [loc.cell p])]
  | _ => []

/-! ## Steps -/

/-- Value `v` is known to hold its cell's word. -/
def isNamed (st : SSt) (v : ℕ) : Bool := bitN st.named v

/-- Value `v` is pending. -/
def isPend (st : SSt) (v : ℕ) : Bool := st.pend.any fun p ↦ Nat.beq p.v v

/-- The constants of a shared cell, with `x` if given. -/
noncomputable def cstAt (cst : Trie (ℕ × ℕ × ℕ)) (c : ℕ) : Option (ℕ × ℕ × ℕ) → Trie (ℕ × ℕ × ℕ)
  | some x => bif bitN sh c then setF x envDepth cst c else cst
  | none => cst

/-- **Name a value**: at a cell no value occupies it holds the cell's word (with the constant
`kc` its atom gives, if any, kept at a shared cell); at an occupied cell it is pending; at a
header cell it is no frame cell's. -/
noncomputable def nameV (kc : ℕ → Option (ℕ × ℕ × ℕ)) (st : SSt) (v : V) : SSt :=
  bif isNamed st v.idx || isPend st v.idx then st
  else
    natSeq (loc.cell v) fun c ↦
    bif Nat.blt c 2 then ⟨st.occ, st.cst, st.keys, setBit st.named v.idx, st.pend⟩
    else bif bitN st.occ c then ⟨st.occ, st.cst, st.keys, st.named, ⟨v.idx, c, none, [], []⟩ :: st.pend⟩
    else ⟨setBit st.occ c, cstAt sh st.cst c (kc v.idx), st.keys, setBit st.named v.idx, st.pend⟩

/-- Name values in order. -/
noncomputable def nameAll (kc : ℕ → Option (ℕ × ℕ × ℕ)) : SSt → List V → SSt
  | st, [] => st
  | st, v :: vs => (nameV loc sh kc st v).seq fun st ↦ nameAll kc st vs

/-- The facts an atom gives the pending values. -/
noncomputable def addFacts (a : Core.Atom) (ps : List PF) : List PF :=
  ps.map fun p ↦ ⟨p.v, p.c, (match p.kc with
    | some x => some x
    | none => constOf a p.v), keysOf a p.v ++ p.keys, eqsOf a p.v ++ p.eqs⟩

/-- Value `v` is known and in a frame cell. -/
noncomputable def knownIn (st : SSt) (v : ℕ) : Bool := isNamed st v && Nat.ble 2 (cellN loc v)

/-- A key `(op, inputs)` of a pending value is one of its cell `c`'s, its inputs known. -/
noncomputable def keyOk (st : SSt) (c : ℕ) (k : ℕ × List ℕ) : Bool :=
  k.2.all (knownIn loc st) &&
    ((getF st.keys c).getD []).any fun k' ↦ Nat.beq k'.1 k.1 && k'.2 == keyCells k.1 (k.2.map (cellN loc))

/-- A pending value is shown. -/
noncomputable def pfOk (st : SSt) (p : PF) : Bool :=
  (match p.kc, getF st.cst p.c with
    | some x, some y => x == y
    | _, _ => false) ||
  p.keys.any (keyOk loc st p.c) ||
  p.eqs.any fun x ↦ isNamed st x && Nat.beq (cellN loc x) p.c

/-- The pending values shown and the others. -/
noncomputable def splitPend (st : SSt) : List PF → List PF × List PF
  | [] => ([], [])
  | p :: ps => match splitPend st ps with
    | (ok, rest) => bif pfOk loc st p then (p :: ok, rest) else (ok, p :: rest)

/-- Show what can be shown, in at most `n` rounds. -/
noncomputable def discharge : ℕ → SSt → SSt
  | 0, st => st
  | n + 1, st =>
    match splitPend loc st st.pend with
    | ([], _) => st
    | (ok, rest) =>
      (natSeq (ok.foldl (fun s p ↦ setBit s p.v) st.named) fun nm ↦
        (⟨st.occ, st.cst, st.keys, nm, rest⟩ : SSt)).seq fun st ↦ discharge n st

/-- The constant an atom gives its output's shared cell, if none is known there. -/
noncomputable def recCst (a : Core.Atom) (cst : Trie (ℕ × ℕ × ℕ)) : Trie (ℕ × ℕ × ℕ) :=
  match a with
  | .const d x => match getF cst (loc.cell d) with
    | none => bif Nat.ble 2 (loc.cell d) && bitN sh (loc.cell d) then
        setF (limbNat x 0, limbNat x 1, limbNat x 2) envDepth cst (loc.cell d) else cst
    | some _ => cst
  | .assertNe _ _ p => match getF cst (loc.cell p) with
    | none => bif Nat.ble 2 (loc.cell p) && bitN sh (loc.cell p) then
        setF (1, 0, 0) envDepth cst (loc.cell p) else cst
    | some _ => cst
  | _ => cst

/-- An atom's facts on its shared cells, once all its values are known: a constant at its
output's cell, the keys of its outputs. -/
noncomputable def record (a : Core.Atom) (st : SSt) : SSt :=
  bif (Memory.atomUses a).all fun v ↦ isNamed st v.idx then
    ⟨st.occ, recCst loc sh a st.cst,
     (cellKeys loc a).foldl (fun t k ↦ bif Nat.ble 2 k.1 && bitN sh k.1 && k.2.2.all (Nat.ble 2) then
        setF ((k.2.1, k.2.2) :: (getF t k.1).getD []) envDepth t k.1 else t) st.keys, st.named, st.pend⟩
  else st

/-- **An atom**: its values named, their facts added, what can be shown shown, its cell facts
recorded. -/
noncomputable def stepAtom (st : SSt) (a : Core.Atom) : SSt :=
  (nameAll loc sh (constOf a) st (Memory.atomUses a)).seq fun st ↦
    (discharge loc (st.pend.length + 1) ⟨st.occ, st.cst, st.keys, st.named, addFacts a st.pend⟩).seq fun st ↦
      record loc sh a st

/-- Other values named, and what can be shown shown. -/
noncomputable def nameStep (st : SSt) (vs : List V) : SSt :=
  (nameAll loc sh (fun _ ↦ none) st vs).seq fun st ↦ discharge loc (st.pend.length + 1) st

end Steps

/-! ## What the certificate lists -/

/-- The certificate lists a value with its cell. -/
noncomputable def listed (l : List (ℕ × ℕ)) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && l.any fun p ↦ Nat.beq p.1 v.idx && Nat.beq p.2 c

/-- The certificate lists a temporary with its cell: `tt` is its temporaries by cell. -/
noncomputable def listedT (tt : Trie ℕ) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && getF tt c == some v.idx

/-- A frame run's values sit in consecutive cells from `base`, listed. -/
noncomputable def runListed (loc : Loc) (l : List (ℕ × ℕ)) (base : ℕ) : ℕ → List V → Bool
  | _, [] => true
  | k, v :: vs => Nat.beq (loc.cell v) (base + k) && listed l v (base + k) &&
      runListed loc l base (k + 1) vs

/-- The certificate's lists hold the atom's temporaries and run. -/
noncomputable def atomListed (loc : Loc) (tt : Trie ℕ) (P : Plumb) : Core.Atom → Bool
  | .rangeCheck _ _ t1 t2 _ => listedT tt t1 (loc.cell t1) && listedT tt t2 (loc.cell t2)
  | .frameAddr _ (r :: rs) => runListed loc P.runs (loc.cell r) 0 (r :: rs)
  | _ => true

/-! ## The walk -/

/-- The values a statement names (an atom's with its facts, in `stepAtom`). -/
def stmtNames : Stmt → List V
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .atom _ => []

mutual
/-- A statement may return. -/
def mayRet : Stmt → Bool
  | .ret _ => true
  | .ite _ z n => !Stmt.noRetList z || !Stmt.noRetList n
  | .match_ _ arms => mayRetArms arms
  | _ => false

/-- Some arm may return. -/
def mayRetArms : List (List Stmt) → Bool
  | [] => false
  | a :: as => !Stmt.noRetList a || mayRetArms as
end

/-- The state after a join: the facts from before, the values known in every branch, and the
cells any branch occupied. -/
def joinSt (pre : SSt) (bs : List SSt) : SSt :=
  ⟨bs.foldl (fun o b ↦ Nat.lor o b.occ) pre.occ, pre.cst, pre.keys,
    match bs with
    | [] => pre.named
    | b :: bs => bs.foldl (fun n b' ↦ Nat.land n b'.named) b.named,
    []⟩

section Walk

variable (loc : Loc) (sh : ℕ) (tt : Trie ℕ) (P : Plumb)

mutual
/-- **The walk** of a block: the state at its end, if every pending value is shown in time. -/
noncomputable def swL : SSt → List Stmt → Option SSt
  | st, [] => bif st.pend.isEmpty then some st else none
  | st, s :: ss => match swS st s with
    | some st' => st'.seq fun st' ↦ bif mayRet s && !st'.pend.isEmpty then none else swL st' ss
    | none => none

/-- One statement. -/
noncomputable def swS (st : SSt) : Stmt → Option SSt
  | .atom a => bif atomListed loc tt P a then some (stepAtom loc sh st a) else none
  | .ite c z n =>
    (nameStep loc sh st [c]).seq fun st1 ↦
      bif st1.pend.isEmpty then
        match swL st1 z, swL st1 n with
        | some sz, some sn => some (joinSt st1 [sz, sn])
        | _, _ => none
      else none
  | .match_ x arms =>
    (nameStep loc sh st [x]).seq fun st1 ↦
      bif st1.pend.isEmpty then
        match swArms st1 arms with
        | some bs => some (joinSt st1 bs)
        | none => none
      else none
  | s => some (nameStep loc sh st (stmtNames s))

/-- The arms of a `match`, each from `st`. -/
noncomputable def swArms (st : SSt) : List (List Stmt) → Option (List SSt)
  | [] => some []
  | a :: as => match swL st a, swArms st as with
    | some b, some bs => some (b :: bs)
    | _, _ => none
end

end Walk

/-! ## The check of a function, by windows -/

/-- The state a function starts with: its fixed cells occupied, their constants known. -/
noncomputable def initSt (P : Plumb) : SSt :=
  ⟨bitsOf (P.stat.map Prod.fst), P.stat.foldl (fun t q ↦ match q.2 with
    | .k a b c => setF (a, b, c) envDepth t q.1
    | .fpg _ => t) .nil, .nil, 0, []⟩

/-- The temporaries' cells. -/
noncomputable def tmpCells (P : Plumb) : ℕ := bitsOf (P.tmps.map Prod.snd)

/-- The fixed cells holding a frame pointer product. -/
noncomputable def fpgCells (P : Plumb) : ℕ :=
  bitsOf (P.stat.filterMap fun q ↦ match q.2 with
    | .fpg _ => some q.1
    | .k .. => none)

/-- Every value is named by its number, has a cell below `n`, in no fixed frame pointer cell, and
in no temporary's cell unless it is that temporary. -/
noncomputable def valOk (loc : Loc) (tt : Trie ℕ) (tc fc : ℕ) (n : ℕ) (v : V) : Bool :=
  v == V.n v.idx && (loc.get? v.idx).isSome && Nat.blt (loc.cell v) n && !bitN fc (loc.cell v) &&
    (!bitN tc (loc.cell v) || listedT tt v (loc.cell v))

/-- The cells a list of `(value, cell)` pairs gives, by cell. -/
noncomputable def byCell (l : List (ℕ × ℕ)) : Trie ℕ := l.foldl (fun t p ↦ setF p.1 envDepth t p.2) .nil

/-- A list of `(value, cell)` pairs with one value per cell, the cells in `[2, n)`. -/
noncomputable def pairsOk (l : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (byCell l).seq fun t ↦ l.all fun p ↦ getF t p.2 == some p.1 && Nat.ble 2 p.2 && Nat.blt p.2 n

/-- The certificate's lists: the fixed cells as the walk starts with them, in the frame; the
temporaries' and runs' cells one value each, apart; the call sites' and table targets' cells in
the frame; no table selector a temporary. -/
noncomputable def listsOk (P : Plumb) (n : ℕ) : Bool :=
  (initSt P).cst.seq fun cst ↦ natSeq (tmpCells P) fun tc ↦
  P.stat.all (fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n && match q.2 with
    | .k a b c => getF cst q.1 == some (a, b, c)
    | .fpg _ => true) &&
  pairsOk P.tmps n && pairsOk P.runs n && P.runs.all (fun p ↦ !bitN tc p.2) &&
  P.sites.all (fun s ↦ Nat.ble 2 s.q && Nat.blt s.q n) &&
  P.arms.all (fun a ↦ Nat.ble 2 a.2.1 && Nat.blt a.2.1 n && !(P.tmps.any fun p ↦ Nat.beq p.1 a.1))

/-- The snapshots of function `j`'s windows after the first. -/
noncomputable def snapsOf (j : ℕ) : List Snap :=
  ((Data.snaps.find? fun p ↦ Nat.beq p.1 j).map Prod.snd).getD []

/-- The state of a snapshot. -/
noncomputable def Snap.st (s : Snap) : SSt :=
  ⟨s.occ, s.cst.foldl (fun t q ↦ setF q.2 envDepth t q.1) .nil,
    s.keys.foldl (fun t q ↦ setF (q.2 :: (getF t q.1).getD []) envDepth t q.1) .nil, bitsOf s.named, []⟩

/-- A window's end state refines the next one's start: its occupied cells are occupied there,
and what that knows it knows. -/
noncomputable def refines (m : SSt) (s : Snap) : Bool :=
  Nat.beq (Nat.land m.occ s.occ) m.occ && s.named.all (bitN m.named) &&
    s.cst.all (fun q ↦ getF m.cst q.1 == some q.2) &&
    s.keys.all (fun q ↦ ((getF m.keys q.1).getD []).any fun k ↦ k == q.2)

/-- `s` has none of `t`'s bits. -/
def apart (s t : ℕ) : Bool := Nat.beq (Nat.land s t) 0

/-- No cell twice, `s` the cells seen. -/
def bitsNodup : List ℕ → ℕ → Bool
  | [], _ => true
  | c :: cs, s => !bitN s c && bitsNodup cs (setBit s c)

/-- The cells of the call sites: the callee frame pointers' and the fused dispatches' targets. -/
def siteCells (P : Plumb) : List ℕ := P.sites.flatMap fun s ↦ s.q :: (bif Nat.beq s.tgt 0 then [] else [s.tgt])

/-- **The cells apart**, in `C`'s order: the fixed cells from the temporaries', the call sites'
from the temporaries', the runs', the fixed cells and every value's, the table targets' from all
of those, the fixed cells, the sites' and the targets' each once, the entry environment's cells
fixed frame pointer cells; in `main`, all below the jump table. -/
noncomputable def apartOk (j : ℕ) : Bool :=
  natSeq (Nat.lor (tmpCells (plumbOf j)) (bitsOf ((plumbOf j).runs.map Prod.snd))) fun tr ↦
  natSeq (bitsOf ((plumbOf j).stat.map Prod.fst)) fun st ↦
  natSeq (Nat.lor (Nat.lor tr st) (bitsOf (certOf j).locs)) fun trsv ↦
  natSeq (bitsOf (siteCells (plumbOf j))) fun sc ↦
  natSeq (bitsOf ((plumbOf j).arms.map fun a ↦ a.2.1)) fun ac ↦
  apart st (tmpCells (plumbOf j)) && apart sc trsv && apart ac (Nat.lor trsv sc) &&
    bitsNodup ((plumbOf j).stat.map Prod.fst) 0 && bitsNodup (siteCells (plumbOf j)) 0 &&
    bitsNodup ((plumbOf j).arms.map fun a ↦ a.2.1) 0 &&
    (certOf j).facts.env.all (fun p ↦ (plumbOf j).stat.any fun q ↦ Nat.beq q.1 p.1 && q.2 == .fpg 0) &&
    (bif Nat.beq j 1 then Nat.blt (Nat.lor (Nat.lor trsv sc) ac) (2 ^ 167) else true)

/-- The snapshot window `k` starts from (`k ≥ 1`). -/
def snapAt (snaps : List Snap) (k : ℕ) : Snap := nth snaps (k - 1) ⟨0, 0, 0, [], [], []⟩

/-- Where window `k` starts. -/
def startW (snaps : List Snap) (k : ℕ) : ℕ := bif k == 0 then 0 else (snapAt snaps k).start

/-- The soundness window whose cells window `k` reads. -/
def winW (snaps : List Snap) (k : ℕ) : ℕ := bif k == 0 then 0 else (snapAt snaps k).win

/-- Window `k`'s statements. -/
def stmtsW (body : List Stmt) (snaps : List Snap) (k : ℕ) : List Stmt :=
  bif Nat.blt k snaps.length then (body.drop (startW snaps k)).take (startW snaps (k + 1) - startW snaps k)
  else body.drop (startW snaps k)

/-- The windows start at nondecreasing statements, each reading a soundness window's cells. -/
def snapsOk (C : Cert) (snaps : List Snap) : Bool :=
  (List.range snaps.length).all fun k ↦
    Nat.ble (startW snaps k) (startW snaps (k + 1)) && Nat.ble (winW snaps (k + 1)) C.cuts.length

/-- **What the sharing check says once of function `j`**: the frame's bounds, the lists, the
windows' order, the cells apart, the parameters numbered in the first window's cells. -/
noncomputable def shareStatic (j : ℕ) : Bool :=
  (locW (certOf j) 0).seq fun loc ↦ natSeq (tmpCells (plumbOf j)) fun tc ↦
  natSeq (fpgCells (plumbOf j)) fun fc ↦ (byCell (plumbOf j).tmps).seq fun tt ↦
  (nth (certOf j).cells 0 []).all (fun c ↦ Nat.blt c 65536) &&
  Nat.blt (fsN j) (2 ^ envDepth) && listsOk (plumbOf j) (fsN j) && snapsOk (certOf j) (snapsOf j) &&
    apartOk j && (coreOf j).params.all (valOk loc tt tc fc (fsN j))

/-- **Window `k` of function `j`**, starting from the snapshots `snaps`: its values numbered, in
its soundness window's cells and in the frame; its walk from the parameters' naming (the first
window) or from its snapshot, ending in a state that refines the next one's. -/
noncomputable def shareWin (j : ℕ) (snaps : List Snap) (k : ℕ) : Bool :=
  (locW (certOf j) (winW snaps k)).seq fun loc ↦ natSeq (bitsOf (plumbOf j).sh) fun sh ↦
  natSeq (tmpCells (plumbOf j)) fun tc ↦ natSeq (fpgCells (plumbOf j)) fun fc ↦
  (byCell (plumbOf j).tmps).seq fun tt ↦
  (nth (certOf j).cells (winW snaps k) []).all (fun c ↦ Nat.blt c 65536) &&
  (Memory.Stmt.usesList (stmtsW (coreOf j).body snaps k) ++
    Memory.Stmt.tmpsList (stmtsW (coreOf j).body snaps k)).all (valOk loc tt tc fc (fsN j)) &&
  (match swL loc sh tt (plumbOf j)
      (bif k == 0 then nameStep loc sh (initSt (plumbOf j)) (coreOf j).params else (snapAt snaps k).st)
      (stmtsW (coreOf j).body snaps k) with
    | some m => bif Nat.blt k snaps.length then refines m (snapAt snaps (k + 1)) else true
    | none => false)

/-- **The sharing check of function `j`**: its static part and every window's. -/
def ShareOk (j : ℕ) : Prop :=
  shareStatic j = true ∧ ∀ k ≤ (snapsOf j).length, shareWin j (snapsOf j) k = true

end
end LeanVM.Guest.B2C
