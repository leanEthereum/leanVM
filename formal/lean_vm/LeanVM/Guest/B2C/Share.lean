/-
  LeanVM.Guest.B2C.Share

  The sharing check: along every path of a core function, the values the certificate places in
  one frame cell hold one word, a fixed cell's constant if it has one.
-/

module

public import LeanVM.Guest.B2C.Defs

/-!
# Values sharing a cell

The compiler places several values in one frame cell (pooled constants, repeated pure results
and loads, `assert ==` and copies): on the honest memory the cell holds one word, so every value
a path names there must hold it. `swL` walks a core block as `walk` does, along every path, with
what is known of the cells (`SSt`): the cells some value named so far may occupy (`occ`, with the
constant the cell holds when known), facts `Ψ(c) = op(Ψ(c₁), …)` on the cells' words (`keys`:
sums, products, loads, compressions, by output cell), the values known to hold their cell's word
(`named`, by number), and the values named at an occupied cell still to be shown to hold its word
(`pend`). A pending value is shown by a constant equal to its cell's, by a key of its own atom
matching one of its cell's, or by a copy or `assert ==` with a known value of its cell; none may
be pending at a branch, at the end of a block, or after a statement that may return. At a join
the walk goes on with the facts from before the branch, the values known in every branch, and
every cell a branch occupied as occupied with no constant known.

The walk also confirms, per atom, the certificate's lists of temporaries and frame runs
(`Plumb.tmps`, `Plumb.runs`), from which the honest memory's cells are built.

Everything is structural recursion over lists and tries keyed by `ℕ`, for the kernel.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Tries: merging -/

namespace Trie

variable {α : Type}

/-- `f none` on every key of a trie. -/
def mergeR (f : Option α → Option α → Option α) : Trie α → Trie α
  | .nil => .nil
  | .node v l r => .node (f none v) (mergeR f l) (mergeR f r)

/-- Two tries merged key by key with `f` (`f none none = none`), by structural recursion on the
first. -/
def merge (f : Option α → Option α → Option α) : Trie α → Trie α → Trie α
  | .nil, b => mergeR f b
  | .node v l r, b => match b with
    | .nil => .node (f v none) (merge f l .nil) (merge f r .nil)
    | .node v' l' r' => .node (f v v') (merge f l l') (merge f r r')

end Trie

/-- The occupancy after a join: a cell occupied before keeps what was known of it, a cell a branch
occupied is occupied with no constant known. -/
def occJoin : Option (Option (ℕ × ℕ × ℕ)) → Option (Option (ℕ × ℕ × ℕ)) → Option (Option (ℕ × ℕ × ℕ))
  | some x, _ => some x
  | none, some _ => some none
  | none, none => none

/-- Values known on both sides. -/
def bothU : Option Unit → Option Unit → Option Unit
  | some _, some _ => some ()
  | _, _ => none

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
  occ : Trie (Option (ℕ × ℕ × ℕ))
  keys : Trie (List (ℕ × List ℕ))
  named : Trie Unit
  pend : List PF

/-- `k st`, its tries evaluated first. -/
def SSt.seq {β : Type} (st : SSt) (k : SSt → β) : β :=
  match st with
  | ⟨o, ky, n, p⟩ => o.seq fun o ↦ ky.seq fun ky ↦ n.seq fun n ↦ k ⟨o, ky, n, p⟩

theorem SSt.seq_eq {β : Type} (st : SSt) (k : SSt → β) : st.seq k = k st := by
  cases st
  simp only [SSt.seq, Trie.seq_eq]

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

variable (loc : Trie ℕ)

/-- The cell of value number `v`. -/
noncomputable def cellN (v : ℕ) : ℕ := cellOf loc (V.n v)

/-- The keys an atom gives the cells of its outputs: `(output cell, op, input cells)`. -/
noncomputable def cellKeys : Core.Atom → List (ℕ × ℕ × List ℕ)
  | .add d x y => [(cellOf loc d, 0, keyCells 0 [cellOf loc x, cellOf loc y]),
      (cellOf loc x, 0, keyCells 0 [cellOf loc d, cellOf loc y]),
      (cellOf loc y, 0, keyCells 0 [cellOf loc d, cellOf loc x])]
  | .mul d x y => [(cellOf loc d, 1, keyCells 1 [cellOf loc x, cellOf loc y])]
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    [(cellOf loc o0, 2, cellsOf loc [m0, m1, m2, m3, c0, c1, md]),
      (cellOf loc o1, 3, cellsOf loc [m0, m1, m2, m3, c0, c1, md])]
  | .load d p off => [(cellOf loc d, off + 4, [cellOf loc p])]
  | _ => []

/-! ## Steps -/

/-- Value `v` is known to hold its cell's word. -/
noncomputable def isNamed (st : SSt) (v : ℕ) : Bool := (getF st.named v).isSome

/-- Value `v` is pending. -/
def isPend (st : SSt) (v : ℕ) : Bool := st.pend.any fun p ↦ Nat.beq p.v v

/-- **Name a value**: at a cell no value occupies it holds the cell's word (with the constant
`kc` its atom gives, if any); at an occupied cell it is pending; at a header cell it is no frame
cell's. -/
noncomputable def nameV (kc : ℕ → Option (ℕ × ℕ × ℕ)) (st : SSt) (v : V) : SSt :=
  bif isNamed st v.idx || isPend st v.idx then st
  else
    natSeq (cellOf loc v) fun c ↦
    bif Nat.blt c 2 then ⟨st.occ, st.keys, setF () indexDepth st.named v.idx, st.pend⟩
    else match getF st.occ c with
      | some _ => ⟨st.occ, st.keys, st.named, ⟨v.idx, c, none, [], []⟩ :: st.pend⟩
      | none => ⟨setF (kc v.idx) envDepth st.occ c, st.keys, setF () indexDepth st.named v.idx, st.pend⟩

/-- Name values in order. -/
noncomputable def nameAll (kc : ℕ → Option (ℕ × ℕ × ℕ)) : SSt → List V → SSt
  | st, [] => st
  | st, v :: vs => (nameV loc kc st v).seq fun st ↦ nameAll kc st vs

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
  (match p.kc, getF st.occ p.c with
    | some x, some (some y) => x == y
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
      (Trie.seq (ok.foldl (fun t p ↦ setF () indexDepth t p.v) st.named) fun nm ↦
        (⟨st.occ, st.keys, nm, rest⟩ : SSt)).seq fun st ↦ discharge n st

/-- The constant an atom gives its output's cell, if none is known there. -/
noncomputable def recOcc (a : Core.Atom) (occ : Trie (Option (ℕ × ℕ × ℕ))) : Trie (Option (ℕ × ℕ × ℕ)) :=
  match a with
  | .const d x => match getF occ (cellOf loc d) with
    | some none => bif Nat.ble 2 (cellOf loc d) then
        setF (some (limbNat x 0, limbNat x 1, limbNat x 2)) envDepth occ (cellOf loc d) else occ
    | _ => occ
  | .assertNe _ _ p => match getF occ (cellOf loc p) with
    | some none => bif Nat.ble 2 (cellOf loc p) then setF (some (1, 0, 0)) envDepth occ (cellOf loc p) else occ
    | _ => occ
  | _ => occ

/-- An atom's facts on its cells, once all its values are known: a constant at its output's cell,
the keys of its outputs. -/
noncomputable def record (a : Core.Atom) (st : SSt) : SSt :=
  bif (Memory.atomUses a).all fun v ↦ isNamed st v.idx then
    ⟨recOcc loc a st.occ,
     (cellKeys loc a).foldl (fun t k ↦ bif Nat.ble 2 k.1 && k.2.2.all (Nat.ble 2) then
        setF ((k.2.1, k.2.2) :: (getF t k.1).getD []) envDepth t k.1 else t) st.keys, st.named, st.pend⟩
  else st

/-- **An atom**: its values named, their facts added, what can be shown shown, its cell facts
recorded. -/
noncomputable def stepAtom (st : SSt) (a : Core.Atom) : SSt :=
  (nameAll loc (constOf a) st (Memory.atomUses a)).seq fun st ↦
    (discharge loc (st.pend.length + 1) ⟨st.occ, st.keys, st.named, addFacts a st.pend⟩).seq fun st ↦
      record loc a st

/-- Other values named, and what can be shown shown. -/
noncomputable def nameStep (st : SSt) (vs : List V) : SSt :=
  (nameAll loc (fun _ ↦ none) st vs).seq fun st ↦ discharge loc (st.pend.length + 1) st

end Steps

/-! ## What the certificate lists -/

/-- The certificate lists a value with its cell. -/
noncomputable def listed (l : List (ℕ × ℕ)) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && l.any fun p ↦ Nat.beq p.1 v.idx && Nat.beq p.2 c

/-- A frame run's values sit in consecutive cells from `base`, listed. -/
noncomputable def runListed (loc : Trie ℕ) (l : List (ℕ × ℕ)) (base : ℕ) : ℕ → List V → Bool
  | _, [] => true
  | k, v :: vs => Nat.beq (cellOf loc v) (base + k) && listed l v (base + k) &&
      runListed loc l base (k + 1) vs

/-- The certificate's lists hold the atom's temporaries and run. -/
noncomputable def atomListed (loc : Trie ℕ) (P : Plumb) : Core.Atom → Bool
  | .rangeCheck _ _ t1 t2 _ => listed P.tmps t1 (cellOf loc t1) && listed P.tmps t2 (cellOf loc t2)
  | .frameAddr _ (r :: rs) => runListed loc P.runs (cellOf loc r) 0 (r :: rs)
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
  ⟨bs.foldl (fun t b ↦ Trie.merge occJoin t b.occ) pre.occ, pre.keys,
    match bs with
    | [] => pre.named
    | b :: bs => bs.foldl (fun t b' ↦ Trie.merge bothU t b'.named) b.named,
    []⟩

section Walk

variable (loc : Trie ℕ) (P : Plumb)

mutual
/-- **The walk** of a block: the state at its end, if every pending value is shown in time. -/
noncomputable def swL : SSt → List Stmt → Option SSt
  | st, [] => bif st.pend.isEmpty then some st else none
  | st, s :: ss => match swS st s with
    | some st' => st'.seq fun st' ↦ bif mayRet s && !st'.pend.isEmpty then none else swL st' ss
    | none => none

/-- One statement. -/
noncomputable def swS (st : SSt) : Stmt → Option SSt
  | .atom a => bif atomListed loc P a then some (stepAtom loc st a) else none
  | .ite c z n =>
    (nameStep loc st [c]).seq fun st1 ↦
      bif st1.pend.isEmpty then
        match swL st1 z, swL st1 n with
        | some sz, some sn => some (joinSt st1 [sz, sn])
        | _, _ => none
      else none
  | .match_ x arms =>
    (nameStep loc st [x]).seq fun st1 ↦
      bif st1.pend.isEmpty then
        match swArms st1 arms with
        | some bs => some (joinSt st1 bs)
        | none => none
      else none
  | s => some (nameStep loc st (stmtNames s))

/-- The arms of a `match`, each from `st`. -/
noncomputable def swArms (st : SSt) : List (List Stmt) → Option (List SSt)
  | [] => some []
  | a :: as => match swL st a, swArms st as with
    | some b, some bs => some (b :: bs)
    | _, _ => none
end

end Walk

/-! ## The check of a window -/

/-- The state a function starts with: its fixed cells occupied, the constants known. -/
noncomputable def initSt (P : Plumb) : SSt :=
  ⟨P.stat.foldl (fun t q ↦ setF (match q.2 with
    | .k a b c => some (a, b, c)
    | .fpg _ => none) envDepth t q.1) .nil, .nil, .nil, []⟩

/-- The temporaries' cells. -/
noncomputable def tmpCells (P : Plumb) : Trie Unit := P.tmps.foldl (fun t p ↦ setF () envDepth t p.2) .nil

/-- The fixed cells holding a frame pointer product. -/
noncomputable def fpgCells (P : Plumb) : Trie Unit :=
  P.stat.foldl (fun t q ↦ match q.2 with
    | .fpg _ => setF () envDepth t q.1
    | .k .. => t) .nil

/-- Every value is named by its number, its cell below `n`, in no fixed frame pointer cell, and
in no temporary's cell unless it is that temporary. -/
noncomputable def valOk (loc : Trie ℕ) (P : Plumb) (tc fc : Trie Unit) (n : ℕ) (v : V) : Bool :=
  v == V.n v.idx && Nat.blt (cellOf loc v) n && (getF fc (cellOf loc v)).isNone &&
    (listed P.tmps v (cellOf loc v) || (getF tc (cellOf loc v)).isNone)

/-- The cells a list of `(value, cell)` pairs gives, by cell. -/
noncomputable def byCell (l : List (ℕ × ℕ)) : Trie ℕ := l.foldl (fun t p ↦ setF p.1 envDepth t p.2) .nil

/-- A list of `(value, cell)` pairs with one value per cell, the cells in `[2, n)`. -/
noncomputable def pairsOk (l : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (byCell l).seq fun t ↦ l.all fun p ↦ getF t p.2 == some p.1 && Nat.ble 2 p.2 && Nat.blt p.2 n

/-- The certificate's lists: the fixed cells as the walk starts with them, in the frame; the
temporaries' and runs' cells one value each, apart; the call sites' and table targets' cells in
the frame; no table selector a temporary. -/
noncomputable def listsOk (P : Plumb) (n : ℕ) : Bool :=
  (initSt P).occ.seq fun occ ↦ (tmpCells P).seq fun tc ↦
  P.stat.all (fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n && getF occ q.1 == some (match q.2 with
    | .k a b c => some (a, b, c)
    | .fpg _ => none)) &&
  pairsOk P.tmps n && pairsOk P.runs n && P.runs.all (fun p ↦ (getF tc p.2).isNone) &&
  P.sites.all (fun s ↦ Nat.ble 2 s.q && Nat.blt s.q n) &&
  P.arms.all (fun a ↦ Nat.ble 2 a.2.1 && Nat.blt a.2.1 n && !(P.tmps.any fun p ↦ Nat.beq p.1 a.1))

/-- The frame size the check bounds the cells by. -/
def fsN (j : ℕ) : ℕ := bif Nat.beq j 1 then mainFrame else max 2 (fsAt j)

/-- **The sharing check of function `j`**, with the certificate's lists. -/
noncomputable def shareOk (j : ℕ) : Bool :=
  (locTrie (certOf j).locs).seq fun loc ↦ (tmpCells (plumbOf j)).seq fun tc ↦
  (fpgCells (plumbOf j)).seq fun fc ↦
  Nat.blt (fsN j) (2 ^ envDepth) && Nat.blt ((certOf j).locs.length + 1) (2 ^ indexDepth) &&
  ((coreOf j).params ++ Memory.Stmt.usesList (coreOf j).body ++ Memory.Stmt.tmpsList (coreOf j).body).all
    (valOk loc (plumbOf j) tc fc (fsN j)) &&
  listsOk (plumbOf j) (fsN j) &&
  (swL loc (plumbOf j) (nameStep loc (initSt (plumbOf j)) (coreOf j).params) (coreOf j).body).isSome

end
end LeanVM.Guest.B2C
