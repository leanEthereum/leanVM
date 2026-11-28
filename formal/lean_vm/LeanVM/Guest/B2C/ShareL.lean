/-
  LeanVM.Guest.B2C.ShareL

  The sharing check by a local certificate: one walk of a core body's positions, each value's
  facts checked where it first occurs and its sharing justified there.
-/

module

public import LeanVM.Guest.Local.Fold
public import LeanVM.Guest.B2C.ShareBase
public import LeanVM.Guest.B2C.CplCheck

/-!
# The local sharing check

The compiler puts several values in one frame cell; on the honest memory a cell holds one word,
so the values a path names in one cell must be equal. A cell holding one value needs nothing. A
**shared** value (in a cell with others, or in a fixed constant cell) is justified once, where it
first occurs (its **home**, the values being numbered in order of first occurrence, so the walk
knows a home as the next number), by one of:

* `root`: no other shared value of its cell can come before it on a path: it is the first site
  of its cell, or the sites before it are in earlier arms of its innermost branch (its cell's
  first site is after the branch, the previous one before its arm);
* `eq`: a `copy` or `assert ==` with another shared value of the cell, justified before it;
* `constK`: its `SET` constant is its fixed cell's (`Plumb.stat`);
* `constA`, `key`: an **anchor**, an earlier atom whose block holds this home, gives its cell
  the same constant, or the same operation of the same input cells (a sum, a product, a load, a
  `KECCAK` output), and its inputs are justified before it.

Every other occurrence of a shared value lies after its home, in its home's block (the home
dominates it). The certificate (`Tabs`, tables of lanes in blocks) gives each value its cell and shared
index, each shared value its home, block end, justification, and its neighbours at its cell in
home order (a list whose head the cell's owner lane names); each cell its owner; the fixed
constants; the anchors, by position. The walk (`Local.foldL`) visits positions in pre-order with
a state of two numbers: the next value number, the next anchor.
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

/-! ## Lanes -/

/-- Bits `[o, o + w)` of `x`. -/
def fld (x o w : ℕ) : ℕ := Nat.mod (Nat.shiftRight x o) (Nat.pow 2 w)

/-- Block `i` of a list of blocks (`0` past its end). -/
noncomputable def nthR (bs : List ℕ) (i : ℕ) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ → ℕ) (fun _ ↦ 0) (fun b _ r i ↦ bif Nat.beq i 0 then b else r (Nat.sub i 1)) bs i

/-- Group `i` of a list of groups (`[]` past its end). -/
noncomputable def nthG (gs : List (List ℕ)) (i : ℕ) : List ℕ :=
  List.rec (motive := fun _ ↦ ℕ → List ℕ) (fun _ ↦ []) (fun g _ r i ↦ bif Nat.beq i 0 then g else r (Nat.sub i 1)) gs i

/-- Lane `k` of a table of `w`-bit lanes, in blocks of `2^b` lanes, in groups of `2^c` blocks, the
key forced first. -/
noncomputable def tget (w b c : ℕ) (t : List (List ℕ)) (k : ℕ) : ℕ :=
  Local.seqN k fun k ↦ Local.seqN (Nat.shiftRight k b) fun i ↦
    fld (nthR (nthG t (Nat.shiftRight i c)) (Nat.mod i (Nat.pow 2 c))) (Nat.mul w (Nat.mod k (Nat.pow 2 b))) w

/-- The widths of the tables' lanes. -/
def wV : ℕ := 80
def wS : ℕ := 144
def wO : ℕ := 24
def wT : ℕ := 160
def wA : ℕ := 432

/-- A function's sharing certificate. -/
structure Tabs where
  /-- By value: cell (16 bits), shared index + 1 (18, `0` if not shared), and a shared value's
  home position (18), operand (8) and home block end (18). -/
  vl : List (List ℕ)
  /-- By shared index: cell, home position and operand, kind, the values before and after it at
  its cell in home order (value + 1, `0` if none), the cell's first home position, `aux`. -/
  sl : List (List ℕ)
  /-- By cell: kind (2 bits: `1` one value, `2` shared, `3` fixed constant), and the value (one
  value) or the first shared value + 1 (`0` if none). -/
  ot : List (List ℕ)
  /-- The fixed constants `(cell, limb 0, limb 1)`, `Plumb.stat`'s `PC.k` entries in order. -/
  st : List (List ℕ)
  /-- The anchors by position: position, block end, cell, operand, operation, constant or not,
  input cells (`packCells`), constant limbs. -/
  an : List (List ℕ)
  nst : ℕ
  nat : ℕ
  /-- The body's end, one past its last position (the body starting at `1`, the parameters at
  `0`). -/
  e : ℕ
  /-- The arms' ends, in the order the arms start. -/
  ends : List ℕ

/-! ### Fields -/

def sCell (s : ℕ) : ℕ := fld s 0 16
def sHp (s : ℕ) : ℕ := fld s 16 18
def sHj (s : ℕ) : ℕ := fld s 34 8
def sKind (s : ℕ) : ℕ := fld s 60 3
def sPrev (s : ℕ) : ℕ := fld s 63 18
def sNext (s : ℕ) : ℕ := fld s 81 18
def sHead (s : ℕ) : ℕ := fld s 99 18
def sAux (s : ℕ) : ℕ := fld s 117 20

def aP (a : ℕ) : ℕ := fld a 0 18
def aE (a : ℕ) : ℕ := fld a 18 18
def aCell (a : ℕ) : ℕ := fld a 36 16
def aJ (a : ℕ) : ℕ := fld a 52 8
def aOp (a : ℕ) : ℕ := fld a 60 16
def aConst (a : ℕ) : ℕ := fld a 76 1
def aIns (a : ℕ) : ℕ := fld a 80 224
def aK0 (a : ℕ) : ℕ := fld a 304 64
def aK1 (a : ℕ) : ℕ := fld a 368 64

def tO (x : ℕ) : ℕ := fld x 0 16
def tK0 (x : ℕ) : ℕ := fld x 16 64
def tK1 (x : ℕ) : ℕ := fld x 80 64

/-- A value's shared index + 1, home position, operand and home block end, from its lane. -/
def vSh (x : ℕ) : ℕ := fld x 16 18
def vHp (x : ℕ) : ℕ := fld x 34 18
def vHj (x : ℕ) : ℕ := fld x 52 8
def vSe (x : ℕ) : ℕ := fld x 60 18

/-- The kinds of justification. -/
def kRoot : ℕ := 0
def kEq : ℕ := 1
def kConstK : ℕ := 2
def kConstA : ℕ := 3
def kKey : ℕ := 4

/-! ## A statement's values -/

/-- `l ++ l'`, by the recursor. -/
noncomputable def appR {α : Type} (l l' : List α) : List α :=
  List.rec (motive := fun _ ↦ List α) l' (fun a _ r ↦ a :: r) l

theorem appR_eq {α : Type} (l l' : List α) : appR l l' = l ++ l' := by
  induction l with
  | nil => rfl
  | cons a l ih => show a :: appR l l' = _; rw [ih]; rfl

/-- An atom's values in numbering order (`Atom.vals`), lists joined by the recursor. -/
noncomputable def atomVals (a : Core.Atom) : List V :=
  match a with
  | .keccak ins outs _ _ => appR ins outs
  | .frameAddr p run => p :: run
  | a => a.vals

theorem atomVals_eq (a : Core.Atom) : atomVals a = a.vals := by
  cases a <;> simp [atomVals, appR_eq, Core.Atom.vals]

/-- The values a statement names at its own position, in numbering order (`Stmt.vals`). -/
noncomputable def ownVals : Stmt → List V
  | .atom a => atomVals a
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .call _ args rets => appR args rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: appR args rets
  | .ret vs => vs

/-- The constant operand `i` of an atom is given, as limbs. -/
noncomputable def constAt (a : Core.Atom) (i : ℕ) : Option (ℕ × ℕ) :=
  match a with
  | .const _ x => bif Nat.beq i 0 then some (limbNat x 0, limbNat x 1) else none
  | .assertNe _ _ _ => bif Nat.beq i 2 then some (1, 0) else none
  | _ => none

/-- The value operand `i` of a `copy` or `assert ==` equals. -/
def eqAt (a : Core.Atom) (i : ℕ) : Option V :=
  match a with
  | .copy d s => bif Nat.beq i 0 then some s else bif Nat.beq i 1 then some d else none
  | .assertEq x y => bif Nat.beq i 0 then some y else bif Nat.beq i 1 then some x else none
  | _ => none

/-- The key operand `i` of an atom is the output of: a sum (`0`), a product (`1`), a load at
offset `off` (`off + 56`), a `KECCAK` output cell (`keccakOp`), of the inputs given. -/
def keyAt (a : Core.Atom) (i : ℕ) : Option (ℕ × List V) :=
  match a with
  | .add d x y => bif Nat.beq i 0 then some (0, [x, y]) else bif Nat.beq i 1 then some (0, [d, y])
      else bif Nat.beq i 2 then some (0, [d, x]) else none
  | .mul _ x y => bif Nat.beq i 0 then some (1, [x, y]) else none
  | .load _ p off => bif Nat.beq i 0 then some (off + 56, [p]) else none
  | .keccak ins outs inOdd outOdd =>
      bif Nat.ble ins.length i && Nat.blt (i - ins.length) outs.length then
        some (keccakOp (i - ins.length) inOdd outOdd, ins) else none
  | _ => none

/-! ## The function's constants -/

/-- What the walk reads of the function besides the tables. -/
structure FnK where
  T : Tabs
  /-- The frame size. -/
  fs : ℕ
  /-- The next frame's cells a tail call's arguments may sit in. -/
  nx : List ℕ
  /-- The fixed frame pointer cells, the temporaries' cells (bit sets). -/
  fc : ℕ
  /-- The temporaries by cell, and the frame runs. -/
  tt : Trie ℕ
  runs : List (ℕ × ℕ)
  /-- A bound on every value's cell (`mainCells` in `main`). -/
  mb : ℕ
  /-- The number of values. -/
  nv : ℕ

section Walk

variable (K : FnK)

/-- Value `v`'s lane. -/
noncomputable def vlane (v : ℕ) : ℕ := tget wV 8 5 K.T.vl v

/-- Value `v`'s cell. -/
noncomputable def cellOf (v : ℕ) : ℕ := fld (vlane K v) 0 16

/-- Value `w`, an input of a home at operand `i` of position `q`, holds its cell's word by then:
in a cell of its own, or justified before (an earlier home, or a root earlier at `q`). -/
noncomputable def known (q i w : ℕ) : Bool :=
  natSeq (vlane K w) fun x ↦
    bif Nat.beq (vSh x) 0 then Nat.ble 2 (fld x 0 16)
    else natSeq (tget wS 6 5 K.T.sl (vSh x - 1)) fun s ↦
      Nat.ble 2 (sCell s) && (Nat.blt (sHp s) q || (Nat.beq (sHp s) q &&
        (Nat.beq (sKind s) kRoot || Nat.blt (sHj s) i)))

/-- A key's input cells, as the anchors pack them. -/
noncomputable def keyPack (op : ℕ) (ins : List V) : ℕ :=
  packCells (keyCells op (mapR (fun w ↦ cellOf K w.idx) ins))

/-- The justification of a shared home (lane `s`) at operand `i` of statement `st` at `q`, in
cell `c` whose owner lane is `o`. -/
noncomputable def justOk (st : Stmt) (q i c s o : ℕ) : Bool :=
  natSeq (sKind s) fun k ↦
  bif Nat.beq k kRoot then !Nat.beq (Nat.mod o 4) 3
  else match st with
  | .atom a =>
    bif Nat.beq k kEq then
      (match eqAt a i with
        | some u => natSeq (vlane K u.idx) fun x ↦
            !Nat.beq (vSh x) 0 && Nat.beq (fld x 0 16) c && known K q i u.idx
        | none => false)
    else bif Nat.beq k kConstK then
      (match constAt a i with
        | some y => natSeq (tget wT 6 5 K.T.st (sAux s)) fun t ↦
            Nat.blt (sAux s) K.T.nst && Nat.beq (tO t) c && Nat.beq (tK0 t) y.1 && Nat.beq (tK1 t) y.2
        | none => false)
    else bif Nat.beq k kConstA then
      (match constAt a i with
        | some y => natSeq (tget wA 4 5 K.T.an (sAux s)) fun an ↦
            Nat.blt (sAux s) K.T.nat && Nat.beq (aConst an) 1 && Nat.beq (aCell an) c &&
              Nat.beq (aK0 an) y.1 && Nat.beq (aK1 an) y.2 && Nat.blt (aP an) q && Nat.blt q (aE an)
        | none => false)
    else bif Nat.beq k kKey then
      (match keyAt a i with
        | some (op, ins) => natSeq (tget wA 4 5 K.T.an (sAux s)) fun an ↦
            Nat.blt (sAux s) K.T.nat && Nat.beq (aConst an) 0 && Nat.beq (aCell an) c &&
              Nat.beq (aOp an) op && Nat.beq (aIns an) (keyPack K op ins) &&
              Nat.blt (aP an) q && Nat.blt q (aE an) && allR (fun w ↦ known K q i w.idx) ins
        | none => false)
    else false
  | _ => false

/-- A shared home, of shared index `si` (+ 1) in cell `c` (owner lane `o`): its lane's home, its
place in its cell's list, its justification. -/
noncomputable def sharedOk (st : Stmt) (q i : ℕ) (cx : Ctx) (v c si o : ℕ) : Bool :=
  natSeq (tget wS 6 5 K.T.sl (si - 1)) fun s ↦
  Nat.beq (sCell s) c && Nat.beq (sHp s) q && Nat.beq (sHj s) i && Nat.ble 2 (Nat.mod o 4) &&
  (bif Nat.beq (sPrev s) 0 then Nat.beq (Nat.shiftRight o 2) (v + 1) && Nat.beq (sHead s) q
   else natSeq (sPrev s - 1) fun w ↦ Nat.blt w K.nv && natSeq (vlane K w) fun xw ↦ !Nat.beq (vSh xw) 0 &&
     natSeq (tget wS 6 5 K.T.sl (vSh xw - 1)) fun p ↦
     Nat.beq (sCell p) c && Nat.beq (sNext p) (v + 1) && Nat.beq (sHead p) (sHead s) &&
     (Nat.blt (sHp p) q || (Nat.beq (sHp p) q && Nat.blt (sHj p) i)) &&
     (bif Nat.beq (sKind s) kRoot then Nat.ble (cx.t + 1) (sHead s) && Nat.blt (sHp p) cx.a else true)) &&
  justOk K st q i c s o

/-- **A home**: value `v` (lane `x`) first occurs at operand `i` of statement `st` at `q`. Its
cell is in the frame or a tail call's next frame, below the bound, no fixed frame pointer's; a
cell of its own is owned by it, a shared one is justified. -/
noncomputable def homeOk (st : Stmt) (q i : ℕ) (cx : Ctx) (v x : ℕ) : Bool :=
  natSeq (fld x 0 16) fun c ↦
  (Nat.blt c K.fs || anyR (Nat.beq c) K.nx) && !bitN K.fc c && Nat.blt c K.mb &&
  (bif Nat.blt c 2 then Nat.beq (vSh x) 0
   else natSeq (tget wO 8 5 K.T.ot c) fun o ↦
     bif Nat.beq (vSh x) 0 then Nat.beq o (4 * v + 1)
     else Nat.beq (vHp x) q && Nat.beq (vHj x) i && Nat.beq (vSe x) cx.e &&
       sharedOk K st q i cx v c (vSh x) o)

/-- A value numbered before, shared with lane `x`: its home before operand `i` of `q`, its home's
block holding `q`. -/
noncomputable def covOk (q i n x : ℕ) : Option ℕ :=
  bif (Nat.blt (vHp x) q || (Nat.beq (vHp x) q && Nat.blt (vHj x) i)) && Nat.blt q (vSe x) then some n else none

/-- An occurrence of value number `v` (lane `x`), the next number `n`. -/
noncomputable def occN (st : Stmt) (q i : ℕ) (cx : Ctx) (v n x : ℕ) : Option ℕ :=
  bif Nat.beq v n then (bif homeOk K st q i cx v x then some (n + 1) else none)
  else bif Nat.blt v n then (bif Nat.beq (vSh x) 0 then some n else covOk q i n x)
  else none

/-- `v` is `V.n v.idx`. -/
def vnOk (v : V) : Bool := List.rec (motive := fun _ ↦ Bool) true (fun _ _ _ ↦ false) v.path && Nat.beq v.tag 0

/-- **An occurrence** of value `v` at operand `i` of statement `st` at `q`, the next number
`n`: a home (`v = n`), or a value numbered before, which, shared, has its home before and its
home's block holding `q`. Returns the next number. -/
noncomputable def occOk (st : Stmt) (q i : ℕ) (cx : Ctx) (v : V) (n : ℕ) : Option ℕ :=
  bif vnOk v then natSeq (vlane K v.idx) (occN K st q i cx v.idx n) else none

/-- The occurrences of a statement's values, from operand `i`. -/
noncomputable def occsOk (st : Stmt) (q : ℕ) (cx : Ctx) (vs : List V) : ℕ → ℕ → Option ℕ :=
  List.rec (motive := fun _ ↦ ℕ → ℕ → Option ℕ) (fun _ n ↦ some n)
    (fun v _ r i n ↦ Local.bindO (occOk K st q i cx v n) fun n ↦ r (i + 1) n) vs

/-- An anchor `an` is made by statement `st`: its operand `aJ` (in cell `aCell`, a shared one) is
given the constant, or is the key output of the operation on the input cells; its block ends at
`aE`. -/
noncomputable def anchorOk (st : Stmt) (cx : Ctx) (an : ℕ) : Bool :=
  match st with
  | .atom a =>
    Nat.beq (aE an) cx.e && Nat.ble 2 (aCell an) &&
    (match (atomVals a)[aJ an]? with
      | some w => Nat.beq (cellOf K w.idx) (aCell an)
      | none => false) &&
    (bif Nat.beq (aConst an) 1 then
      (match constAt a (aJ an) with
        | some y => Nat.beq (aK0 an) y.1 && Nat.beq (aK1 an) y.2
        | none => false)
     else match keyAt a (aJ an) with
      | some (op, ins) => Nat.beq (aOp an) op && Nat.beq (aIns an) (keyPack K op ins) &&
          allR (fun w ↦ Nat.ble 2 (cellOf K w.idx)) ins
      | none => false)
  | _ => false

/-- The anchors at position `q`, from anchor `k`: the next anchor not at `q` (at most `f` of
them). -/
noncomputable def anchorsOk (st : Stmt) (q : ℕ) (cx : Ctx) : ℕ → ℕ → Option ℕ :=
  fun f ↦ Nat.rec (motive := fun _ ↦ ℕ → Option ℕ) (fun k ↦ some k)
    (fun _ r k ↦ bif Nat.blt k K.T.nat then
        natSeq (tget wA 4 5 K.T.an k) fun an ↦
          bif Nat.beq (aP an) q then (bif anchorOk K st cx an then r (k + 1) else none) else some k
      else some k) f

/-- Temporaries and frame runs are listed with their cells (`atomListed`, cells from the
table). -/
noncomputable def listedOk : Stmt → Bool
  | .atom (.rangeCheck _ _ t1 t2 _) => listedT K.tt t1 (cellOf K t1.idx) && listedT K.tt t2 (cellOf K t2.idx)
  | .atom (.touch t _) => listedT K.tt t (cellOf K t.idx)
  | .atom (.frameAddr _ (r :: rs)) => runListedL (cellOf K r.idx) 0 (r :: rs)
  | _ => true
where
  /-- A frame run's values in consecutive cells from `base`, listed. -/
  runListedL (base : ℕ) : ℕ → List V → Bool
    | _, [] => true
    | k, v :: vs => Nat.beq (cellOf K v.idx) (base + k) && listed K.runs v (base + k) &&
        runListedL base (k + 1) vs

/-- **The step at a position**: its anchors, its listed temporaries and runs, its values'
occurrences. The state is the next value number and the next anchor. -/
noncomputable def step (st : ℕ × ℕ) (q : ℕ) (s : Stmt) (cx : Ctx) : Option (ℕ × ℕ) :=
  Local.bindO (anchorsOk K s q cx 32 st.2) fun k ↦
  bif listedOk K s then
    Local.bindO (occsOk K s q cx (ownVals s) 0 st.1) fun n ↦ Local.seqN n fun n ↦ Local.seqN k fun k ↦ some (n, k)
  else none

end Walk

/-! ## The function -/

/-- The fixed constants in the table, the fixed constant cells' owner lanes. -/
noncomputable def statOk (T : Tabs) (stat : List (ℕ × PC)) : Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun n ↦ Nat.beq n T.nst)
    (fun q _ r n ↦ match q.2 with
      | .k a b => natSeq (tget wT 6 5 T.st n) fun t ↦
          Nat.beq (tO t) q.1 && Nat.beq (tK0 t) a && Nat.beq (tK1 t) b &&
            Nat.beq (Nat.mod (tget wO 8 5 T.ot q.1) 4) 3 && Local.seqN (n + 1) r
      | .fpg _ => r n) stat 0

/-- The temporaries own their cells. -/
noncomputable def tmpsOk (T : Tabs) (tmps : List (ℕ × ℕ)) : Bool :=
  allR (fun p ↦ Nat.beq (tget wO 8 5 T.ot p.2) (4 * p.1 + 1)) tmps

/-- The table's cells are the certificate's (`Cert.locs`), value by value. -/
noncomputable def locsOk (T : Tabs) (locs : List ℕ) : Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun _ ↦ true)
    (fun c _ r v ↦ Nat.beq (fld (tget wV 8 5 T.vl v) 0 16) c && Local.seqN (v + 1) r) locs 0

/-- No value in the cells `cs` (their owner lanes empty). -/
noncomputable def freeOk (T : Tabs) (cs : List ℕ) : Bool :=
  allR (fun c ↦ Nat.ble 2 c && Nat.beq (tget wO 8 5 T.ot c) 0) cs

/-- The cells apart, as `apartOkD` without the values' cells, which `freeOk` keeps the call
sites' and table targets' cells apart from. -/
noncomputable def apartOkL (C : Cert) (P : Plumb) (main : Bool) (mc : ℕ) : Bool :=
  natSeq (Nat.lor (tmpCells P) (bitsOf (P.runs.map Prod.snd))) fun tr ↦
  natSeq (bitsOf (P.stat.map Prod.fst)) fun st ↦
  natSeq (Nat.lor tr st) fun trs ↦
  natSeq (bitsOf (siteCells P)) fun sc ↦
  natSeq (bitsOf (P.arms.map fun a ↦ a.2.1)) fun ac ↦
  apart st (tmpCells P) && apart sc trs && apart ac (Nat.lor trs sc) &&
    bitsNodup (P.stat.map Prod.fst) 0 && bitsNodup (siteCells P) 0 &&
    bitsNodup (P.arms.map fun a ↦ a.2.1) 0 &&
    C.facts.env.all (fun p ↦ P.stat.any fun q ↦ Nat.beq q.1 p.1 && q.2 == .fpg 0) &&
    (bif main then Nat.blt (Nat.lor trs (Nat.lor sc ac)) (2 ^ mc) else true)

/-- The function's constants for the walk. -/
noncomputable def fnK (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) (T : Tabs) :
    FnK :=
  ⟨T, fs, nextCells C.locs fs (tailArgs cf), fpgCells P, byCell P.tmps, P.runs,
    bif main then mc else 65536, C.locs.length⟩

/-- The parameters' occurrences, at position `0`. -/
noncomputable def paramsOk (K : FnK) (params : List V) : Option ℕ :=
  occsOk K (.ret params) 0 ⟨K.T.e, 0, 0⟩ params 0 0

/-! ## Pieces of a walk

A large function's walk is checked in pieces, each in its own kernel evaluation: statements
`[a, b)` of the body (`segL`), and arms `[a, b)` of a `match` of the body (`segHead`, `segArms`),
each from the position, state and arm end the previous one reaches. -/

/-- The walk of statements `[a, b)` of block `ss` (context `cx`), from position `p`, state `st`
and arm end `ea`, reaches position `p'`, state `st'` and arm end `eb`. -/
noncomputable def segL (K : FnK) (ss : List Stmt) (cx : Ctx) (a b p : ℕ) (st : ℕ × ℕ) (ea p' : ℕ)
    (st' : ℕ × ℕ) (eb : ℕ) : Bool :=
  match Local.foldL (step K) ((ss.drop a).take (b - a)) cx p st (K.T.ends.drop ea) with
  | some r => Nat.beq r.1 p' && Nat.beq r.2.1.1 st'.1 && Nat.beq r.2.1.2 st'.2 && r.2.2 == K.T.ends.drop eb
  | none => false

/-- Statement `m` of block `ss` is a `match`, and its own step at position `p` takes `st` to
`st'`. -/
noncomputable def segHead (K : FnK) (ss : List Stmt) (cx : Ctx) (m p : ℕ) (st st' : ℕ × ℕ) : Bool :=
  match (ss.drop m).head? with
  | some (.match_ x arms) => match step K st p (.match_ x arms) cx with
    | some r => Nat.beq r.1 st'.1 && Nat.beq r.2 st'.2
    | none => false
  | _ => false

/-- Statement `m` of block `ss` is a `match` at position `t`, and the walk of its arms `[a, b)`,
from position `pa`, state `st` and arm end `ea`, reaches position `pb`, state `st'` and arm end
`eb`. -/
noncomputable def segArms (K : FnK) (ss : List Stmt) (m t a b pa : ℕ) (st : ℕ × ℕ) (ea pb : ℕ)
    (st' : ℕ × ℕ) (eb : ℕ) : Bool :=
  match (ss.drop m).head? with
  | some (.match_ _ arms) =>
    match Local.foldA (step K) ((arms.drop a).take (b - a)) t pa st (K.T.ends.drop ea) with
    | some r => Nat.beq r.1 pb && Nat.beq r.2.1.1 st'.1 && Nat.beq r.2.1.2 st'.2 && r.2.2 == K.T.ends.drop eb
    | none => false
  | _ => false

/-- Statement `m` of block `ss` is a `match` of `n` arms. -/
noncomputable def segArity (ss : List Stmt) (m n : ℕ) : Bool :=
  match (ss.drop m).head? with
  | some (.match_ _ arms) => Nat.beq arms.length n
  | _ => false

/-- The once-per-function parts of the check. -/
noncomputable def staticL (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) (T : Tabs) : Bool :=
  listsOk P fs && apartOkL C P main mc && freeOk T (siteCells P) && freeOk T (P.arms.map fun a ↦ a.2.1) &&
  statOk T P.stat && tmpsOk T P.tmps && locsOk T C.locs &&
  allR (fun v ↦ Nat.blt (fld (tget wV 8 5 T.vl v.idx) 0 16) fs) cf.params

/-- The walk of the parameters and the body. -/
noncomputable def walkL (K : FnK) (cf : Core.Fn) : Bool :=
  match paramsOk K cf.params with
  | some n => segL K cf.body ⟨K.T.e, 0, 0⟩ 0 cf.body.length 1 (n, 0) 0 K.T.e (K.nv, K.T.nat) K.T.ends.length
  | none => false

/-- **The sharing check of a function**, of core IR `cf`, certificate `C`, completeness data
`P`, frame size `fs`, with its sharing certificate `T`. -/
noncomputable def shareCheckL (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ)
    (T : Tabs) : Bool :=
  staticL cf C P fs main mc T && walkL (fnK cf C P fs main mc T) cf

end
end LeanVM.Guest.B2C.ShareL
