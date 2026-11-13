/-
  LeanVM.Guest.B2C.CplCheck

  B2's completeness check of one compiled function, from its own data and its view of the
  program: its code runs from its entry to its return on a memory whose frame holds what the
  honest memory puts there, window by window of its soundness certificate.
-/

module

public import LeanVM.Guest.CheckView
public import LeanVM.Guest.B2C.Types
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Renumber

/-!
# The completeness check

`cplWinD`: the check of part `k` of window `i` of a function given by its data, the walk of its
statements against its code (`cplResD`), which the kernel evaluates (`Pack/*/Cplw*`); `CplOkD`,
every part of every window. The check reads the program only as the function's callees see it
(`cxOfD`, `cplWinD_congr`), so a check over the function's own view (`Check.Glob.ofSigs`) is the
check over the whole program's (`Cpl.lean`). This module imports none of the guest's data
(`CplFirewall.lean`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-! ## A window's cells

A window's cells packed in one number, base `2^16` (as `B2C.Share`'s `Loc`): those of the values
`lo, …, lo + len - 1`, and those of the other values its statements name. -/

/-- The cells of a list packed, cell `m` in the `m`-th base-`2^16` digit. -/
def packC : List ℕ → ℕ
  | [] => 0
  | c :: cs => Nat.add c (Nat.mul (packC cs) 65536)

/-- The cell `(value, cell, window)` entries give value `v`. -/
def insC (v : ℕ) : List (ℕ × ℕ × ℕ) → Option ℕ
  | [] => none
  | p :: ps => bif Nat.beq p.1 v then some p.2.1 else insC v ps

/-- A window's cells. -/
structure CLoc where
  lo : ℕ
  len : ℕ
  pk : ℕ
  ins : List (ℕ × ℕ × ℕ)

/-- The cell of value number `v`, if the window has it. -/
def CLoc.get? (L : CLoc) (v : ℕ) : Option ℕ :=
  bif Nat.ble L.lo v && Nat.blt v (Nat.add L.lo L.len) then
    some (Nat.mod (Nat.div L.pk (Nat.pow 65536 (Nat.sub v L.lo))) 65536)
  else insC v L.ins

/-- The cell of a value (`0` if the window has none). -/
def CLoc.cell (L : CLoc) (v : V) : ℕ := (L.get? v.idx).getD 0

/-- `k L`, its packed cells evaluated first. -/
def CLoc.seq {β : Type} (L : CLoc) (k : CLoc → β) : β :=
  match L with
  | ⟨lo, len, pk, ins⟩ => natSeq lo fun lo ↦ natSeq len fun len ↦ natSeq pk fun pk ↦ k ⟨lo, len, pk, ins⟩

theorem CLoc.seq_eq {β : Type} (L : CLoc) (k : CLoc → β) : L.seq k = k L := by
  cases L
  simp only [CLoc.seq, natSeq_eq]

/-- Window `i`'s cells in certificate `C`. -/
def clocW (C : Cert) (i : ℕ) : CLoc :=
  ⟨listElementOrDefault C.los i 0, (listElementOrDefault C.cells i []).length, packC
      (listElementOrDefault C.cells i []), listElementOrDefault C.ins i []⟩

/-! ## Counts -/

/-- Instructions of each opcode. -/
structure Cnt where
  x : ℕ
  m : ℕ
  s : ℕ
  d : ℕ
  j : ℕ
  /-- `KECCAK`s. -/
  kc : ℕ

/-- The count of an opcode. -/
def Cnt.get (c : Cnt) : Opcode → ℕ
  | .xor => c.x
  | .mulNative => c.m
  | .setConstant => c.s
  | .deref => c.d
  | .jump => c.j
  | .keccak => c.kc

/-- `k c`, its counts evaluated first. -/
def Cnt.seq {β : Type} (c : Cnt) (k : Cnt → β) : β :=
  match c with
  | ⟨x, m, s, d, j, kc⟩ => natSeq x fun x ↦ natSeq m fun m ↦ natSeq s fun s ↦ natSeq d fun d ↦
      natSeq j fun j ↦ natSeq kc fun kc ↦ k ⟨x, m, s, d, j, kc⟩

theorem Cnt.seq_eq {β : Type} (c : Cnt) (k : Cnt → β) : c.seq k = k c := by
  cases c
  simp only [Cnt.seq, natSeq_eq]

/-- One more instruction of `ins`'s opcode. -/
def Cnt.bump (c : Cnt) : OffsetInstruction → Cnt
  | .xor .. => { c with x := c.x + 1 }
  | .mul .. => { c with m := c.m + 1 }
  | .set .. => { c with s := c.s + 1 }
  | .deref .. => { c with d := c.d + 1 }
  | .jump .. => { c with j := c.j + 1 }
  | .keccak .. => { c with kc := c.kc + 1 }

/-- One more `JUMP`. -/
def Cnt.bumpJ (c : Cnt) : Cnt := { c with j := c.j + 1 }

/-- The larger counts. -/
def Cnt.max (c c' : Cnt) : Cnt :=
  ⟨Nat.max c.x c'.x, Nat.max c.m c'.m, Nat.max c.s c'.s, Nat.max c.d c'.d, Nat.max c.j c'.j,
    Nat.max c.kc c'.kc⟩

/-- Every count at most the other's. -/
def Cnt.le (c c' : Cnt) : Bool :=
  Nat.ble c.x c'.x && Nat.ble c.m c'.m && Nat.ble c.s c'.s && Nat.ble c.d c'.d && Nat.ble c.j c'.j &&
    Nat.ble c.kc c'.kc

/-- Counts from a list in `Opcode`'s order. -/
def Cnt.ofList (l : List ℕ) : Cnt := ⟨listElementOrDefault l 0 0, listElementOrDefault l 1 0, listElementOrDefault l 2 0, listElementOrDefault l 3 0, listElementOrDefault l 4 0, listElementOrDefault l 5 0⟩

/-- No instructions. -/
def Cnt.zero : Cnt := ⟨0, 0, 0, 0, 0, 0⟩

/-! ## Facts on the frame

The atoms of the path, on their cells (`Check.LAtom`), filed under the cells the check looks
them up by. -/

/-- The cells a fact is filed under. -/
def keysC : LAtom → List ℕ
  | .const d _ => [d]
  | .add d _ _ => [d]
  | .mul d _ _ => [d]
  | .same a b => [a, b]
  | .load d _ _ => [d]
  | .ne _ _ p => [p]
  | .range x y _ _ _ => [x, y]
  | .inK a b => [a, b]
  | .keccak _ outs _ _ => outs.take 1
  | .addr p _ => [p]
  | .none => []

/-- The cells of a fact, which must lie in the frame past the header. -/
def cellsC : LAtom → List ℕ
  | .const d _ => [d]
  | .add d a b => [d, a, b]
  | .mul d a b => [d, a, b]
  | .same a b => [a, b]
  | .load d p _ => [d, p]
  | .ne x i p => [x, i, p]
  | .range x y t1 t2 k => [x, y, t1, t2, k]
  | .inK a b => [a, b]
  | .keccak ins outs _ _ => ins ++ outs
  | .addr p run => p :: run.take 1
  | .none => []

/-- Every cell in `[2, n)`. -/
def inFrame (n : ℕ) : List ℕ → Bool
  | [] => true
  | c :: cs => Nat.ble 2 c && Nat.blt c n && inFrame n cs

/-- The cells of a core atom in a window. -/
def locC (L : CLoc) : Core.Atom → LAtom
  | .const d x => .const (L.cell d) x
  | .add d a b => .add (L.cell d) (L.cell a) (L.cell b)
  | .mul d a b => .mul (L.cell d) (L.cell a) (L.cell b)
  | .copy d s => .same (L.cell d) (L.cell s)
  | .load d p off => .load (L.cell d) (L.cell p) off
  | .assertEq a b => .same (L.cell a) (L.cell b)
  | .assertNe x i p => .ne (L.cell x) (L.cell i) (L.cell p)
  | .rangeCheck x y t1 t2 k => .range (L.cell x) (L.cell y) (L.cell t1) (L.cell t2) (L.cell k)
  | .assertInK a b => .inK (L.cell a) (L.cell b)
  | .keccak ins outs inOdd outOdd => .keccak (ins.map L.cell) (outs.map L.cell) inOdd outOdd
  | .frameAddr p (r :: rs) => .addr (L.cell p) ((r :: rs).map L.cell)
  | .frameAddr _ [] => .none
  | .hint _ => .none
  | .touch t p => .load (L.cell t) (L.cell p) 0

/-- The facts by cell. -/
abbrev BookC := Trie (List LAtom)

/-- The facts filed under a cell. -/
noncomputable def lookC (B : BookC) (o : ℕ) : List LAtom := (getF B o).getD []

/-- File `a` under `o`. -/
noncomputable def addKeyC (a : LAtom) (B : BookC) (o : ℕ) : BookC :=
  optSeq (getF B o) fun l ↦ setF (a :: l.getD []) envDepth B o

/-- File a fact under its keys. -/
noncomputable def fileC (B : BookC) (a : LAtom) : BookC := (keysC a).foldl (addKeyC a) B

/-- File the atoms of a block's statements (not those of nested blocks), those whose cells lie in
the frame. -/
noncomputable def fileB (L : CLoc) (n : ℕ) : List Core.Stmt → BookC → BookC
  | [], B => B
  | .atom a :: ss, B => (locC L a).seq fun la ↦
      bif inFrame n (cellsC la) then (fileC B la).seq fun B ↦ fileB L n ss B else fileB L n ss B
  | _ :: ss, B => fileB L n ss B

/-! ## Frames in flight -/

/-- What a callee frame cell holds: the caller's cell `c`, the callee frame pointer, the
caller's frame pointer, `g^r`, the caller's header cell `i`. -/
inductive FC where
  | val (c : ℕ)
  | self
  | fp
  | pc (r : ℕ)
  | hdr (i : ℕ)
  deriving DecidableEq

/-- The arguments' (or returns') cells at a callee frame from offset `o`. -/
def argFC (L : CLoc) : ℕ → List V → List (ℕ × FC)
  | _, [] => []
  | o, v :: vs => (o, .val (L.cell v)) :: argFC L (o + 1) vs

/-! ## The check's context and position -/

/-- The context of a window's completeness walk. -/
structure CX where
  G : Glob
  F : Exec.Facts
  entry : ℕ
  idx : Trie Exec.Seg
  loc : CLoc
  /-- The frame size. -/
  fs : ℕ
  /-- The fixed cells in `[2, fs)`. -/
  stat : Trie PC
  main : Bool
  name : String
  nargs : ℕ
  nret : ℕ
  callees : List ℕ
  sites : List Site
  arms : List (ℕ × ℕ × ℕ)
  /-- The function's self frame pointer cells. -/
  self : List ℕ
  /-- The most instructions a path runs. -/
  pmax : Cnt
  /-- The renumbered values the body's top-level atoms name (a bit set by number). -/
  nv : ℕ
  /-- Where the part stops inside a segment: the segment's start and the items passed. -/
  stop : Option (ℕ × ℕ)
  /-- The `match`es whose arms are counted separately, by selector, with their arms' counts. -/
  acs : List (ℕ × List (List ℕ))
  /-- The chained `match`es (`Plumb.chains`). -/
  chains : List (ℕ × ℕ × List ℕ × ℕ × ℕ)

/-- A position of the walk: a segment and its items not yet passed, the facts, the callee frames
in flight `(cell, its cells)`, the table reads `(target, selector, base)`, the next frame of a
tail call, the instructions passed on the path, the cells of the callee frame pointers and
dispatch targets set up on the path (a bit set), and `fresh = some t` at the start of segment `t`
before any item is passed. -/
structure CW where
  seg : Exec.Seg
  its : List Exec.Item
  book : BookC
  fr : List (ℕ × List (ℕ × FC))
  tg : List (ℕ × ℕ × ℕ)
  nx : List (ℕ × FC)
  cnt : Cnt
  uq : ℕ
  fresh : Option ℕ
  /-- The renumbered values `V.n k` the atoms walked in the enclosing blocks name, as bits. -/
  nm : ℕ

/-! ## Justifying instructions -/

section Just

variable (X : CX) (st : CW)

/-- A fixed cell. -/
noncomputable def statAt (o : ℕ) : Option PC := getF X.stat o

/-- The exponent of the `SET` immediate `(k0, 0)` as a power of `g`. -/
noncomputable def gpE (k0 : ℕ) : Option ℕ := bif Nat.beq k0 1 then some 0 else X.F.pows.find k0

/-- The constant a cell holds: a fixed cell's, a constant's, an `assert !=`'s `1`. -/
noncomputable def cplCstAt (o : ℕ) : Option (ℕ × ℕ) :=
  match statAt X o with
  | some (.k k0 k1) => some (k0, k1)
  | _ => (lookC st.book o).findSome? fun a ↦ match a with
    | .const d x => bif Nat.beq d o then some (limbNat x 0, limbNat x 1) else none
    | .ne _ _ p => bif Nat.beq p o then some (1, 0) else none
    | _ => none

/-- The cell holds `0`: a constant, or the segment's environment. -/
noncomputable def isZ (o : ℕ) : Bool :=
  (match cplCstAt X st o with
    | some (0, 0) => true
    | _ => false) || isZero (st.seg.env.get o)

/-- The cell holds `1`: a constant, or the segment's environment. -/
noncomputable def isO (o : ℕ) : Bool :=
  (match cplCstAt X st o with
    | some (1, 0) => true
    | _ => false) || isOne (st.seg.env.get o)

/-- The cell holds a word: the header, a fixed cell, a fact's. -/
noncomputable def known (o : ℕ) : Bool :=
  Nat.ble o 1 || (statAt X o).isSome || !(lookC st.book o).isEmpty

/-- Two cells hold one word. -/
noncomputable def sameC (a b : ℕ) : Bool :=
  (Nat.beq a b && known X st a) || (lookC st.book a).any fun x ↦ match x with
    | .same u w => (Nat.beq u a && Nat.beq w b) || (Nat.beq u b && Nat.beq w a)
    | _ => false

/-- The cell holds `0` by an `assert ==` with a cell holding `0`. -/
noncomputable def zeroBy (a : ℕ) : Bool :=
  (lookC st.book a).any fun x ↦ match x with
    | .same u w => (Nat.beq u a && isZ X st w) || (Nat.beq w a && isZ X st u)
    | _ => false

/-- A sum filed under `c` over a permutation of the cells `a, b, d`. -/
noncomputable def addAt (a b d c : ℕ) : Bool :=
  (lookC st.book c).any fun x ↦ match x with
    | .add d' x y => perm3 a b d d' x y
    | _ => false

/-- `{x, y} = {a, b}`. -/
def pairEq (x y a b : ℕ) : Bool := (Nat.beq x a && Nat.beq y b) || (Nat.beq x b && Nat.beq y a)

/-- The cell holds a word of `K`: the header but in `main`, a fixed cell, a fact's, a callee
frame pointer, a table read's target, a cell the segment's environment knows. -/
noncomputable def cellK (o : ℕ) : Bool :=
  (Nat.ble o 1 && !X.main) ||
  (match statAt X o with
    | some (.k _ k1) => Nat.beq k1 0
    | some (.fpg _) => true
    | none => false) ||
  (lookC st.book o).any (fun x ↦ match x with
    | .const d x => Nat.beq d o && Nat.beq (limbNat x 1) 0
    | .range x y _ _ _ => Nat.beq x o || Nat.beq y o
    | .inK a b => Nat.beq a o || Nat.beq b o
    | .addr p _ => Nat.beq p o
    | .ne _ _ p => Nat.beq p o
    | _ => false) ||
  st.fr.any (fun q ↦ Nat.beq q.1 o) || st.tg.any (fun t ↦ Nat.beq t.1 o) ||
  (st.seg.env.get o).isSome

/-- `fp[a] = fp·g^e`: a fixed cell, or the address of a run starting at cell `e` (an `addr` fact,
from which the compiler steps a shifted one). -/
noncomputable def fpgAtC (a : ℕ) : Option ℕ :=
  match statAt X a with
  | some (.fpg e) => some e
  | _ => (lookC st.book a).findSome? fun x ↦ match x with
    | .addr p (r :: _) => bif Nat.beq p a then some r else none
    | _ => none

/-- A `MUL` of a frame address: `fp[a] = fp·g^e₁`, `fp[b] = g^e₂`, the run at `e₁ + e₂`. -/
noncomputable def addrMul (a b : ℕ) (run : List ℕ) : Bool :=
  match fpgAtC X st a, cplCstAt X st b, run with
  | some e1, some (k0, 0), r :: _ => match gpE X k0 with
    | some e2 => Nat.beq (e1 + e2) r
    | none => false
  | _, _, _ => false

/-- A `MUL` of fixed cells: `fp·g^e = fp·g^e₁ · g^(e - e₁)`. -/
noncomputable def fpgMul (a b d : ℕ) : Bool :=
  match statAt X d, statAt X a, cplCstAt X st b with
  | some (.fpg e), some (.fpg e1), some (k0, 0) => Nat.ble e1 e && (match gpE X k0 with
    | some e2 => Nat.beq e2 (e - e1)
    | none => false)
  | _, _, _ => false

/-- A copy into the next frame's cell `o`. -/
noncomputable def nextMul (a o : ℕ) : Bool :=
  match st.nx.find? (fun p ↦ Nat.beq p.1 o) with
  | some (_, .val cv) => Nat.beq a cv || sameC X st a cv
  | some (_, .hdr i) => Nat.beq a i && Nat.ble i 1
  | some (_, .self) => decide (statAt X a = some (.fpg X.fs))
  | _ => false

/-- A store into or load from a callee frame through its pointer cell `o1`. -/
noncomputable def frameCell (o1 o2 o3 : ℕ) : Bool :=
  match st.fr.find? (fun q ↦ Nat.beq q.1 o1) with
  | some (_, fcs) => fcs.any fun p ↦ Nat.beq p.1 o2 && (match p.2 with
    | .val cv => Nat.beq cv o3 || sameC X st cv o3
    | .self => Nat.beq o3 o1
    | .pc r => (match cplCstAt X st o3 with
      | some (k0, 0) => decide (gpE X k0 = some r)
      | _ => false)
    | _ => false)
  | none => false

/-- A callee frame's cell `o2` holds `fc`. -/
noncomputable def frameHas (o1 o2 : ℕ) (fc : FC) : Bool :=
  match st.fr.find? (fun q ↦ Nat.beq q.1 o1) with
  | some (_, fcs) => fcs.any fun p ↦ Nat.beq p.1 o2 && decide (p.2 = fc)
  | none => false

/-- **An instruction at pc `pc` holds** on the frame: by a fact on its cells, the fixed cells,
a callee frame in flight, a table read, or the next frame. -/
noncomputable def justI (pc : ℕ) : OffsetInstruction → Bool
  | .set o k0 k1 => decide (cplCstAt X st o = some (k0, k1))
  | .xor a b d =>
    addAt st a b d d || addAt st a b d a || addAt st a b d b ||
    (isZ X st d && sameC X st a b) || (Nat.beq a d && isZ X st b && known X st d) ||
    (Nat.beq b d && isZ X st a && known X st d) || (Nat.beq b d && known X st d && zeroBy X st a)
  | .mul a b d =>
    (lookC st.book d).any (fun x ↦ match x with
      | .mul d' x y => Nat.beq d' d && pairEq x y a b
      | .ne x i p => Nat.beq p d && pairEq x i a b
      | .addr p run => Nat.beq p d && addrMul X st a b run
      | _ => false) ||
    (lookC st.book a).any (fun x ↦ match x with
      | .range x y _ _ k => Nat.beq k d && pairEq x y a b
      | _ => false) ||
    (isO X st b && sameC X st a d) || (isO X st a && sameC X st b d) || fpgMul X st a b d ||
    (Nat.ble X.fs d && isO X st b && nextMul X st a (d - X.fs))
  | .deref o1 o2 o3 .cell =>
    (lookC st.book o3).any (fun x ↦ match x with
      | .load d p off => Nat.beq d o3 && Nat.beq p o1 && Nat.beq off o2
      | _ => false) ||
    (lookC st.book o1).any (fun x ↦ match x with
      | .range x y t1 t2 _ => Nat.beq o2 0 && ((Nat.beq x o1 && Nat.beq t1 o3) ||
          (Nat.beq y o1 && Nat.beq t2 o3))
      | _ => false) ||
    frameCell X st o1 o2 o3 ||
    st.tg.any (fun t ↦ Nat.beq t.1 o3 && Nat.beq t.2.1 o1 && Nat.beq t.2.2 o2) ||
    (Nat.beq o2 0 && decide (statAt X o1 = some (.fpg o3)) && known X st o3)
  | .deref o1 o2 o3 .fp =>
    known X st o3 && (frameHas st o1 o2 .fp ||
      (Nat.beq o2 0 && (match statAt X o1 with
        | some (.fpg x) => decide (statAt X x = some (.fpg 0))
        | _ => false)))
  | .deref o1 o2 o3 .pc => known X st o3 && frameHas st o1 o2 (.pc (pc + 2))
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oC =>
    (lookC st.book out).any fun x ↦ match x with
      | .keccak ins outs iO oO => ins == keccakIns m0 m1 m2 m3 tail b8 cap &&
          outs == keccakOuts out oC.cellCount && iO == inOdd && oO == outOdd
      | _ => false
  | .jump .. => false

/-- Pass items, each justified and counted, up to the next branch or the end. -/
noncomputable def passL : List Exec.Item → Cnt → Except ℕ (List Exec.Item × Cnt)
  | [], c => .ok ([], c)
  | .ins (.instr pc ins) :: its, c =>
      bif justI X st pc ins then (c.bump ins).seq fun c ↦ passL its c else .error pc
  | .ins (.jump oc od of) :: its, c =>
      bif cellK X st oc && cellK X st od && cellK X st of then c.bumpJ.seq fun c ↦ passL its c
      else .error (3 + 4 * oc)
  | .ins _ :: _, _ => .error 2
  | .fact _ :: its, c => passL its c
  | .branch oc od of x :: its, c => .ok (.branch oc od of x :: its, c)

end Just

/-! ## Moving along the segments -/

section Move

variable (X : CX)

/-- The start of segment `t`, with the facts, frames, reads and counts of `st`. -/
noncomputable def segAtC (t : ℕ) (st : CW) : Option CW :=
  match getF X.idx t with
  | some s => bif Nat.beq s.start t then
      some ⟨s, s.items, st.book, st.fr, st.tg, st.nx, st.cnt, st.uq, some t, st.nm⟩ else none
  | none => none

/-- The position at the end of the segment, its items passed, if no branch is before it. -/
noncomputable def endAtC (st : CW) : Except ℕ CW :=
  match passL X st st.its st.cnt with
  | .ok ([], c) => c.seq fun c ↦ .ok ⟨st.seg, [], st.book, st.fr, st.tg, st.nx, c, st.uq, none, st.nm⟩
  | .ok _ => .error 5
  | .error e => .error e

/-- The next branch, the items before it passed: the position after it, its cells and exit. -/
noncomputable def brAtC (st : CW) : Except ℕ (CW × ℕ × ℕ × ℕ × Exec.Exit) :=
  match passL X st st.its st.cnt with
  | .ok (.branch oc od of x :: its, c) => c.bumpJ.seq fun c ↦
      .ok (⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c, st.uq, none, st.nm⟩, oc, od, of, x)
  | .ok _ => .error 6
  | .error e => .error e

/-- The next branch's cells and exit, nothing passed. -/
def peekBr : List Exec.Item → Option (ℕ × Exec.Exit)
  | [] => none
  | .branch oc _ _ x :: _ => some (oc, x)
  | _ :: its => peekBr its

/-- The table read into `t` among the items: its selector cell and base. -/
def tblRead (t : ℕ) : List Exec.Item → Option (ℕ × ℕ)
  | [] => none
  | .ins (.instr _ (.deref o1 o2 o3 .cell)) :: its =>
      bif Nat.beq o3 t then some (o1, o2) else tblRead t its
  | _ :: its => tblRead t its

end Move

/-! ## The walk -/

/-- Bit `n` of `s`. -/
def bitK (s n : ℕ) : Bool := Nat.beq (Nat.mod (Nat.shiftRight s n) 2) 1

/-- `s` with bit `n` set. -/
def setK (s n : ℕ) : ℕ := Nat.lor s (Nat.shiftLeft 1 n)

/-- Every bit of `s` is one of `t`'s. -/
def subK (s t : ℕ) : Bool := Nat.beq (Nat.land s t) s

/-- How a block's walk ends: at a join with the counts of the path there (the most of any), by
the return, in a chained `match`'s table jump into the arms `succ` through the selector in cell
`o`, or not at all (with a code saying where). -/
inductive RC where
  | join (J : ℕ) (c : Cnt) (u : ℕ)
  /-- In a table jump through slot `log fp[o]` into the arms `succ` of the next `match`. -/
  | chain (o : ℕ) (succ : List ℕ) (c : Cnt) (u : ℕ)
  /-- Inside the segment starting at `J`, its first `m` items passed. -/
  | mid (J m : ℕ) (c : Cnt) (u : ℕ)
  | done
  | fail (code : ℕ)

section Walk

variable (X : CX)

/-- The callee at `pc`, with what a caller knows of it: the first of the function's callees
entered there, a good one. -/
noncomputable def calleeS (pc : ℕ) : Option (ℕ × Sig) :=
  (X.callees.find? fun j ↦ X.G.good j && Nat.beq (X.G.sig j).entry pc).map fun j ↦ (j, X.G.sig j)

/-- The callee at `pc`. -/
noncomputable def calleeC (pc : ℕ) : Option ℕ := (calleeS X pc).map Prod.fst

/-- The renumbered values `V.n k` a value list names, set in `s`. -/
def nvVals : List V → ℕ → ℕ
  | [], s => s
  | v :: vs, s => bif v.path.isEmpty && Nat.beq v.tag 0 then natSeq (setK s v.idx) fun s ↦ nvVals vs s
    else nvVals vs s

/-- The arms' counts of the `match` on `x`, if counted separately. -/
def armKeyD (acs : List (ℕ × List (List ℕ))) (x : ℕ) : Option (List Cnt) :=
  (armRaw acs x).map fun cs ↦ cs.map Cnt.ofList

/-- Arm `k` within its count, if counted separately. -/
def armChkK (key : Option (List Cnt)) (k : ℕ) (c : Cnt) : Bool :=
  match key with
  | some cs => c.le (listElementOrDefault cs k Cnt.zero)
  | none => true

/-- The position the arms start from: the counts restarted if the arms are counted separately. -/
def armSt (key : Option (List Cnt)) (se : CW) : CW :=
  match key with
  | some _ => { se with cnt := Cnt.zero }
  | none => se

/-- The counts after the arms: those at the jump if counted separately, else the arms' most. -/
def armCnt (key : Option (List Cnt)) (se : CW) (c : Cnt) : Cnt :=
  match key with
  | some _ => se.cnt
  | none => c

/-- A selector the path names: a parameter, a value of one of the body's atoms, or of one of the
atoms walked, or calls returned from, in the enclosing blocks. -/
def selOk (st : CW) (v : V) : Bool := Nat.blt v.idx X.nargs || bitK X.nv v.idx || bitK st.nm v.idx

/-- The call site of a call with these argument and return values (`siteOf`). -/
def siteC (args rets : List V) : Option Site :=
  X.sites.find? fun s ↦ s.args == args.map (·.idx) && s.rets == rets.map (·.idx)

/-- The call site is the code's: its callee frame pointer cell, return pc and dispatch target
cell. -/
def siteOk (args rets : List V) (q r t : ℕ) : Bool :=
  match siteC X args rets with
  | some s => Nat.beq s.q q && Nat.beq s.r r && Nat.beq s.tgt t
  | none => false

/-- Slot `base + k` of the jump table holds the entry of the callee named `fs[k]`, of arity
`na`, returning `nr` words. -/
noncomputable def tcOk (base na nr : ℕ) : ℕ → List String → Bool
  | _, [] => true
  | k, f :: fs => (match X.G.jt.get (base + k) with
      | some pc => match calleeS X pc with
        | some (_, sg) => f == sg.name && Nat.beq sg.nargs na && Nat.beq sg.nret nr
        | none => false
      | none => false) && tcOk base na nr (k + 1) fs

/-- A callee frame's cells: the arguments, the self frame pointer cells, the caller's frame
pointer and the return pc. -/
def callFC (args : List V) (self : List ℕ) (r : ℕ) : List (ℕ × FC) :=
  argFC X.loc 2 args ++ self.map (fun o ↦ (o, FC.self)) ++ [(1, .fp), (0, .pc r)]

/-- The table read `(selector cell, base)` into target cell `t`, among the walk's. -/
def tgAt (tg : List (ℕ × ℕ × ℕ)) (t : ℕ) : Option (ℕ × ℕ) := (tg.find? fun q ↦ Nat.beq q.1 t).map Prod.snd

/-- The end of a block in a chained `match`'s table jump, at the segment's end `se`: the jump
through cell `t`, the frame kept, read from a table at `b` through the selector in cell `o`
(the walk's table reads), whose slots hold the arms `succ`. -/
noncomputable def chainEnd (se : CW) (t : ℕ) (ft : Tgt) : RC :=
  match se.seg.exit.succ with
  | [] => .fail 2
  | t0 :: ts => match tgAt se.tg t with
    | some (o, b) => bif X.F.self ft && armsOk X.G X.entry b 0 (t0 :: ts) then
        .chain o (t0 :: ts) se.cnt se.uq else .fail 8
    | none => .fail 9

/-- The chained `match` on value number `x`, if any: its arms' targets, the next selector and
table base. -/
def chainOf (x : ℕ) : Option (List ℕ × ℕ × ℕ) :=
  (X.chains.find? fun ch ↦ Nat.beq ch.2.1 x).map fun ch ↦ ch.2.2

/-- The table read arm `k` of the `match` on `v` sets up, if the `match` is chained: into its
target cell, through the next selector's cell, from the next table. -/
noncomputable def armTg (v : V) (k : ℕ) : List (ℕ × ℕ × ℕ) :=
  match chainOf X v.idx with
  | some (ts, y, b) => [(listElementOrDefault ts k 0, X.loc.cell (V.n y), b)]
  | none => []

/-- A chained `match` on `v` of `n` arms: one target per arm, in the frame, the next selector a
value the path names, in the frame. -/
noncomputable def chainPre (st : CW) (v : V) (n : ℕ) : Bool :=
  match chainOf X v.idx with
  | some (ts, y, _) => Nat.beq ts.length n && selOk X st (V.n y) &&
      inFrame X.fs (X.loc.cell (V.n y) :: ts)
  | none => true

/-- How an arm of a `match` must end, as its first: at the join `J` (`succ = []`), or in the next
`match`'s table jump through the selector in cell `J` into the arms `succ`; its counts and set-up
cells. -/
def armEnd (J : ℕ) (succ : List ℕ) : RC → Option (Cnt × ℕ)
  | .join J' c u => bif succ.isEmpty && Nat.beq J J' then some (c, u) else none
  | .chain o succ' c u => bif !succ.isEmpty && Nat.beq J o && succ == succ' then some (c, u) else none
  | _ => none

/-- Where a block ends: at the start of a segment, at the part's stop inside its segment, by
its segment's local jump, or in a chained `match`'s table jump. -/
noncomputable def endC (st : CW) : RC :=
  match st.fresh with
  | some t => .join t st.cnt st.uq
  | none => match X.stop with
    | some (J, m) =>
      bif Nat.beq st.seg.start J && Nat.ble m st.seg.items.length &&
          Nat.ble (st.seg.items.length - m) st.its.length then
        match passL X st (st.its.take (st.its.length - (st.seg.items.length - m))) st.cnt with
        | .ok ([], c) => c.seq fun c ↦ .mid J m c st.uq
        | _ => .fail 3
      else .fail 4
    | none => match endAtC X st with
      | .ok se => match se.seg.exit.kind with
        | .next t => bif se.seg.exit.succ == [t] then .join t se.cnt se.uq else .fail 1
        | .jump (.cell t) ft => chainEnd X se t ft
        | _ => .fail 2
      | .error e => .fail e

/-- After a call into the frame `fp[q]` returning to `r`: the position at the return point, its
callee frame's returns known. -/
noncomputable def afterC (st : CW) (q r u : ℕ) (fcs : List (ℕ × FC)) (args rets : List V) :
    Except ℕ CW :=
  match endAtC X { st with fr := (q, fcs) :: st.fr } with
  | .ok se => match segAtC X (r - X.entry) se with
    | some sr => .ok ⟨sr.seg, sr.its, sr.book, (q, fcs ++ argFC X.loc (2 + args.length) rets) :: st.fr,
        sr.tg, sr.nx, sr.cnt, u, bif rets.isEmpty then sr.fresh else none, nvVals rets sr.nm⟩
    | none => .error 7
  | .error e => .error e

set_option maxRecDepth 20000

mutual
/-- **The completeness walk** of a block from a position. -/
noncomputable def cw : List Core.Stmt → CW → RC
  | [], st => endC X st
  | .atom a :: ss, st => natSeq (nvVals (atomUses a) st.nm) fun m ↦
    cw ss ⟨st.seg, st.its, st.book, st.fr, st.tg, st.nx, st.cnt, st.uq, none, m⟩
  | .ite c z n :: ss, st =>
    match brAtC X st with
    | .ok (st', oc, od, of, x) =>
      match x.kind with
      | .next t =>
        bif Nat.beq oc (X.loc.cell c) && inFrame X.fs [oc] && cellK X st' od && cellK X st' of &&
            x.succ == [t] then
          match segAtC X t st' with
          | some sn =>
            (fileB X.loc X.fs z st'.book).seq fun Bz ↦ (fileB X.loc X.fs n st'.book).seq fun Bn ↦
            match cw z { st' with book := Bz }, cw n { sn with book := Bn } with
            | .join J c1 u1, .join J' c2 u2 =>
              bif Nat.beq J J' then
                match segAtC X J st' with
                | some sj => (Cnt.max c1 c2).seq fun c ↦ natSeq (Nat.lor u1 u2) fun u ↦
                    cw ss { sj with cnt := c, uq := u }
                | none => .fail 10
              else .fail (1000000000 + J * 100000 + J')
            | .fail e, _ => .fail e
            | _, .fail e => .fail e
            | _, _ => .fail 12
          | none => .fail 13
        else .fail 14
      | _ => .fail 15
    | .error e => .fail e
  | .match_ _ [] :: _, _ => .fail 28
  | .match_ v (a0 :: as) :: ss, st =>
    match st.seg.exit.kind, st.seg.exit.succ with
    | .jump (.cell t) ft, t0 :: ts =>
      match tblRead t st.its with
      | some (o1, base) =>
        bif X.F.self ft && Nat.beq ts.length as.length && Nat.beq o1 (X.loc.cell v) &&
            v.path.isEmpty && Nat.beq v.tag 0 && selOk X st v &&
            inFrame X.fs [o1, t] &&
            X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) &&
            armsOk X.G X.entry base 0 (t0 :: ts) && chainPre X st v (as.length + 1) then
          match endAtC X { st with tg := (t, o1, base) :: st.tg } with
          | .ok se =>
            match segAtC X t0 (armSt (armKeyD X.acs v.idx) se) with
            | some s0 =>
              (fileB X.loc X.fs a0 se.book).seq fun B0 ↦
              match cw a0 { s0 with book := B0, tg := armTg X v 0 ++ s0.tg } with
              | .join J c0 u0 =>
                bif armChkK (armKeyD X.acs v.idx) 0 c0 then
                  match cwArms J [] v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 with
                  | some (c, u) => match segAtC X J se with
                    | some sj => (armCnt (armKeyD X.acs v.idx) se c).seq fun c ↦ natSeq u fun u ↦
                        cw ss { sj with cnt := c, uq := u }
                    | none => .fail 20
                  | none => .fail 21
                else .fail 24
              | .chain o succ c0 u0 =>
                bif armChkK (armKeyD X.acs v.idx) 0 c0 && ss.isEmpty && !succ.isEmpty then
                  match cwArms o succ v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 with
                  | some (c, u) => (armCnt (armKeyD X.acs v.idx) se c).seq fun c ↦ natSeq u fun u ↦
                        .chain o succ c u
                  | none => .fail 21
                else .fail 24
              | .fail e => .fail e
              | _ => .fail 22
            | none => .fail 23
          | .error e => .fail e
        else .fail 25
      | none => .fail 26
    | _, _ => .fail 27
  | .call f args rets :: ss, st =>
    match st.seg.exit.kind with
    | .call (.gp e) q r =>
      match calleeS X e with
      | some (_, sg) =>
        bif f == sg.name && Nat.beq args.length sg.nargs &&
            Nat.beq rets.length sg.nret && Nat.ble X.entry r &&
            st.seg.exit.succ == [r - X.entry] && siteOk X args rets q r 0 && !bitK st.uq q &&
            inFrame X.fs (q :: (args ++ rets).map X.loc.cell) && !(f == X.name) then
          match afterC X st q r (setK st.uq q) (callFC X args (sg.env.map (·.1)) r) args
              rets with
          | .ok sr => cw ss sr
          | .error e => .fail e
        else .fail 31
      | none => .fail 32
    | _ => .fail 33
  | .dispatch v fs args rets :: ss, st =>
    match st.seg.exit.kind with
    | .call (.cell t) q r =>
      match tblRead t st.its with
      | some (o1, base) =>
        bif Nat.beq o1 (X.loc.cell v) && v.path.isEmpty && Nat.beq v.tag 0 && selOk X st v &&
            tcOk X base args.length rets.length 0 fs &&
            Nat.ble X.entry r && st.seg.exit.succ == [r - X.entry] && siteOk X args rets q r t &&
            !bitK st.uq q && !bitK st.uq t && !Nat.beq q t &&
            inFrame X.fs (t :: q :: o1 :: (args ++ rets).map X.loc.cell) &&
            fs.all (fun g ↦ !(g == X.name)) then
          match afterC X { st with tg := (t, o1, base) :: st.tg } q r (setK (setK st.uq q) t)
              (callFC X args [] r) args rets with
          | .ok sr => cw ss sr
          | .error e => .fail e
        else .fail 41
      | none => .fail 42
    | _ => .fail 43
  | .callIf c f args :: ss, st =>
    match peekBr st.its with
    | some (oc, x) =>
      bif Nat.beq oc (X.loc.cell c) && inFrame X.fs (oc :: args.map X.loc.cell) then
        match x.kind with
        | .call (.gp e) q r =>
          match calleeS X e with
          | some (_, sg) =>
            bif f == sg.name && Nat.beq args.length sg.nargs &&
                Nat.beq sg.nret 0 && Nat.ble X.entry r && x.succ == [r - X.entry] &&
                siteOk X args [] q r 0 && !bitK st.uq q && inFrame X.fs [q] && !(f == X.name) then
              match brAtC X { st with fr := (q, callFC X args (sg.env.map (·.1)) r) :: st.fr } with
              | .ok (st', _, od, of, _) =>
                bif cellK X st' od && cellK X st' of then
                  match endAtC X st' with
                  | .ok se => match se.seg.exit.kind with
                    | .next t =>
                      bif Nat.beq t (r - X.entry) && se.seg.exit.succ == [t] then
                        match segAtC X t st' with
                        | some sr => (Cnt.max se.cnt st'.cnt).seq fun c ↦ natSeq (setK st.uq q) fun u ↦
                            cw ss { sr with cnt := c, uq := u }
                        | none => .fail 50
                      else .fail 51
                    | _ => .fail 52
                  | .error e => .fail e
                else .fail 54
              | .error e => .fail e
            else .fail 56
          | none => .fail 57
        | .jump (.gp e) (.fpg S) =>
          match ss with
          | [.ret []] =>
            bif Nat.beq e X.entry && f == X.name && Nat.beq S X.fs && Nat.beq args.length X.nargs &&
                Nat.beq X.nret 0 && !X.main && (siteC X args []).isNone then
              match brAtC X { st with nx := (argFC X.loc 2 args ++ [(0, .hdr 0), (1, .hdr 1)] ++
                  X.self.map (fun o ↦ (o, FC.self))) } with
              | .ok (st', _, od, of, _) =>
                bif cellK X st' od && cellK X st' of && st'.cnt.le X.pmax then
                  match endAtC X st' with
                  | .ok se =>
                    bif decide (se.seg.exit.kind = .ret) && se.cnt.le X.pmax then .done else .fail 60
                  | .error e => .fail e
                else .fail 62
              | .error e => .fail e
            else .fail 64
          | _ => .fail 65
        | _ => .fail 66
      else .fail 67
    | none => .fail 68
  | .ret vs :: _, st =>
    match endAtC X st with
    | .ok se =>
      bif (bif X.main then decide (se.seg.exit.kind = .jump (.gp (2 ^ 19 - 1)) (.gp 0))
          else decide (se.seg.exit.kind = .ret)) && se.cnt.le X.pmax &&
        Nat.beq vs.length X.nret && runCells (2 + X.nargs) (vs.map X.loc.cell) &&
        inFrame X.fs (vs.map X.loc.cell) then .done else .fail 70
    | .error e => .fail e

/-- The other arms of a `match` on `v`, each from its segment, ending as `armEnd J succ` says (at
the join `J`, or in the next `match`'s table jump): the most counts of any. -/
noncomputable def cwArms (J : ℕ) (succ : List ℕ) (v : V) (se : CW) (key : Option (List Cnt)) :
    List (List Core.Stmt) → List ℕ → Cnt → ℕ → ℕ → Option (Cnt × ℕ)
  | [], [], c, u, _ => some (c, u)
  | a :: as, t :: ts, c, u, k =>
    match segAtC X t se with
    | some s => (fileB X.loc X.fs a se.book).seq fun B ↦
      match armEnd J succ (cw a { s with book := B, tg := armTg X v k ++ s.tg }) with
      | some (c', u') => bif armChkK key k c' then
          (Cnt.max c c').seq fun c ↦ natSeq (Nat.lor u u') fun u ↦ cwArms J succ v se key as ts c u (k + 1)
          else none
      | none => none
    | none => none
  | _, _, _, _, _ => none
end

/-- **A chained `match`**, entered from the arms of the one before by a table jump through slot
`log fp[o]` into the arms `succ`: the `match` on the value in cell `o`, each arm walked from its
segment with the facts, frames, reads and counts `se` of the chain's dispatch, all ending at one
join (the walk goes on there) or, the `match` the last statement, in one next table jump. -/
noncomputable def cwE (X : CX) (o : ℕ) (succ : List ℕ) (se : CW) : List Core.Stmt → RC
  | .match_ v (a0 :: as) :: ss =>
    match succ with
    | t0 :: ts =>
      bif Nat.beq o (X.loc.cell v) && v.path.isEmpty && Nat.beq v.tag 0 && selOk X se v &&
          Nat.beq ts.length as.length && inFrame X.fs [o] && chainPre X se v (as.length + 1) then
        match segAtC X t0 (armSt (armKeyD X.acs v.idx) se) with
        | some s0 =>
          (fileB X.loc X.fs a0 se.book).seq fun B0 ↦
          match cw X a0 { s0 with book := B0, tg := armTg X v 0 ++ s0.tg } with
          | .join J c0 u0 =>
            bif armChkK (armKeyD X.acs v.idx) 0 c0 then
              match cwArms X J [] v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 with
              | some (c, u) => match segAtC X J se with
                | some sj => (armCnt (armKeyD X.acs v.idx) se c).seq fun c ↦ natSeq u fun u ↦
                    cw X ss { sj with cnt := c, uq := u }
                | none => .fail 80
              | none => .fail 81
            else .fail 84
          | .chain o' succ' c0 u0 =>
            bif armChkK (armKeyD X.acs v.idx) 0 c0 && ss.isEmpty && !succ'.isEmpty then
              match cwArms X o' succ' v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 with
              | some (c, u) => (armCnt (armKeyD X.acs v.idx) se c).seq fun c ↦ natSeq u fun u ↦
                  .chain o' succ' c u
              | none => .fail 81
            else .fail 84
          | .fail e => .fail e
          | _ => .fail 82
        | none => .fail 83
      else .fail 85
    | [] => .fail 86
  | _ => .fail 87

end Walk

/-! ## A function, by windows and parts

Window `i` of function `j` is walked over the segments of the soundness certificate's window
(`execWin` from `(cutAt i).J` to `endAt i`), its statements (`stmtsAt i`) in parts, each walked
by its own kernel evaluation (`Data.cplParts`): part `k` starts at statement `s` of the window at
the start of the segment at offset `J` (the window's start for the first part), from the facts of
its statements, no frame in flight, and the counts and set-up site cells its start hands on; it
ends at the next part's start within what is handed on there, or, the window's last part, at the
next window's start, or, the function's last, by the return within the most a path runs
(`Plumb.pmax`). -/

/-- The fixed cells in `[2, n)`, by cell. -/
noncomputable def statT (n : ℕ) : List (ℕ × PC) → Trie PC → Trie PC
  | [], t => t
  | p :: ps, t => bif Nat.ble 2 p.1 && Nat.blt p.1 n then (setF p.2 envDepth t p.1).seq fun t ↦
      statT n ps t else statT n ps t

/-- The renumbered values a block's own atoms name. -/
def nvOf : List Core.Stmt → ℕ → ℕ
  | [], s => s
  | .atom a :: ss, s => natSeq (nvVals (atomUses a) s) fun s ↦ nvOf ss s
  | _ :: ss, s => nvOf ss s

/-- The last window's statements: none returns but the last, a `ret`. -/
def lastOkC : List Core.Stmt → Bool
  | [] => false
  | [.ret _] => true
  | s :: ss => Stmt.noRet s && lastOkC ss

/-! A function's data: its view of the program `G`, code `f`, core IR `cf`, certificate `C`,
completeness data `P`, frame size `fs`, parts `ps` (`Data.cplParts`), arms counted separately
`acs` (`Data.cplArms`), and whether it is `main`. -/

/-- The parts of window `i`, `[s, J, counts, set-up cells, m]` each, `m` (absent: `0`) the items of
the segment at `J` before the part (none: one part from the window's start with nothing handed
on). -/
noncomputable def partsOfD (ps : List (List (List ℕ))) (i : ℕ) : List (List ℕ) := listElementOrDefault ps i []

/-- The number of parts of a window. -/
noncomputable def nPartsD (ps : List (List (List ℕ))) (i : ℕ) : ℕ := Nat.max 1 (partsOfD ps i).length

/-- The window statement part `k` starts at. -/
noncomputable def partSD (ps : List (List (List ℕ))) (i k : ℕ) : ℕ :=
  listElementOrDefault (listElementOrDefault (partsOfD ps i) k []) 0 0

/-- The code offset part `k` starts at: the window's start for the first. -/
noncomputable def partJD (C : Cert) (ps : List (List (List ℕ))) (i k : ℕ) : ℕ :=
  bif Nat.beq k 0 then (C.cutAt i).J else listElementOrDefault (listElementOrDefault (partsOfD ps i) k []) 1 0

/-- The counts at part `k`'s start. -/
noncomputable def partCD (ps : List (List (List ℕ))) (i k : ℕ) : Cnt :=
  Cnt.ofList ((listElementOrDefault (partsOfD ps i) k []).drop 2)

/-- The set-up site cells at part `k`'s start. -/
noncomputable def partUD (ps : List (List (List ℕ))) (i k : ℕ) : ℕ :=
  listElementOrDefault (listElementOrDefault (partsOfD ps i) k []) 8 0

/-- The items of its segment part `k` starts after (`0`: at the segment's start). -/
noncomputable def partMD (ps : List (List (List ℕ))) (i k : ℕ) : ℕ :=
  listElementOrDefault (listElementOrDefault (partsOfD ps i) k []) 9 0

/-- Part `k` entered: it starts with a chained `match`, entered by a table jump through the
selector in cell `o` into its arms `succ` (`[…, m, 1, o, succ…]`). -/
noncomputable def partEntD (ps : List (List (List ℕ))) (i k : ℕ) : Option (ℕ × List ℕ) :=
  match (listElementOrDefault (partsOfD ps i) k []).drop 10 with
  | 1 :: o :: succ => some (o, succ)
  | _ => none

/-- Where part `k` stops: inside a segment, if the next part starts there. -/
noncomputable def stopOfD (C : Cert) (ps : List (List (List ℕ))) (i k : ℕ) : Option (ℕ × ℕ) :=
  bif Nat.blt (k + 1) (nPartsD ps i) && !(Nat.beq (partMD ps i (k + 1)) 0) then
    some (partJD C ps i (k + 1), partMD ps i (k + 1))
  else none

/-- The statements of part `k`. -/
noncomputable def partStmtsD (cf : Core.Fn) (C : Cert) (ps : List (List (List ℕ))) (i k : ℕ) :
    List Core.Stmt :=
  bif Nat.blt (k + 1) (nPartsD ps i) then
    ((C.stmtsAt cf i).drop (partSD ps i k)).take (partSD ps i (k + 1) - partSD ps i k)
  else (C.stmtsAt cf i).drop (partSD ps i k)

/-- The context of a window: the function's callees as `G` has them, and no other function. -/
noncomputable def cxOfD (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (P : Plumb)
    (fs : ℕ) (acs : List (ℕ × List (List ℕ))) (main : Bool) (idx : Trie Exec.Seg) (loc : CLoc)
    (stat : Trie PC) (nv : ℕ) (stop : Option (ℕ × ℕ)) : CX :=
  ⟨G.restrict C.callees, C.facts, f.entryPc, idx, loc, fs, stat, main, cf.name, cf.params.length,
    C.nret, C.callees, P.sites, P.arms, C.facts.env.map (·.1), Cnt.ofList P.pmax, nv, stop, acs,
    P.chains⟩

/-- How part `k` of window `i` must end: at the next part's start, the next window's, within
what is handed on there (in its chained `match`'s table jump if it is entered), or by the
return. -/
noncomputable def partEndD (C : Cert) (ps : List (List (List ℕ))) (i k : ℕ) : RC → Bool
  | .join J c u =>
    bif Nat.blt (k + 1) (nPartsD ps i) then
      Nat.beq J (partJD C ps i (k + 1)) && Nat.beq (partMD ps i (k + 1)) 0 &&
        (partEntD ps i (k + 1)).isNone && c.le (partCD ps i (k + 1)) && subK u (partUD ps i (k + 1))
    else Nat.blt i C.cuts.length && Nat.beq J (C.cutAt (i + 1)).J &&
      (partEntD ps (i + 1) 0).isNone && c.le (partCD ps (i + 1) 0) && subK u (partUD ps (i + 1) 0)
  | .mid J m c u => Nat.blt (k + 1) (nPartsD ps i) && Nat.beq J (partJD C ps i (k + 1)) &&
      Nat.beq m (partMD ps i (k + 1)) && !(Nat.beq m 0) && (partEntD ps i (k + 1)).isNone &&
      c.le (partCD ps i (k + 1)) && subK u (partUD ps i (k + 1))
  | .chain o succ c u => !succ.isEmpty &&
    bif Nat.blt (k + 1) (nPartsD ps i) then
      decide (partEntD ps i (k + 1) = some (o, succ)) && Nat.beq (partJD C ps i (k + 1)) (succ.headD 0) &&
        c.le (partCD ps i (k + 1)) && subK u (partUD ps i (k + 1))
    else Nat.blt i C.cuts.length && decide (partEntD ps (i + 1) 0 = some (o, succ)) &&
      Nat.beq (partJD C ps (i + 1) 0) (succ.headD 0) && c.le (partCD ps (i + 1) 0) &&
        subK u (partUD ps (i + 1) 0)
  | .done => !(Nat.blt (k + 1) (nPartsD ps i)) && !(Nat.blt i C.cuts.length)
  | .fail _ => false

/-- The walk's result of part `k` of window `i`. -/
noncomputable def cplResD (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (P : Plumb)
    (fs : ℕ) (ps : List (List (List ℕ))) (acs : List (ℕ × List (List ℕ))) (main : Bool) (i k : ℕ) :
    RC :=
  match execWinCS C.facts f (C.cutAt i).J (C.cutAt i).env ((C.succAt i).drop 1) (C.endAt f i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (clocW C i).seq fun loc ↦
    (statT fs P.stat .nil).seq fun stat ↦
    (fileB loc fs (partStmtsD cf C ps i k) .nil).seq fun B ↦
    (partCD ps i k).seq fun c ↦ natSeq (partUD ps i k) fun u ↦ natSeq (partJD C ps i k) fun J ↦
    natSeq P.nv fun nv ↦ natSeq (partMD ps i k) fun m ↦
    match getF idx J with
    | some s => bif Nat.beq s.start J then
        match partEntD ps i k with
        | some (o, succ) => cwE (cxOfD G f cf C P fs acs main idx loc stat nv (stopOfD C ps i k)) o succ
            ⟨s, s.items, B, [], [], [], c, u, some J, 0⟩ (partStmtsD cf C ps i k)
        | none => cw (cxOfD G f cf C P fs acs main idx loc stat nv (stopOfD C ps i k)) (partStmtsD cf C ps i k)
          ⟨s, s.items.drop m, B, [], [], [], c, u, bif Nat.beq m 0 then some J else none, 0⟩
      else .fail 91
    | none => .fail 90

/-- What a window's first part also checks: its cells pack, and the function's first window
starts with nothing handed on, its parameters `V.n 0, V.n 1, …`, its self frame pointer cells
fixed, and its values the top-level atoms name as `Plumb.nv` says, which every part reads. -/
noncomputable def winOkCD (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (ps : List (List (List ℕ)))
    (i : ℕ) : Bool :=
  (listElementOrDefault C.cells i []).all (fun c ↦ Nat.blt c 65536) &&
  Nat.beq (partSD ps i 0) 0 && Nat.beq (partMD ps i 0) 0 &&
  (match partEntD ps i 0 with
    | some (o, succ) => Nat.beq o (C.selAt i) && succ == C.succAt i && !succ.isEmpty
    | none => (C.succAt i).isEmpty) &&
  cf.params == (List.range cf.params.length).map V.n &&
  (bif Nat.beq i 0 then (partCD ps 0 0).le Cnt.zero && Nat.beq (partUD ps 0 0) 0 &&
      C.facts.env.all (fun p ↦ Sym.beq p.2 (.fpg 0) &&
        decide (getF (statT fs P.stat .nil) p.1 = some (.fpg 0))) &&
      Nat.beq (nvOf cf.body 0) P.nv
    else true)

/-- The last part of the function's last window. -/
noncomputable def lastPartD (C : Cert) (ps : List (List (List ℕ))) (i k : ℕ) : Bool :=
  !(Nat.blt (k + 1) (nPartsD ps i)) && !(Nat.blt i C.cuts.length)

/-- **The completeness check of part `k` of window `i`** of a function, from its data: its
statements return only at the function's end, it starts within its window and after the part
before it, and its walk ends as `partEndD` says. -/
noncomputable def cplWinD (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (P : Plumb)
    (fs : ℕ) (ps : List (List (List ℕ))) (acs : List (ℕ × List (List ℕ))) (main : Bool) (i k : ℕ) :
    Bool :=
  (bif Nat.beq k 0 then winOkCD cf C P fs ps i else Nat.ble (partSD ps i (k - 1)) (partSD ps i k)) &&
  Nat.ble (partSD ps i k) (C.stmtsAt cf i).length &&
  (bif lastPartD C ps i k then lastOkC (partStmtsD cf C ps i k)
    else Stmt.noRetList (partStmtsD cf C ps i k)) &&
  partEndD C ps i k (cplResD G f cf C P fs ps acs main i k)

/-- The completeness check reads its context only as the function's callees see it. -/
theorem cplWinD_congr {G G' : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert} {P : Plumb}
    {fs : ℕ} {ps : List (List (List ℕ))} {acs : List (ℕ × List (List ℕ))} {main : Bool} {i k : ℕ}
    (h : G.restrict C.callees = G'.restrict C.callees) :
    cplWinD G f cf C P fs ps acs main i k = cplWinD G' f cf C P fs ps acs main i k := by
  simp only [cplWinD, cplResD, cxOfD, h]

/-- **Every part of every window passes the completeness check.** -/
noncomputable def CplOkD (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ)
    (ps : List (List (List ℕ))) (acs : List (ℕ × List (List ℕ))) (main : Bool) : Prop :=
  ∀ i ≤ C.cuts.length, ∀ k < nPartsD ps i, cplWinD G f cf C P fs ps acs main i k = true

end
end LeanVM.Guest.B2C
