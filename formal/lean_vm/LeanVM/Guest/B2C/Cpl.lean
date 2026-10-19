/-
  LeanVM.Guest.B2C.Cpl

  B2's completeness check of one compiled function: its code runs from its entry to its return
  on a memory whose frame holds what the honest memory puts there, window by window of its
  soundness certificate.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Data.CplHand
public import LeanVM.Guest.B2C.Count

/-!
# The completeness check

`FrameHolds L j fp σ es vs kfps hdr` is what the check reads of the memory for one instance of
function `j` at frame `fp` on the path `es` of its valuation `σ` (`walk σ (coreOf j).body =
.ret es vs`), its callees' frames at `kfps` and its header `hdr`: the header, every value the
path names and every range check temporary at its certificate cell, the fixed cells
(`Plumb.stat`), the frame addresses, the table jumps' targets, each call site's callee frame
pointer and dispatch target, and each callee frame's header, arguments, returns and self frame
pointer cells. `KidsRun` is the callees' runs.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-! ## What the check reads of the memory -/

/-- The self frame pointer cells of a function, by name. -/
noncomputable def selfCells (f : String) : List ℕ :=
  match idxOf f with
  | some j => (certOf j).facts.env.map (·.1)
  | none => []

/-- The header of the callee of the `i`-th call on a path `es` of function `j` at `fp` with
header `hdr` (`H`'s): the caller's own for a loop's tail call, its last; else its call site's
return pc and the caller's frame. -/
noncomputable def kidHdr (j fp : ℕ) (hdr : E × E) (es : List Ev) (i : ℕ) : E × E :=
  match (calls es)[i]? with
  | some c =>
    if (coreOf j).loop = true ∧ i + 1 = (calls es).length then hdr
    else match siteOf j c with
      | some s => (ofK (gpow s.r), ofK (gpow fp))
      | none => (0, 0)
  | none => (0, 0)

/-- **What one instance's frame holds** for the completeness check: an instance of function `j`
at frame `fp` (cells at `g^(fp + o)`) with valuation `σ`, path `es` and returned values `vs`, its
callees' frames at `kfps` (one per call of `es`, in order) and its header `hdr`. -/
structure FrameHolds {κ : ℕ} (L : MemImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V)
    (kfps : List ℕ) (hdr : E × E) : Prop where
  /-- The header. -/
  hdr0 : L.read (gpow (fp + 0)) = some hdr.1
  hdr1 : L.read (gpow (fp + 1)) = some hdr.2
  /-- A function but `main` returns to registers of `K`. -/
  hdrK : j ≠ 1 → IsInK hdr.1 ∧ IsInK hdr.2
  /-- Every value the path names, at its cell. -/
  val : ∀ v ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j v → cellJ j v < fsN j →
    L.read (gpow (fp + cellJ j v)) = some (σ v)
  /-- The range checks' temporaries, at their cells. -/
  tmp : ∀ e ∈ es, ∀ t ∈ e.tmps, 2 ≤ cellJ j t → cellJ j t < fsN j →
    L.read (gpow (fp + cellJ j t)) = some (σ t)
  /-- The fixed cells. -/
  stat : ∀ p ∈ (plumbOf j).stat, 2 ≤ p.1 → p.1 < fsN j →
    L.read (gpow (fp + p.1)) = some (p.2.word fp)
  /-- The frame addresses point into the frame. -/
  addr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cellJ j q.2))
  /-- The table jumps' targets. -/
  arm : ∀ a ∈ (plumbOf j).arms, 2 ≤ a.2.1 → a.2.1 < fsN j →
    L.read (gpow (fp + a.2.1)) = some (armWord σ a.1 a.2.2)
  /-- One callee frame per call. -/
  len : kfps.length = (calls es).length
  /-- A call site's callee frame pointer and dispatch target. -/
  site : ∀ (i : ℕ) (c : Call) (kfp : ℕ) (s : Site), (calls es)[i]? = some c → kfps[i]? = some kfp → siteOf j c = some s →
    (2 ≤ s.q → s.q < fsN j → L.read (gpow (fp + s.q)) = some (ofK (gpow kfp))) ∧
    (s.tgt ≠ 0 → 2 ≤ s.tgt → s.tgt < fsN j →
      L.read (gpow (fp + s.tgt)) = some (ofK (gpow (entryOf c.f))))
  /-- Each callee frame's header, arguments, returns (a call entered) and self frame pointer
  cells. -/
  kid : ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    L.read (gpow (kfp + 0)) = some (kidHdr j fp hdr es i).1 ∧
    L.read (gpow (kfp + 1)) = some (kidHdr j fp hdr es i).2 ∧
    (∀ k (hk : k < c.args.length), L.read (gpow (kfp + (2 + k))) = some (σ c.args[k])) ∧
    (c.taken = true → ∀ k (hk : k < c.rets.length),
      L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])) ∧
    (∀ o ∈ selfCells c.f, L.read (gpow (kfp + o)) = some (ofK (gpow kfp)))
  /-- A loop's tail call, its last, has its frame right after the caller's. -/
  tail : (coreOf j).loop = true → ∀ kfp, kfps.getLast? = some kfp → kfp = fp + fsN j

/-- **The callees on a path run**: each call entered, from its callee's entry at its frame to its
return registers, executing `ck[i] op` instructions of each opcode. -/
def KidsRun {κ : ℕ} (L : MemImage κ) (es : List Ev) (kfps : List ℕ) (ck : List (Opcode → ℕ)) :
    Prop :=
  ck.length = (calls es).length ∧ ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    c.taken = true → ∃ r, retRegs L (gpow kfp) = some r ∧
      RunC guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r (ck.getD i 0)


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
  ⟨nth C.los i 0, (nth C.cells i []).length, packC (nth C.cells i []), nth C.ins i []⟩

/-! ## Counts -/

/-- Instructions of each opcode. -/
structure Cnt where
  x : ℕ
  m : ℕ
  s : ℕ
  d : ℕ
  j : ℕ
  b : ℕ

/-- The count of an opcode. -/
def Cnt.get (c : Cnt) : Opcode → ℕ
  | .xor => c.x
  | .mulNative => c.m
  | .setConstant => c.s
  | .deref => c.d
  | .jump => c.j
  | .blake2s => c.b

/-- `k c`, its counts evaluated first. -/
def Cnt.seq {β : Type} (c : Cnt) (k : Cnt → β) : β :=
  match c with
  | ⟨x, m, s, d, j, b⟩ => natSeq x fun x ↦ natSeq m fun m ↦ natSeq s fun s ↦ natSeq d fun d ↦
      natSeq j fun j ↦ natSeq b fun b ↦ k ⟨x, m, s, d, j, b⟩

theorem Cnt.seq_eq {β : Type} (c : Cnt) (k : Cnt → β) : c.seq k = k c := by
  cases c
  simp only [Cnt.seq, natSeq_eq]

/-- One more instruction of `ins`'s opcode. -/
def Cnt.bump (c : Cnt) : OInstr → Cnt
  | .xor .. => { c with x := c.x + 1 }
  | .mul .. => { c with m := c.m + 1 }
  | .set .. => { c with s := c.s + 1 }
  | .deref .. => { c with d := c.d + 1 }
  | .jump .. => { c with j := c.j + 1 }
  | .blake2s .. => { c with b := c.b + 1 }

/-- One more `JUMP`. -/
def Cnt.bumpJ (c : Cnt) : Cnt := { c with j := c.j + 1 }

/-- The larger counts. -/
def Cnt.max (c c' : Cnt) : Cnt :=
  ⟨Nat.max c.x c'.x, Nat.max c.m c'.m, Nat.max c.s c'.s, Nat.max c.d c'.d, Nat.max c.j c'.j,
    Nat.max c.b c'.b⟩

/-- Every count at most the other's. -/
def Cnt.le (c c' : Cnt) : Bool :=
  Nat.ble c.x c'.x && Nat.ble c.m c'.m && Nat.ble c.s c'.s && Nat.ble c.d c'.d && Nat.ble c.j c'.j &&
    Nat.ble c.b c'.b

/-- Counts from a list in `Opcode`'s order. -/
def Cnt.ofList (l : List ℕ) : Cnt := ⟨nth l 0 0, nth l 1 0, nth l 2 0, nth l 3 0, nth l 4 0, nth l 5 0⟩

/-- No instructions. -/
def Cnt.zero : Cnt := ⟨0, 0, 0, 0, 0, 0⟩

/-! ## Facts on the frame

The atoms of the path, on their cells (`Check.LAtom`), filed under the cells the check looks
them up by. -/

/-- The cells a fact is filed under. -/
def keysC : LAtom → List ℕ
  | .const d _ => [d]
  | .add d a b => [d, a, b]
  | .mul d _ _ => [d]
  | .same a b => [a, b]
  | .load d p _ => [d, p]
  | .ne _ _ p => [p]
  | .range x y t1 t2 k => [t1, t2, k, x, y]
  | .inK a b => [a, b]
  | .blake _ _ _ _ _ _ o0 _ _ => [o0]
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
  | .blake m0 m1 m2 m3 cv0 cv1 o0 o1 md => [m0, m1, m2, m3, cv0, cv1, o0, o1, md]
  | .addr p _ => [p]
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
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      .blake (L.cell m0) (L.cell m1) (L.cell m2) (L.cell m3) (L.cell cv0) (L.cell cv1) (L.cell o0)
        (L.cell o1) (L.cell md)
  | .frameAddr p run => .addr (L.cell p) (run.map L.cell)
  | .hint _ => .none

/-- The facts by cell. -/
abbrev BookC := Trie (List LAtom)

/-- The facts filed under a cell. -/
noncomputable def lookC (B : BookC) (o : ℕ) : List LAtom := (getF B o).getD []

/-- File `a` under `o`. -/
noncomputable def addKeyC (a : LAtom) (B : BookC) (o : ℕ) : BookC :=
  listSeq (lookC B o) fun l ↦ setF (a :: l) envDepth B o

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

/-- A position of the walk: a segment and its items not yet passed, the facts, the callee frames
in flight `(cell, its cells)`, the table reads `(target, selector, base)`, the next frame of a
tail call, the instructions passed on the path, and `fresh = some t` at the start of segment `t`
before any item is passed. -/
structure CW where
  seg : Exec.Seg
  its : List Exec.Item
  book : BookC
  fr : List (ℕ × List (ℕ × FC))
  tg : List (ℕ × ℕ × ℕ)
  nx : List (ℕ × FC)
  cnt : Cnt
  fresh : Option ℕ

/-! ## Justifying instructions -/

section Just

variable (X : CX) (st : CW)

/-- A fixed cell. -/
noncomputable def statAt (o : ℕ) : Option PC := getF X.stat o

/-- The exponent of the `SET` immediate `(k0, 0, 0)` as a power of `g`. -/
noncomputable def gpE (k0 : ℕ) : Option ℕ := bif Nat.beq k0 1 then some 0 else X.F.pows.find k0

/-- The constant a cell holds: a fixed cell's, a constant's, an `assert !=`'s `1`. -/
noncomputable def cstAt (o : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match statAt X o with
  | some (.k k0 k1 k2) => some (k0, k1, k2)
  | _ => (lookC st.book o).findSome? fun a ↦ match a with
    | .const d x => bif Nat.beq d o then some (limbNat x 0, limbNat x 1, limbNat x 2) else none
    | .ne _ _ p => bif Nat.beq p o then some (1, 0, 0) else none
    | _ => none

/-- The cell holds `0`. -/
noncomputable def isZ (o : ℕ) : Bool :=
  match cstAt X st o with
  | some (0, 0, 0) => true
  | _ => false

/-- The cell holds `1`. -/
noncomputable def isO (o : ℕ) : Bool :=
  match cstAt X st o with
  | some (1, 0, 0) => true
  | _ => false

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

/-- `{x, y} = {a, b}`. -/
def pairEq (x y a b : ℕ) : Bool := (Nat.beq x a && Nat.beq y b) || (Nat.beq x b && Nat.beq y a)

/-- The cell holds a word of `K`. -/
noncomputable def cellK (o : ℕ) : Bool :=
  (Nat.ble o 1 && !X.main) ||
  (match statAt X o with
    | some (.k _ k1 k2) => Nat.beq k1 0 && Nat.beq k2 0
    | some (.fpg _) => true
    | none => false) ||
  (lookC st.book o).any (fun x ↦ match x with
    | .const d x => Nat.beq d o && Nat.beq (limbNat x 1) 0 && Nat.beq (limbNat x 2) 0
    | .load _ p _ => Nat.beq p o
    | .range x y _ _ _ => Nat.beq x o || Nat.beq y o
    | .inK a b => Nat.beq a o || Nat.beq b o
    | .addr p _ => Nat.beq p o
    | .ne _ _ p => Nat.beq p o
    | _ => false) ||
  st.fr.any (fun q ↦ Nat.beq q.1 o) || st.tg.any (fun t ↦ Nat.beq t.1 o)

/-- A `MUL` of a frame address: `fp[a] = fp·g^e₁`, `fp[b] = g^e₂`, the run at `e₁ + e₂`. -/
noncomputable def addrMul (a b : ℕ) (run : List ℕ) : Bool :=
  match statAt X a, cstAt X st b, run with
  | some (.fpg e1), some (k0, 0, 0), r :: _ => match gpE X k0 with
    | some e2 => Nat.beq (e1 + e2) r
    | none => false
  | _, _, _ => false

/-- A `MUL` of fixed cells: `fp·g^e = fp·g^e₁ · g^(e - e₁)`. -/
noncomputable def fpgMul (a b d : ℕ) : Bool :=
  match statAt X d, statAt X a, cstAt X st b with
  | some (.fpg e), some (.fpg e1), some (k0, 0, 0) => Nat.ble e1 e && (match gpE X k0 with
    | some e2 => Nat.beq e2 (e - e1)
    | none => false)
  | _, _, _ => false

/-- A copy into the next frame's cell `o`. -/
noncomputable def nextMul (a o : ℕ) : Bool :=
  match st.nx.find? (fun p ↦ Nat.beq p.1 o) with
  | some (_, .val cv) => sameC X st a cv
  | some (_, .hdr i) => Nat.beq a i && Nat.ble i 1
  | some (_, .self) => decide (statAt X a = some (.fpg X.fs))
  | _ => false

/-- A store into or load from a callee frame through its pointer cell `o1`. -/
noncomputable def frameCell (o1 o2 o3 : ℕ) : Bool :=
  match st.fr.find? (fun q ↦ Nat.beq q.1 o1) with
  | some (_, fcs) => fcs.any fun p ↦ Nat.beq p.1 o2 && (match p.2 with
    | .val cv => sameC X st cv o3
    | .self => Nat.beq o3 o1
    | .pc r => (match cstAt X st o3 with
      | some (k0, 0, 0) => decide (gpE X k0 = some r)
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
noncomputable def justI (pc : ℕ) : OInstr → Bool
  | .set o k0 k1 k2 => decide (cstAt X st o = some (k0, k1, k2))
  | .xor a b d =>
    (lookC st.book d).any (fun x ↦ match x with
      | .add d' x y => perm3 a b d d' x y
      | _ => false) ||
    (isZ X st d && sameC X st a b) || (Nat.beq a d && isZ X st b && known X st d) ||
    (Nat.beq b d && isZ X st a && known X st d) || (Nat.beq b d && known X st d && zeroBy X st a)
  | .mul a b d =>
    (lookC st.book d).any (fun x ↦ match x with
      | .mul d' x y => Nat.beq d' d && pairEq x y a b
      | .range x y _ _ k => Nat.beq k d && pairEq x y a b
      | .ne x i p => Nat.beq p d && pairEq x i a b
      | .addr p run => Nat.beq p d && addrMul X st a b run
      | _ => false) ||
    (isO X st b && sameC X st a d) || (isO X st a && sameC X st b d) || fpgMul X st a b d ||
    (Nat.ble X.fs d && isO X st b && nextMul X st a (d - X.fs))
  | .deref o1 o2 o3 .cell =>
    (lookC st.book o3).any (fun x ↦ match x with
      | .load d p off => Nat.beq d o3 && Nat.beq p o1 && Nat.beq off o2
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
  | .blake2s m0 m1 m2 m3 cv out md =>
    (lookC st.book out).any fun x ↦ match x with
      | .blake n0 n1 n2 n3 c0 c1 o0 o1 d => Nat.beq n0 m0 && Nat.beq n1 m1 && Nat.beq n2 m2 &&
          Nat.beq n3 m3 && Nat.beq c0 cv && Nat.beq c1 (cv + 1) && Nat.beq o0 out &&
          Nat.beq o1 (out + 1) && Nat.beq d md
      | _ => false
  | .jump .. => false

/-- Pass items, each justified and counted, up to the next branch or the end. -/
noncomputable def passL : List Exec.Item → Cnt → Option (List Exec.Item × Cnt)
  | [], c => some ([], c)
  | .ins (.instr pc ins) :: its, c =>
      bif justI X st pc ins then (c.bump ins).seq fun c ↦ passL its c else none
  | .ins (.jump oc od of) :: its, c =>
      bif cellK X st oc && cellK X st od && cellK X st of then c.bumpJ.seq fun c ↦ passL its c
      else none
  | .ins _ :: _, _ => none
  | .fact _ :: its, c => passL its c
  | .branch oc od of x :: its, c => some (.branch oc od of x :: its, c)

end Just

/-! ## Moving along the segments -/

section Move

variable (X : CX)

/-- The start of segment `t`, with the facts, frames, reads and counts of `st`. -/
noncomputable def segAtC (t : ℕ) (st : CW) : Option CW :=
  match getF X.idx t with
  | some s => bif Nat.beq s.start t then
      some ⟨s, s.items, st.book, st.fr, st.tg, st.nx, st.cnt, some t⟩ else none
  | none => none

/-- The position at the end of the segment, its items passed, if no branch is before it. -/
noncomputable def endAtC (st : CW) : Option CW :=
  match passL X st st.its st.cnt with
  | some ([], c) => c.seq fun c ↦ some ⟨st.seg, [], st.book, st.fr, st.tg, st.nx, c, none⟩
  | _ => none

/-- The next branch, the items before it passed: the position after it, its cells and exit. -/
noncomputable def brAtC (st : CW) : Option (CW × ℕ × ℕ × ℕ × Exec.Exit) :=
  match passL X st st.its st.cnt with
  | some (.branch oc od of x :: its, c) => c.bumpJ.seq fun c ↦
      some (⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c, none⟩, oc, od, of, x)
  | _ => none

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

/-- How a block's walk ends: at a join with the counts of the path there (the most of any), by
the return, or not at all (with a code saying where). -/
inductive RC where
  | join (J : ℕ) (c : Cnt)
  | done
  | fail (code : ℕ)

section Walk

variable (X : CX)

/-- The callee at `pc`, among the function's callees. -/
noncomputable def calleeC (pc : ℕ) : Option ℕ :=
  X.callees.find? fun j ↦ X.G.good j && Nat.beq (X.G.sig j).entry pc

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
      | some pc => match calleeC X pc with
        | some j => f == (X.G.sig j).name && Nat.beq (X.G.sig j).nargs na &&
            Nat.beq (X.G.sig j).nret nr
        | none => false
      | none => false) && tcOk base na nr (k + 1) fs

/-- A callee frame's cells: the arguments, the self frame pointer cells, the caller's frame
pointer and the return pc. -/
def callFC (args : List V) (self : List ℕ) (r : ℕ) : List (ℕ × FC) :=
  argFC X.loc 2 args ++ self.map (fun o ↦ (o, FC.self)) ++ [(1, .fp), (0, .pc r)]

/-- Where a block ends: at the start of a segment, or by its segment's local jump. -/
noncomputable def endC (st : CW) : RC :=
  match st.fresh with
  | some t => .join t st.cnt
  | none => match endAtC X st with
    | some se => match se.seg.exit.kind with
      | .next t => bif se.seg.exit.succ == [t] then .join t se.cnt else .fail 1
      | _ => .fail 2
    | none => .fail 0

/-- After a call into the frame `fp[q]` returning to `r`: the position at the return point, its
callee frame's returns known. -/
noncomputable def afterC (st : CW) (q r : ℕ) (fcs : List (ℕ × FC)) (args rets : List V) :
    Option CW :=
  match endAtC X { st with fr := (q, fcs) :: st.fr } with
  | some se => match segAtC X (r - X.entry) se with
    | some sr => some ⟨sr.seg, sr.its, sr.book, (q, fcs ++ argFC X.loc (2 + args.length) rets) :: st.fr,
        sr.tg, sr.nx, sr.cnt, bif rets.isEmpty then sr.fresh else none⟩
    | none => none
  | none => none

mutual
/-- **The completeness walk** of a block from a position. -/
noncomputable def cw : List Core.Stmt → CW → RC
  | [], st => endC X st
  | .atom _ :: ss, st => cw ss st
  | .ite c z n :: ss, st =>
    match brAtC X st with
    | some (st', oc, od, of, x) =>
      match x.kind with
      | .next t =>
        bif Nat.beq oc (X.loc.cell c) && inFrame X.fs [oc] && cellK X st' od && cellK X st' of &&
            x.succ == [t] then
          match segAtC X t st' with
          | some sn =>
            (fileB X.loc X.fs z st'.book).seq fun Bz ↦ (fileB X.loc X.fs n st'.book).seq fun Bn ↦
            match cw z { st' with book := Bz }, cw n { sn with book := Bn } with
            | .join J c1, .join J' c2 =>
              bif Nat.beq J J' then
                match segAtC X J st' with
                | some sj => (Cnt.max c1 c2).seq fun c ↦ cw ss { sj with cnt := c }
                | none => .fail 10
              else .fail 11
            | .fail e, _ => .fail e
            | _, .fail e => .fail e
            | _, _ => .fail 12
          | none => .fail 13
        else .fail 14
      | _ => .fail 15
    | none => .fail 16
  | .match_ _ [] :: _, _ => .fail 28
  | .match_ v (a0 :: as) :: ss, st =>
    match st.seg.exit.kind, st.seg.exit.succ with
    | .jump (.cell t) ft, t0 :: ts =>
      match tblRead t st.its with
      | some (o1, base) =>
        bif X.F.self ft && Nat.beq ts.length as.length && Nat.beq o1 (X.loc.cell v) &&
            inFrame X.fs [o1, t] &&
            X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) &&
            armsOk X.G X.entry base 0 (t0 :: ts) then
          match endAtC X { st with tg := (t, o1, base) :: st.tg } with
          | some se =>
            match segAtC X t0 se with
            | some s0 =>
              (fileB X.loc X.fs a0 se.book).seq fun B0 ↦
              match cw a0 { s0 with book := B0 } with
              | .join J c0 =>
                match cwArms J se as ts c0 with
                | some c => match segAtC X J se with
                  | some sj => c.seq fun c ↦ cw ss { sj with cnt := c }
                  | none => .fail 20
                | none => .fail 21
              | .fail e => .fail e
              | _ => .fail 22
            | none => .fail 23
          | none => .fail 24
        else .fail 25
      | none => .fail 26
    | _, _ => .fail 27
  | .call f args rets :: ss, st =>
    match st.seg.exit.kind with
    | .call (.gp e) q r =>
      match calleeC X e with
      | some j =>
        bif f == (X.G.sig j).name && Nat.beq args.length (X.G.sig j).nargs &&
            Nat.beq rets.length (X.G.sig j).nret && Nat.ble X.entry r &&
            st.seg.exit.succ == [r - X.entry] && siteOk X args rets q r 0 &&
            inFrame X.fs (q :: (args ++ rets).map X.loc.cell) then
          match afterC X st q r (callFC X args ((X.G.sig j).env.map (·.1)) r) args rets with
          | some sr => cw ss sr
          | none => .fail 30
        else .fail 31
      | none => .fail 32
    | _ => .fail 33
  | .dispatch v fs args rets :: ss, st =>
    match st.seg.exit.kind with
    | .call (.cell t) q r =>
      match tblRead t st.its with
      | some (o1, base) =>
        bif Nat.beq o1 (X.loc.cell v) && tcOk X base args.length rets.length 0 fs &&
            Nat.ble X.entry r && st.seg.exit.succ == [r - X.entry] && siteOk X args rets q r t &&
            inFrame X.fs (t :: q :: o1 :: (args ++ rets).map X.loc.cell) then
          match afterC X { st with tg := (t, o1, base) :: st.tg } q r (callFC X args [] r) args
              rets with
          | some sr => cw ss sr
          | none => .fail 40
        else .fail 41
      | none => .fail 42
    | _ => .fail 43
  | .callIf c f args :: ss, st =>
    match peekBr st.its with
    | some (oc, x) =>
      bif Nat.beq oc (X.loc.cell c) && inFrame X.fs (oc :: args.map X.loc.cell) then
        match x.kind with
        | .call (.gp e) q r =>
          match calleeC X e with
          | some j =>
            bif f == (X.G.sig j).name && Nat.beq args.length (X.G.sig j).nargs &&
                Nat.beq (X.G.sig j).nret 0 && Nat.ble X.entry r && x.succ == [r - X.entry] &&
                siteOk X args [] q r 0 && inFrame X.fs [q] then
              match brAtC X { st with fr := (q, callFC X args ((X.G.sig j).env.map (·.1)) r) :: st.fr } with
              | some (st', _, od, of, _) =>
                bif cellK X st' od && cellK X st' of then
                  match endAtC X st' with
                  | some se => match se.seg.exit.kind with
                    | .next t =>
                      bif Nat.beq t (r - X.entry) && se.seg.exit.succ == [t] then
                        match segAtC X t st' with
                        | some sr => (Cnt.max se.cnt st'.cnt).seq fun c ↦ cw ss { sr with cnt := c }
                        | none => .fail 50
                      else .fail 51
                    | _ => .fail 52
                  | none => .fail 53
                else .fail 54
              | none => .fail 55
            else .fail 56
          | none => .fail 57
        | .jump (.gp e) (.fpg S) =>
          match ss with
          | [.ret []] =>
            bif Nat.beq e X.entry && f == X.name && Nat.beq S X.fs && Nat.beq args.length X.nargs &&
                Nat.beq X.nret 0 && !X.main then
              match brAtC X { st with nx := (argFC X.loc 2 args ++ [(0, .hdr 0), (1, .hdr 1)] ++
                  X.self.map (fun o ↦ (o, FC.self))) } with
              | some (st', _, od, of, _) =>
                bif cellK X st' od && cellK X st' of && st'.cnt.le X.pmax then
                  match endAtC X st' with
                  | some se =>
                    bif decide (se.seg.exit.kind = .ret) && se.cnt.le X.pmax then .done else .fail 60
                  | none => .fail 61
                else .fail 62
              | none => .fail 63
            else .fail 64
          | _ => .fail 65
        | _ => .fail 66
      else .fail 67
    | none => .fail 68
  | .ret _ :: _, st =>
    match endAtC X st with
    | some se =>
      bif (bif X.main then decide (se.seg.exit.kind = .jump (.gp (2 ^ 18 - 1)) (.gp 0))
          else decide (se.seg.exit.kind = .ret)) && se.cnt.le X.pmax then .done else .fail 70
    | none => .fail 71

/-- The other arms of a `match`, each from its segment, ending at the join `J`: the most counts
of any. -/
noncomputable def cwArms (J : ℕ) (se : CW) :
    List (List Core.Stmt) → List ℕ → Cnt → Option Cnt
  | [], [], c => some c
  | a :: as, t :: ts, c =>
    match segAtC X t se with
    | some s => (fileB X.loc X.fs a se.book).seq fun B ↦
      match cw a { s with book := B } with
      | .join J' c' => bif Nat.beq J J' then (Cnt.max c c').seq fun c ↦ cwArms J se as ts c
          else none
      | _ => none
    | none => none
  | _, _, _ => none
end

end Walk

/-! ## A function, by windows

Window `i` of function `j` is walked over the segments of the soundness certificate's window
(`execWin` from `(cutAt i).J` to `endAt i`) and its statements (`stmtsAt i`), starting from the
facts of its statements, no frame in flight, and the counts its start hands on
(`Data.cplHands`); it ends at the next window's start within the counts handed on there, or, the
last, by the return within the most a path runs (`Plumb.pmax`). -/

/-- The fixed cells in `[2, n)`, by cell. -/
noncomputable def statT (n : ℕ) : List (ℕ × PC) → Trie PC → Trie PC
  | [], t => t
  | p :: ps, t => bif Nat.ble 2 p.1 && Nat.blt p.1 n then (setF p.2 envDepth t p.1).seq fun t ↦
      statT n ps t else statT n ps t

/-- The counts at window `i`'s start of function `j`. -/
noncomputable def cplHand (j i : ℕ) : Cnt := Cnt.ofList (nth (nth Data.cplHands j []) i [])

/-- The context of window `i` of function `j`. -/
noncomputable def cxOf (j : ℕ) (idx : Trie Exec.Seg) (loc : CLoc) (stat : Trie PC) : CX :=
  ⟨glob, (certOf j).facts, (fnOf j).entry, idx, loc, fsN j, stat, j == 1, (coreOf j).name,
    (coreOf j).params.length, (certOf j).nret, (certOf j).callees, (plumbOf j).sites,
    (plumbOf j).arms, (certOf j).facts.env.map (·.1), Cnt.ofList (plumbOf j).pmax⟩

/-- How window `i` must end: at the next window's start within its counts, or by the return. -/
noncomputable def winEndC (C : Cert) (j i : ℕ) : RC → Bool
  | .join J c => Nat.blt i C.cuts.length && Nat.beq J (C.cutAt (i + 1)).J && c.le (cplHand j (i + 1))
  | .done => !(Nat.blt i C.cuts.length)
  | .fail _ => false

/-- The walk's result of window `i` of function `j`. -/
noncomputable def cplRes (j i : ℕ) : RC :=
  match execWin (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
      ((certOf j).endAt (fnOf j) i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (clocW (certOf j) i).seq fun loc ↦
    (statT (fsN j) (plumbOf j).stat .nil).seq fun stat ↦
    (fileB loc (fsN j) ((certOf j).stmtsAt (coreOf j) i) .nil).seq fun B ↦
    (cplHand j i).seq fun c ↦
    match getF idx ((certOf j).cutAt i).J with
    | some s => cw (cxOf j idx loc stat) ((certOf j).stmtsAt (coreOf j) i)
        ⟨s, s.items, B, [], [], [], c, some s.start⟩
    | none => .fail 90

/-- **The completeness check of window `i` of function `j`**: the window's cells pack, the
first window starts with no counts and its self frame pointer cells fixed, and the walk ends as
`winEndC` says. -/
noncomputable def cplWin (j i : ℕ) : Bool :=
  (nth (certOf j).cells i []).all (fun c ↦ Nat.blt c 65536) &&
  (bif Nat.beq i 0 then (cplHand j 0).le Cnt.zero &&
      (certOf j).facts.env.all (fun p ↦ Sym.beq p.2 (.fpg 0) &&
        decide (getF (statT (fsN j) (plumbOf j).stat .nil) p.1 = some (.fpg 0)))
    else true) &&
  winEndC (certOf j) j i (cplRes j i)

/-- **The completeness check of function `j`**: every window's. -/
noncomputable def CplOk (j : ℕ) : Prop := ∀ i ≤ (certOf j).cuts.length, cplWin j i = true

end
end LeanVM.Guest.B2C
