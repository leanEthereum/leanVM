/-
  LeanVM.Guest.B2C.Cpl

  B2's completeness check of one compiled function: its code runs from its entry to its return
  on a memory whose frame holds what the honest memory puts there, window by window of its
  soundness certificate.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Data.CplParts
public import LeanVM.Guest.Data.CplArms
public import LeanVM.Guest.B2C.Count
public import LeanVM.Guest.ExecC

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
  /-- Each callee frame's header, arguments and self frame pointer cells. -/
  kid : ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    L.read (gpow (kfp + 0)) = some (kidHdr j fp hdr es i).1 ∧
    L.read (gpow (kfp + 1)) = some (kidHdr j fp hdr es i).2 ∧
    (∀ k (hk : k < c.args.length), L.read (gpow (kfp + (2 + k))) = some (σ c.args[k])) ∧
    (∀ o ∈ selfCells c.f, L.read (gpow (kfp + o)) = some (ofK (gpow kfp)))
  /-- A loop's tail call, its last, has its frame right after the caller's. -/
  tail : (coreOf j).loop = true → ∀ kfp, kfps.getLast? = some kfp → kfp = fp + fsN j

/-- **The callees on a path run**: each call entered, from its callee's entry at its frame to its
return registers, executing `ck[i] op` instructions of each opcode, its returns left in its frame's
cells after its arguments. -/
def KidsRun {κ : ℕ} (L : MemImage κ) (σ : Val) (es : List Ev) (kfps : List ℕ) (ck : List (Opcode → ℕ)) :
    Prop :=
  ck.length = (calls es).length ∧ ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    c.taken = true → (∃ r, retRegs L (gpow kfp) = some r ∧
      RunC guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r (ck.getD i 0)) ∧
      ∀ k (hk : k < c.rets.length), L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])


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
  | .add d _ _ => [d]
  | .mul d _ _ => [d]
  | .same a b => [a, b]
  | .load d _ _ => [d]
  | .ne _ _ p => [p]
  | .range x y _ _ _ => [x, y]
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
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      .blake (L.cell m0) (L.cell m1) (L.cell m2) (L.cell m3) (L.cell cv0) (L.cell cv1) (L.cell o0)
        (L.cell o1) (L.cell md)
  | .frameAddr p (r :: rs) => .addr (L.cell p) ((r :: rs).map L.cell)
  | .frameAddr _ [] => .none
  | .hint _ => .none

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

/-- The exponent of the `SET` immediate `(k0, 0, 0)` as a power of `g`. -/
noncomputable def gpE (k0 : ℕ) : Option ℕ := bif Nat.beq k0 1 then some 0 else X.F.pows.find k0

/-- The constant a cell holds: a fixed cell's, a constant's, an `assert !=`'s `1`. -/
noncomputable def cplCstAt (o : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match statAt X o with
  | some (.k k0 k1 k2) => some (k0, k1, k2)
  | _ => (lookC st.book o).findSome? fun a ↦ match a with
    | .const d x => bif Nat.beq d o then some (limbNat x 0, limbNat x 1, limbNat x 2) else none
    | .ne _ _ p => bif Nat.beq p o then some (1, 0, 0) else none
    | _ => none

/-- The cell holds `0`: a constant, or the segment's environment. -/
noncomputable def isZ (o : ℕ) : Bool :=
  (match cplCstAt X st o with
    | some (0, 0, 0) => true
    | _ => false) || isZero (st.seg.env.get o)

/-- The cell holds `1`: a constant, or the segment's environment. -/
noncomputable def isO (o : ℕ) : Bool :=
  (match cplCstAt X st o with
    | some (1, 0, 0) => true
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
    | some (.k _ k1 k2) => Nat.beq k1 0 && Nat.beq k2 0
    | some (.fpg _) => true
    | none => false) ||
  (lookC st.book o).any (fun x ↦ match x with
    | .const d x => Nat.beq d o && Nat.beq (limbNat x 1) 0 && Nat.beq (limbNat x 2) 0
    | .range x y _ _ _ => Nat.beq x o || Nat.beq y o
    | .inK a b => Nat.beq a o || Nat.beq b o
    | .addr p _ => Nat.beq p o
    | .ne _ _ p => Nat.beq p o
    | _ => false) ||
  st.fr.any (fun q ↦ Nat.beq q.1 o) || st.tg.any (fun t ↦ Nat.beq t.1 o) ||
  (st.seg.env.get o).isSome

/-- A `MUL` of a frame address: `fp[a] = fp·g^e₁`, `fp[b] = g^e₂`, the run at `e₁ + e₂`. -/
noncomputable def addrMul (a b : ℕ) (run : List ℕ) : Bool :=
  match statAt X a, cplCstAt X st b, run with
  | some (.fpg e1), some (k0, 0, 0), r :: _ => match gpE X k0 with
    | some e2 => Nat.beq (e1 + e2) r
    | none => false
  | _, _, _ => false

/-- A `MUL` of fixed cells: `fp·g^e = fp·g^e₁ · g^(e - e₁)`. -/
noncomputable def fpgMul (a b d : ℕ) : Bool :=
  match statAt X d, statAt X a, cplCstAt X st b with
  | some (.fpg e), some (.fpg e1), some (k0, 0, 0) => Nat.ble e1 e && (match gpE X k0 with
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
  | .set o k0 k1 k2 => decide (cplCstAt X st o = some (k0, k1, k2))
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
  | .blake2s m0 m1 m2 m3 cv out md =>
    (lookC st.book out).any fun x ↦ match x with
      | .blake n0 n1 n2 n3 c0 c1 o0 o1 d => Nat.beq n0 m0 && Nat.beq n1 m1 && Nat.beq n2 m2 &&
          Nat.beq n3 m3 && Nat.beq c0 cv && Nat.beq c1 (cv + 1) && Nat.beq o0 out &&
          Nat.beq o1 (out + 1) && Nat.beq d md
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
the return, or not at all (with a code saying where). -/
inductive RC where
  | join (J : ℕ) (c : Cnt) (u : ℕ)
  /-- Inside the segment starting at `J`, its first `m` items passed. -/
  | mid (J m : ℕ) (c : Cnt) (u : ℕ)
  | done
  | fail (code : ℕ)

/-- What a caller knows of a function, from its code, core function and certificate (`sigOf`). -/
def mkSig (f : CompiledFn) (c : Core.Fn) (k : Cert) : Sig :=
  ⟨c.name, f.entry, c.params.length, k.nret, k.facts.env, k.pre, k.post, k.mem, k.sem⟩

/-- The functions `fs` with their core functions `cs` and certificates `ks`, numbered from `i`,
filed under their entries (one pass, by the recursor, for the kernel). -/
noncomputable def sigT (fs : List CompiledFn) : List Core.Fn → List Cert → ℕ → Trie (ℕ × Sig) →
    Trie (ℕ × Sig) :=
  List.rec (motive := fun _ ↦ List Core.Fn → List Cert → ℕ → Trie (ℕ × Sig) → Trie (ℕ × Sig))
    (fun _ _ _ t ↦ t)
    (fun f _ r cs ks i t ↦ (setF (i, mkSig f (cs.headD default) (ks.headD default)) indexDepth t
      f.entry).seq fun t ↦ r cs.tail ks.tail (i + 1) t) fs

/-- Every function but `__jump_tables`, with what a caller knows of it, by its entry. -/
@[irreducible] noncomputable def sigTrie : Trie (ℕ × Sig) :=
  sigT Data.functions.tail coreProgram Data.certs.tail 1 .nil

section Walk

variable (X : CX)

/-- The callee at `pc`, with what a caller knows of it: the function entered there (`sigTrie`),
a good one. -/
noncomputable def calleeS (pc : ℕ) : Option (ℕ × Sig) :=
  match getF sigTrie pc with
  | some p => bif X.G.good p.1 then some p else none
  | none => none

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
  | some cs => c.le (nth cs k Cnt.zero)
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
atoms walked in the enclosing blocks. -/
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

/-- Where a block ends: at the start of a segment, at the part's stop inside its segment, or by
its segment's local jump. -/
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
        | _ => .fail 2
      | .error e => .fail e

/-- After a call into the frame `fp[q]` returning to `r`: the position at the return point, its
callee frame's returns known. -/
noncomputable def afterC (st : CW) (q r u : ℕ) (fcs : List (ℕ × FC)) (args rets : List V) :
    Except ℕ CW :=
  match endAtC X { st with fr := (q, fcs) :: st.fr } with
  | .ok se => match segAtC X (r - X.entry) se with
    | some sr => .ok ⟨sr.seg, sr.its, sr.book, (q, fcs ++ argFC X.loc (2 + args.length) rets) :: st.fr,
        sr.tg, sr.nx, sr.cnt, u, bif rets.isEmpty then sr.fresh else none, sr.nm⟩
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
            armsOk X.G X.entry base 0 (t0 :: ts) then
          match endAtC X { st with tg := (t, o1, base) :: st.tg } with
          | .ok se =>
            match segAtC X t0 (armSt (armKeyD X.acs v.idx) se) with
            | some s0 =>
              (fileB X.loc X.fs a0 se.book).seq fun B0 ↦
              match cw a0 { s0 with book := B0 } with
              | .join J c0 u0 =>
                bif armChkK (armKeyD X.acs v.idx) 0 c0 then
                  match cwArms J (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 with
                  | some (c, u) => match segAtC X J se with
                    | some sj => (armCnt (armKeyD X.acs v.idx) se c).seq fun c ↦ natSeq u fun u ↦
                        cw ss { sj with cnt := c, uq := u }
                    | none => .fail 20
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
      bif (bif X.main then decide (se.seg.exit.kind = .jump (.gp (2 ^ 18 - 1)) (.gp 0))
          else decide (se.seg.exit.kind = .ret)) && se.cnt.le X.pmax &&
        Nat.beq vs.length X.nret && runCells (2 + X.nargs) (vs.map X.loc.cell) &&
        inFrame X.fs (vs.map X.loc.cell) then .done else .fail 70
    | .error e => .fail e

/-- The other arms of a `match`, each from its segment, ending at the join `J`: the most counts
of any. -/
noncomputable def cwArms (J : ℕ) (se : CW) (key : Option (List Cnt)) :
    List (List Core.Stmt) → List ℕ → Cnt → ℕ → ℕ → Option (Cnt × ℕ)
  | [], [], c, u, _ => some (c, u)
  | a :: as, t :: ts, c, u, k =>
    match segAtC X t se with
    | some s => (fileB X.loc X.fs a se.book).seq fun B ↦
      match cw a { s with book := B } with
      | .join J' c' u' => bif Nat.beq J J' && armChkK key k c' then
          (Cnt.max c c').seq fun c ↦ natSeq (Nat.lor u u') fun u ↦ cwArms J se key as ts c u (k + 1)
          else none
      | _ => none
    | none => none
  | _, _, _, _, _ => none
end

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

/-- The parts of window `i` of function `j`, `[s, J, counts, set-up cells, m]` each, `m` (absent:
`0`) the items of the segment at `J` before the part (none: one part from the window's start with
nothing handed on). -/
noncomputable def partsOf (j i : ℕ) : List (List ℕ) := nth (nth Data.cplParts j []) i []

/-- The number of parts of a window. -/
noncomputable def nParts (j i : ℕ) : ℕ := Nat.max 1 (partsOf j i).length

/-- The window statement part `k` starts at. -/
noncomputable def partS (j i k : ℕ) : ℕ := nth (nth (partsOf j i) k []) 0 0

/-- The code offset part `k` starts at: the window's start for the first. -/
noncomputable def partJ (j i k : ℕ) : ℕ :=
  bif Nat.beq k 0 then ((certOf j).cutAt i).J else nth (nth (partsOf j i) k []) 1 0

/-- The counts at part `k`'s start. -/
noncomputable def partC (j i k : ℕ) : Cnt := Cnt.ofList ((nth (partsOf j i) k []).drop 2)

/-- The set-up site cells at part `k`'s start. -/
noncomputable def partU (j i k : ℕ) : ℕ := nth (nth (partsOf j i) k []) 8 0

/-- The items of its segment part `k` starts after (`0`: at the segment's start). -/
noncomputable def partM (j i k : ℕ) : ℕ := nth (nth (partsOf j i) k []) 9 0

/-- Where part `k` stops: inside a segment, if the next part starts there. -/
noncomputable def stopOf (j i k : ℕ) : Option (ℕ × ℕ) :=
  bif Nat.blt (k + 1) (nParts j i) && !(Nat.beq (partM j i (k + 1)) 0) then
    some (partJ j i (k + 1), partM j i (k + 1))
  else none

/-- The statements of part `k`. -/
noncomputable def partStmts (j i k : ℕ) : List Core.Stmt :=
  bif Nat.blt (k + 1) (nParts j i) then
    (((certOf j).stmtsAt (coreOf j) i).drop (partS j i k)).take (partS j i (k + 1) - partS j i k)
  else ((certOf j).stmtsAt (coreOf j) i).drop (partS j i k)

/-- The context of window `i` of function `j`. -/
noncomputable def cxOf (j : ℕ) (idx : Trie Exec.Seg) (loc : CLoc) (stat : Trie PC) (nv : ℕ)
    (stop : Option (ℕ × ℕ)) : CX :=
  ⟨glob, (certOf j).facts, (fnOf j).entry, idx, loc, fsN j, stat, j == 1, (coreOf j).name,
    (coreOf j).params.length, (certOf j).nret, (certOf j).callees, (plumbOf j).sites,
    (plumbOf j).arms, (certOf j).facts.env.map (·.1), Cnt.ofList (plumbOf j).pmax, nv, stop,
    nth Data.cplArms j []⟩

/-- The renumbered values a block's own atoms name. -/
def nvOf : List Core.Stmt → ℕ → ℕ
  | [], s => s
  | .atom a :: ss, s => natSeq (nvVals (atomUses a) s) fun s ↦ nvOf ss s
  | _ :: ss, s => nvOf ss s

/-- How part `k` of window `i` must end: at the next part's start, the next window's, within
what is handed on there, or by the return. -/
noncomputable def partEnd (j i k : ℕ) : RC → Bool
  | .join J c u =>
    bif Nat.blt (k + 1) (nParts j i) then
      Nat.beq J (partJ j i (k + 1)) && Nat.beq (partM j i (k + 1)) 0 && c.le (partC j i (k + 1)) &&
        subK u (partU j i (k + 1))
    else Nat.blt i (certOf j).cuts.length && Nat.beq J ((certOf j).cutAt (i + 1)).J &&
      c.le (partC j (i + 1) 0) && subK u (partU j (i + 1) 0)
  | .mid J m c u => Nat.blt (k + 1) (nParts j i) && Nat.beq J (partJ j i (k + 1)) &&
      Nat.beq m (partM j i (k + 1)) && !(Nat.beq m 0) && c.le (partC j i (k + 1)) &&
      subK u (partU j i (k + 1))
  | .done => !(Nat.blt (k + 1) (nParts j i)) && !(Nat.blt i (certOf j).cuts.length)
  | .fail _ => false

/-- The walk's result of part `k` of window `i` of function `j`. -/
noncomputable def cplRes (j i k : ℕ) : RC :=
  match execWinC (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
      ((certOf j).endAt (fnOf j) i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (clocW (certOf j) i).seq fun loc ↦
    (statT (fsN j) (plumbOf j).stat .nil).seq fun stat ↦
    (fileB loc (fsN j) (partStmts j i k) .nil).seq fun B ↦
    (partC j i k).seq fun c ↦ natSeq (partU j i k) fun u ↦ natSeq (partJ j i k) fun J ↦
    natSeq (nvOf (coreOf j).body 0) fun nv ↦ natSeq (partM j i k) fun m ↦
    match getF idx J with
    | some s => bif Nat.beq s.start J then
        cw (cxOf j idx loc stat nv (stopOf j i k)) (partStmts j i k)
          ⟨s, s.items.drop m, B, [], [], [], c, u, bif Nat.beq m 0 then some J else none, 0⟩
      else .fail 91
    | none => .fail 90

/-- The last window's statements: none returns but the last, a `ret`. -/
def lastOkC : List Core.Stmt → Bool
  | [] => false
  | [.ret _] => true
  | s :: ss => Stmt.noRet s && lastOkC ss

/-- What a window's first part also checks: its cells pack, and the function's first window
starts with nothing handed on, its parameters `V.n 0, V.n 1, …` and its self frame pointer cells
fixed. -/
noncomputable def winOkC (j i : ℕ) : Bool :=
  (nth (certOf j).cells i []).all (fun c ↦ Nat.blt c 65536) &&
  Nat.beq (partS j i 0) 0 && Nat.beq (partM j i 0) 0 &&
  (coreOf j).params == (List.range (coreOf j).params.length).map V.n &&
  (bif Nat.beq i 0 then (partC j 0 0).le Cnt.zero && Nat.beq (partU j 0 0) 0 &&
      (certOf j).facts.env.all (fun p ↦ Sym.beq p.2 (.fpg 0) &&
        decide (getF (statT (fsN j) (plumbOf j).stat .nil) p.1 = some (.fpg 0)))
    else true)

/-- The last part of the function's last window. -/
noncomputable def lastPart (j i k : ℕ) : Bool :=
  !(Nat.blt (k + 1) (nParts j i)) && !(Nat.blt i (certOf j).cuts.length)

/-- **The completeness check of part `k` of window `i` of function `j`**: its statements return
only at the function's end, it starts within its window and after the part before it, and its
walk ends as `partEnd` says. -/
noncomputable def cplWin (j i k : ℕ) : Bool :=
  (bif Nat.beq k 0 then winOkC j i else Nat.ble (partS j i (k - 1)) (partS j i k)) &&
  Nat.ble (partS j i k) ((certOf j).stmtsAt (coreOf j) i).length &&
  (bif lastPart j i k then lastOkC (partStmts j i k)
    else Stmt.noRetList (partStmts j i k)) &&
  partEnd j i k (cplRes j i k)

/-- **The completeness check of function `j`**: every part of every window. -/
noncomputable def CplOk (j : ℕ) : Prop :=
  ∀ i ≤ (certOf j).cuts.length, ∀ k < nParts j i, cplWin j i k = true

/-- **What the completeness check gives of function `j`** (`cpl_run`): on a memory holding the
jump table, from an instance's frame holding what the check reads (`FrameHolds`) and its callees'
runs (`KidsRun`), a counted run from its entry to its return registers (`main`: the final ones),
with at most `pathMax` instructions of each opcode besides its callees', its returned values left
in its frame's cells after its arguments. -/
def CplRun (j : ℕ) : Prop :=
  ∀ {κ : ℕ} (L : MemImage κ), κ ≤ 32 → JTHolds glob L →
    (∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2) → ∀ (fp : ℕ), (j = 1 → fp = 0) →
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ (coreOf j).body = .ret es vs →
    (∀ e ∈ es, e.Holds L.read σ) → ∀ (kfps : List ℕ) (hdr : E × E),
    FrameHolds L j fp σ es vs kfps hdr → ∀ ck : List (Opcode → ℕ), KidsRun L σ es kfps ck →
    ∃ (r : Regs K) (c : Opcode → ℕ), (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
      RunC guest L ⟨gpow (fnOf j).entry, gpow fp⟩ r c ∧
      (∀ op, c op ≤ pathCount j σ op + (ck.map (· op)).sum) ∧
      ∀ k (hk : k < vs.length),
        L.read (gpow (fp + (2 + (coreOf j).params.length + k))) = some (σ vs[k])

end
end LeanVM.Guest.B2C
