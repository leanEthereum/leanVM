module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.CoreMode.Bits
public import LeanVM.Guest.Mode.Abs

/-!
# The frame walk

`frameOk` checks, with no generated certificate of its own, that a compiled function finds every
frame cell it reads written: one forward pass over the code, offset by offset, as `Exec.exec` cuts
it (a path's state goes on to the next offset; a jump adds an edge into each later offset it may
reach; at a join the states of the edges into it are met), with `Exec`'s symbolic step (`stepI`:
the words known of frame cells, the last stores, the last instructions) for the values a jump's
kind and a back-solve's divisor need. A path's state (`FSt`) is, besides that:

* `w`, the frame offsets written;
* `nz`, frame cells whose word in the reference is nonzero: a `SET` of a nonzero immediate, a
  `DEREF`'s pointer, a product of nonzero words, a back-solved `MUL`'s divisor, a residual;
* `hq`, cells past the word of a frame cell `q` written (`hqKey q o`): a store through `q`, the
  header a call writes through its callee frame cell, the cells a callee guarantees at return;
* `hs`, cells past the word of `q` holding that word (a loop callee's self frame pointer);
* `cp`, frame cells holding another's word (`MUL c = x·1`, or a `DEREF` through a next frame's
  pointer: a loop's next frame's header and arguments);
* `one`, frame cells holding `1` plus another's word (`XOR c = 1 + x`, for a quotient by `1 + x`).

`w` and `hq` are facts of the executor's memory, monotone in its run; the rest are facts of the
reference image at the frame, true at any time. Each instruction reads written cells: `XOR`,
`MUL` forward or back-solved by a divisor the state knows nonzero (`divOk`), `KECCAK`, a `JUMP`'s
three cells, a `DEREF`'s pointer. A `DEREF` of mode `cell` stores when its frame side is written,
loads when its heap side is known written (`hq`) or its offset is in the oracle `O` (the offsets
whose heap cell the core heap certificate proves written), and links otherwise, learning nothing;
through a cell known to hold `fp·g^e` (a next frame's pointer) its heap side is the frame's own cell
`e + o`, which holds `[c]` and is written once `c` is (`nextF`).
Hints read and write as the mode walk's `stepHints` says of its written cells, stepped from the
written cells among those they may read (`readT`), stack runs at once (`wsRuns`). A taken jump is
one of `Exec`'s kinds: a forward jump; a table jump through a cell to the offsets `tgt` lists
(that it lands at one is a hypothesis of the soundness, the reference's choice); a call, whose
callee frame cell `q` must have its callees' entry cells written past it (and the self frame
pointer of a loop), its return point getting the cells every callee guarantees; a return with the
signature's return cells written; a loop's tail call into `fp·g^e`, its entry cells, self frame
pointer and header held there; `main`'s halting jump.

Everything is structural recursion over lists and tries keyed by `ℕ`, for the kernel; the written
and nonzero cells and the oracle are the bits of a number (`Bits`), which the kernel's `Nat`
operations test, extend, intersect and compare at once. A long function is checked in windows, at
cuts (`FFun.cutAt`) where one path is live and no edge pending, the walk going on from a given
weaker state.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Exec
open LeanVM.Prover.Exec (Hint)

@[expose] public section

/-! ## The state -/

/-- The bound on an offset past a frame cell's word that `hq` and `hs` keep. -/
def hqLim : ℕ := 16384

/-- The key of the cell `o` past frame cell `q`'s word. -/
def hqKey (q o : ℕ) : ℕ := q * hqLim + o

/-- The levels of `hq` and `hs`. -/
def hqDepth : ℕ := 28

/-- The bound on the pcs and frame offsets a jump's target names that the walk relies on. -/
def pcLim : ℕ := 2 ^ 30

/-- A path's state at an offset. -/
structure FSt where
  /-- `Exec`'s state: words of frame cells, the last stores, the last instructions. -/
  st : Exec.St
  /-- Frame offsets written (`Bits`). -/
  w : ℕ
  /-- Frame cells nonzero in the reference (`Bits`). -/
  nz : ℕ
  /-- Cells past a frame cell's word written, by `hqKey`. -/
  hq : Trie Unit
  /-- Cells past a frame cell's word holding that word, by `hqKey`. -/
  hs : Trie Unit
  /-- Frame cells holding another frame cell's word. -/
  cp : Trie ℕ
  /-- Frame cells holding `1` plus another frame cell's word. -/
  one : Trie ℕ

/-- `k A`, `A` and its parts evaluated first. -/
def FSt.force {β : Type} (A : FSt) (k : FSt → β) : β :=
  match A with
  | ⟨st, w, nz, hq, hs, cp, one⟩ =>
    st.seq fun st ↦ natSeq w fun w ↦ natSeq nz fun nz ↦ hq.seq fun hq ↦ hs.seq fun hs ↦ cp.seq fun cp ↦
      one.seq fun one ↦ k ⟨st, w, nz, hq, hs, cp, one⟩

/-- Key `o` is in the set. -/
def has (t : Trie Unit) (o : ℕ) : Bool := (t.get o).isSome

namespace FSt

variable (A : FSt)

/-- Frame offset `o` is written. -/
def hasW (o : ℕ) : Bool := Bits.has A.w o

/-- The cell `o` past frame cell `q`'s word is written. -/
def hasQ (q o : ℕ) : Bool := decide (o < hqLim) && has A.hq (hqKey q o)

/-- The cell `o` past frame cell `q`'s word holds that word. -/
def hasS (q o : ℕ) : Bool := decide (o < hqLim) && has A.hs (hqKey q o)

/-- Frame offset `o` written. -/
def addW (o : ℕ) : FSt := { A with w := Bits.add A.w o }

/-- Frame cell `o` nonzero. -/
def addNz (o : ℕ) : FSt := { A with nz := Bits.add A.nz o }

/-- The cell `o` past frame cell `q`'s word written. -/
noncomputable def addQ (q o : ℕ) : FSt :=
  if o < hqLim then { A with hq := A.hq.set () hqDepth (hqKey q o) } else A

/-- The cell `o` past frame cell `q`'s word holds that word. -/
noncomputable def addS (q o : ℕ) : FSt :=
  if o < hqLim then { A with hs := A.hs.set () hqDepth (hqKey q o) } else A

/-- A known word that is nonzero: `g^e` or `fp·g^e`. -/
def symNz : Option Sym → Bool
  | some (.gp _) => true
  | some (.fpg _) => true
  | _ => false

/-- Frame cell `o` is known nonzero. -/
def nzOf (o : ℕ) : Bool := Bits.has A.nz o || symNz (A.st.env.get o)

/-- `[b] = 0` makes `[x] = 0`: `b` is `x`, or the last instruction is `MUL [b] = [x]·[k]` with `[k]`
nonzero. -/
def zImp (b x : ℕ) : Bool :=
  b == x || match A.st.prev with
    | (_, .mul p q r) :: _ => r == b && ((p == x && A.nzOf q) || (q == x && A.nzOf p))
    | _ => false

/-- The divisor `b` of a back-solved `[c] = …·[b]` is nonzero: known so, or `[c]` known nonzero, or
`[c] = 1 + [x]` with `[b] = 0` making `[x] = 0`. -/
def divOk (b c : ℕ) : Bool :=
  A.nzOf b || A.nzOf c || match A.one.get c with
    | some x => A.zImp b x
    | none => false

/-- The meet of two paths' states, `Exec`'s state restarted at the join. -/
noncomputable def meet (B : FSt) : FSt :=
  ⟨St.init (Trie.inter Sym.beq A.st.env B.st.env), Bits.inter A.w B.w, Bits.inter A.nz B.nz,
    Trie.inter (fun _ _ ↦ true) A.hq B.hq, Trie.inter (fun _ _ ↦ true) A.hs B.hs, Trie.inter Nat.beq A.cp B.cp,
    Trie.inter Nat.beq A.one B.one⟩

/-- `Exec`'s state restarted at a join. -/
def reset : FSt := { A with st := St.init A.st.env }

end FSt

/-! ## What the walk is told -/

/-- What one function's frame walk is told. -/
structure FFun where
  /-- `Exec`'s facts about the function (its entry environment, `main`'s frame, the powers of `g`
  its constants name, the cells whose products by powers of `g` are tracked). -/
  F : Facts
  /-- Its entry pc and length. -/
  entry : ℕ
  len : ℕ
  /-- Its signature: entry cells, self frame pointer cell, return cells. -/
  sig : Mode.Sig
  /-- The callees' signatures by entry pc. -/
  sigs : Trie Mode.Sig
  /-- The halting pc. -/
  halt : ℕ
  /-- Its hints by pc, increasing: the advice's entries in the function. -/
  hints : List (ℕ × List Hint)
  /-- Frame cells nonzero in the reference, by offset (residuals). -/
  nzr : Trie (List ℕ)
  /-- The table a jump through a cell reads, by offset: an index into `arms` (a table jump in the
  frame) or `calls` (a call). -/
  tgt : Trie ℕ
  /-- A table jump's arms, as offsets, increasing, by table. -/
  arms : Trie (List ℕ)
  /-- A table call's callees' pcs, by table. -/
  calls : Trie (List ℕ)
  /-- The oracle: offsets whose heap reads are written. -/
  O : Trie Unit
  /-- The oracle's offsets the walk reads, a list (`Ob`, `OracleOk`). -/
  Ol : List ℕ
  /-- The stores: offsets whose `DEREF` must find its frame side written. -/
  S : Trie Unit
  /-- The cuts' stride: they sit at multiples of it (`cutAt`). -/
  cutW : ℕ
  /-- The live path and pending groups at the cuts, the cut at offset `k * cutW` by `k`. -/
  cuts : Trie (Option FSt × List (ℕ × List ℕ × FSt))

/-- The cut at offset `i`, if any: looked up only at a multiple of the stride, so that the pass, which
asks at every offset, pays a division there and a trie walk only at the cuts. -/
noncomputable def FFun.cutAt (Fn : FFun) (i : ℕ) : Option (Option FSt × List (ℕ × List ℕ × FSt)) :=
  bif Nat.beq (Nat.mod i Fn.cutW) 0 then Fn.cuts.get (Nat.div i Fn.cutW) else none

/-- The oracle's offsets the walk reads, as bits: tested at once, where the oracle's trie would be built
from its list in every check that reads it. -/
noncomputable def FFun.Ob (Fn : FFun) : ℕ := Bits.ofNats Fn.Ol

/-- **The walk reads the oracle**: each offset of `Ol` is the oracle's. -/
def OracleOk (Fn : FFun) : Prop := ∀ i, Bits.has Fn.Ob i = true → has Fn.O i = true

/-- Each offset of `Ol` is the oracle's, decided (`oracleOk_of`). -/
noncomputable def oracleChk (Fn : FFun) : Bool := Fn.Ol.all (has Fn.O)

/-! ## One instruction -/

/-- The written cells as the mode walk's state. -/
def hintAbs (w : Trie Unit) : Mode.Abs := ⟨w, .nil, .nil, [], [], [], [], [], .nil, [], []⟩

/-- The heap pointer cell a hint's destination reads. -/
def destReads : LeanVM.Prover.Exec.BitsDest → List ℕ
  | .stack _ => []
  | .heap ptr => [ptr]

/-- The frame cells a hint may read (`Mode.stepHint`'s `hasW`s). -/
def hintReads : Hint → List ℕ
  | .allocFrames _ _ stop _ _ => [stop]
  | .allocDyn _ size => [size]
  | .allocArm _ sel _ => [sel]
  | .witnessHeap _ ptr _ _ => [ptr]
  | .log2Ceil (.stack base) _ nbits _ => (List.range nbits).map (base + ·)
  | .log2Ceil (.heap ptr) _ _ _ => [ptr]
  | .bitDecompose value bits _ => value :: destReads bits
  | .bitDecomposeExp value bits _ => value :: destReads bits
  | .digitDecomposeExp value dst _ _ _ _ startCell => value :: startCell.toList ++ destReads dst
  | .windowsExp value dest _ _ _ _ => value :: destReads dest
  | .fieldLimbs value _ _ => [value]
  | .inverse value _ => [value]
  | _ => []

/-- The written cells among those the hints may read, as a trie. -/
noncomputable def readT (w : ℕ) (hs : List Hint) : Trie Unit :=
  ((hs.map hintReads).flatten.filter (Bits.has w)).foldl (fun t o ↦ t.set () envDepth o) .nil

/-- Hints that only write stack runs (`witnessStack`, the most frequent): the written cells after
them, else `none`. -/
def wsRuns (w : ℕ) : List Hint → Option ℕ
  | [] => some w
  | .witnessStack _ base len :: hs => wsRuns (Bits.addRun w base len) hs
  | _ :: _ => none

/-- **The hints** at an offset: what they read written, what they write. Stack runs are written at
once; other hints are stepped by the mode walk from the cells they may read, and what it writes
joins the written cells. -/
noncomputable def stepHintsF (A : FSt) : List Hint → Option FSt
  | [] => some A
  | h :: hs => match wsRuns A.w (h :: hs) with
    | some w => some { A with w := w }
    | none => (Mode.stepHints (hintAbs (readT A.w (h :: hs))) (h :: hs)).map fun B ↦
      { A with w := A.w ||| Bits.ofTrie B.w }

/-- The residuals at an offset: nonzero frame cells. -/
noncomputable def addNzs (A : FSt) : List ℕ → FSt
  | [] => A
  | o :: os => addNzs (A.addNz o) os

/-- `[c] = 1 + [x]` from `XOR c = a + b`, one of `a`, `b` known `1`. -/
noncomputable def oneOf (A : FSt) (a b c : ℕ) : Trie ℕ :=
  if isOne (A.st.env.get a) then A.one.set b envDepth c
  else if isOne (A.st.env.get b) then A.one.set a envDepth c
  else A.one

/-- The cells a `KECCAK` reads (`keccakIns`), as bits. -/
def keccakMask (m0 m1 m2 m3 tail b8 cap : ℕ) : ℕ :=
  2 ^ m0 ||| 2 ^ m1 ||| 2 ^ m2 ||| 2 ^ m3 ||| 15 <<< tail ||| 2 ^ b8 ||| 15 <<< cap

/-- A `DEREF` of mode `cell` through frame cell `a` at offset `o`, frame side `c`: a store when `c`
is written, a load when the heap cell is known written or the oracle says so, else a link. -/
noncomputable def cellF (O : ℕ) (i : ℕ) (A : FSt) (a o c : ℕ) : FSt :=
  if A.hasW c then (A.addNz a).addQ a o
  else if A.hasQ a o then (A.addNz a).addW c
  else if Bits.has O i then ((A.addNz a).addW c).addQ a o
  else A.addNz a

/-- After a `DEREF` of mode `cell` (`B`, from `A`) through frame cell `a` known to hold `fp·g^e`
at offset `o`: the frame's own cell `e + o` holds `[c]`, and is written once `c` is. -/
noncomputable def nextF (A B : FSt) (a o c : ℕ) : FSt :=
  match A.st.env.get a with
  | some (.fpg e) =>
    if e + o < pcLim then
      if B.hasW c then { B.addW (e + o) with cp := B.cp.set c envDepth (e + o) }
      else { B with cp := B.cp.set c envDepth (e + o) }
    else B
  | _ => B

/-- A `DEREF`, its pointer cell written: its pointer nonzero, and what its mode writes. -/
noncomputable def derefF (O : ℕ) (i : ℕ) (A : FSt) (a o c : ℕ) : LeanVM.Semantics.DerefMode → FSt
  | .cell => nextF A (if c == a then (cellF O i A a o c).addS a o else cellF O i A a o c) a o c
  | _ => (A.addNz a).addQ a o

/-- **One non-`JUMP` instruction's frame rule** at offset `i`: the cells it reads must be known
written, and what it surely writes and teaches joins. -/
noncomputable def stepF (O : ℕ) (S : Trie Unit) (i : ℕ) (A : FSt) : OffsetInstruction → Option FSt
  | .xor a b c =>
    if A.hasW a && A.hasW b then some { A.addW c with one := oneOf A a b c } else none
  | .mul a b c =>
    if A.hasW a && A.hasW b then
      some (if A.nzOf a && A.nzOf b then (A.addW c).addNz c else A.addW c)
    else if A.hasW c && A.hasW a && A.divOk a c then some ((A.addW b).addNz a)
    else if A.hasW c && A.hasW b && A.divOk b c then some ((A.addW a).addNz b)
    else none
  | .set o k0 k1 => some (if Mode.immNz k0 k1 then (A.addW o).addNz o else A.addW o)
  | .deref a o c mode =>
    if A.hasW a && (!has S i || A.hasW c) then some (derefF O i A a o c mode) else none
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ outCells =>
    if Bits.sub (keccakMask m0 m1 m2 m3 tail b8 cap) A.w then
      some { A with w := Bits.addRun A.w out outCells.cellCount }
    else none
  | .jump .. => none

/-- The copies an instruction's facts teach. -/
noncomputable def addCopies (A : FSt) : List Atom → FSt
  | [] => A
  | .copy d s :: fs => addCopies { A with cp := A.cp.set s envDepth d } fs
  | _ :: fs => addCopies A fs

/-- `Exec`'s step after a non-`JUMP` at pc `pc`: its state, and the copies its facts teach. -/
noncomputable def execF (F : Facts) (pc : ℕ) (A : FSt) (ins : OffsetInstruction) : FSt :=
  match nonJump F pc A.st ins with
  | (fs, env, mem) => addCopies { A with st := A.st.push env mem pc ins } fs

/-! ## Jumps -/

/-- The signatures at pcs. -/
def sigsAt (sigs : Trie Mode.Sig) : List ℕ → Option (List Mode.Sig)
  | [] => some []
  | pc :: pcs => match sigs.get pc, sigsAt sigs pcs with
    | some G, some Gs => some (G :: Gs)
    | _, _ => none

/-- The return cells every one of the callees guarantees. -/
def retsOf : List Mode.Sig → List ℕ
  | [] => []
  | G :: Gs => G.ret.filter fun o ↦ Gs.all fun G' ↦ G'.ret.contains o

/-- The caller has written callee `G`'s entry cells past callee frame cell `q`, and its self frame
pointer there. -/
def calleeOk (A : FSt) (q : ℕ) (G : Mode.Sig) : Bool :=
  G.entry.all (A.hasQ q ·) && match G.self with
    | some o => A.hasQ q o && A.hasS q o
    | none => true

/-- The cells past callee frame cell `q` written at the return point. -/
noncomputable def addRets (A : FSt) (q : ℕ) : List ℕ → FSt
  | [] => A
  | o :: os => addRets (A.addQ q o) q os

/-- The word `fp·g^e` known in frame cell `t`. -/
def fpgAt (A : FSt) (e t : ℕ) : Bool :=
  match A.st.env.get t with
  | some (.fpg e') => e' == e
  | _ => false

/-- `[t]` holds `fp·g^e`, known or through a copy: a loop's next frame's self frame pointer. -/
def selfAt (A : FSt) (e t : ℕ) : Bool :=
  A.hasW t && (fpgAt A e t || match A.cp.get t with
    | some c => fpgAt A e c
    | none => false)

/-- `[t]` holds `[c]`. -/
def cpIs (A : FSt) (t c : ℕ) : Bool :=
  match A.cp.get t with
  | some c' => c' == c
  | none => false

/-- A loop's tail call into frame `fp·g^e`: the next frame's entry cells written, its self frame
pointer `fp·g^e` and its header this frame's, and nothing returned in the frame. -/
def tailOk (G : Mode.Sig) (A : FSt) (e : ℕ) : Bool :=
  G.entry.all (fun o ↦ A.hasW (e + o)) &&
    (match G.self with
      | some o => selfAt A e (e + o)
      | none => true) &&
    cpIs A e 0 && cpIs A (e + 1) 1 && G.ret.isEmpty

/-- The callees' pcs of a call through register `pt`: a constant's, or a table's. -/
def callPcs (Fn : FFun) (i : ℕ) : Tgt → Option (List ℕ)
  | .gp e => if e < pcLim then some [e] else none
  | .cell _ => (Fn.tgt.get i).bind Fn.calls.get
  | .fpg _ => none

/-- A call through callee frame cell `q` to `pt`'s callees, returning to `succ`: each callee's entry
cells written, its return point getting the cells every callee guarantees. -/
noncomputable def callF (Fn : FFun) (i : ℕ) (A : FSt) (q : ℕ) (succ : List ℕ) (pt : Tgt) :
    Option (List ℕ × FSt) :=
  match (callPcs Fn i pt).bind (sigsAt Fn.sigs) with
  | some (G :: Gs) =>
    if (G :: Gs).all (calleeOk A q) then
      match succ with
      | [t] => some ([t], addRets A q (retsOf (G :: Gs)))
      | _ => none
    else none
  | _ => none

/-- A jump to registers `(pt, ft)`: in the frame, `main`'s halt or a table jump's arms; else a
loop's tail call. -/
noncomputable def jumpExF (Fn : FFun) (i : ℕ) (A : FSt) (pt ft : Tgt) : Option (List ℕ × FSt) :=
  if Fn.F.self ft then
    match pt with
    | .gp e => if Fn.F.fpOne && e == Fn.halt && decide (e < pcLim) then some ([], A) else none
    | .cell _ => match Fn.tgt.get i with
      | some k => (Fn.arms.get k).map fun ts ↦ (ts, A)
      | none => none
    | .fpg _ => none
  else
    match ft, pt with
    | .fpg e, .gp e' =>
      if e' == Fn.entry && decide (e < pcLim) && tailOk Fn.sig A e then some ([], A) else none
    | _, _ => none

/-- **A taken jump** at offset `i`, by its exit: its successors and the state there, or `none`. -/
noncomputable def exitF (Fn : FFun) (i : ℕ) (A : FSt) (x : Exit) : Option (List ℕ × FSt) :=
  match x.kind with
  | .next _ => some (x.succ, A)
  | .ret => if Fn.sig.ret.all A.hasW then some ([], A) else none
  | .call pt q _ => callF Fn i A q x.succ pt
  | .jump pt ft => jumpExF Fn i A pt ft

/-- The tag of a taken jump's group: a table jump's table index plus one, else `0`. -/
def tagF (Fn : FFun) (i : ℕ) (x : Exit) : ℕ :=
  match x.kind with
  | .jump (.cell _) ft =>
    if Fn.F.self ft then
      match Fn.tgt.get i with
      | some k => k + 1
      | none => 0
    else 0
  | _ => 0

/-! ## The pass -/

/-- Pending edges into later offsets, in groups: a tag (`0`, or a table's index plus one while
the group's targets are that table's arms), the group's targets, increasing, and the meet of the
states of the jumps into them (a table jump's arms share one state; the arms of a `match` that all
end in a table jump into the next one's form one group). -/
abbrev FPend := List (ℕ × List ℕ × FSt)

/-- Add a jump's edges into the targets `ts` with state `A`, its tag `k`: met into the group of
the same tag (the same table's arms) or, untagged, of the same targets; else a new group last. -/
noncomputable def addGrpF (k : ℕ) (ts : List ℕ) (A : FSt) : FPend → FPend
  | [] => [(k, ts, A)]
  | (k', us, B) :: gs =>
    if (bif k == 0 then ts == us else k == k') then (B.meet A).force fun C ↦ (k', us, C) :: gs
    else headSeq (addGrpF k ts A gs) fun gs ↦ (k', us, B) :: gs

/-- `A` met with `B`, if any. -/
noncomputable def meetOpt (B : FSt) : Option FSt → FSt
  | some A => A.meet B
  | none => B.reset

/-- The meet of the states the groups give offset `i`, if any, and the groups past it (untagged:
their targets are no table's arms any more). -/
noncomputable def popF (i : ℕ) : FPend → Option FSt × FPend
  | [] => (none, [])
  | (k, ts, B) :: gs =>
    match popF i gs with
    | (o, ps) =>
      match ts with
      | t :: ts' =>
        if t = i then (some (meetOpt B o), if ts' = [] then ps else (0, ts', B) :: ps)
        else (o, (k, t :: ts', B) :: ps)
      | [] => (o, ps)

/-- Every target past offset `i`. -/
def pastAll (i : ℕ) (ts : List ℕ) : Bool := ts.all fun t ↦ decide (i < t)

/-- Strictly increasing. -/
def incrF : List ℕ → Bool
  | a :: b :: l => decide (a < b) && incrF (b :: l)
  | _ => true

/-- The edges of a taken jump's exit added, if the walk accepts it: its targets past `i` and
increasing (a table's arms are, by `armsOk`, once their first is). -/
noncomputable def jumpF (Fn : FFun) (i : ℕ) (A : FSt) (x : Exit) (pend : FPend) : Option FPend :=
  match exitF Fn i A x with
  | some ([], _) => some pend
  | some (t :: ts, B) =>
    if (bif tagF Fn i x == 0 then pastAll i (t :: ts) && incrF (t :: ts) else decide (i < t)) then
      some (B.force fun B ↦ addGrpF (tagF Fn i x) (t :: ts) B pend)
    else none
  | none => none

/-- **One path at offset `i`**: its hints `hs`, the residuals, the instruction. What falls through,
and the pending edges. -/
noncomputable def offF (Fn : FFun) (i : ℕ) (hs : List Hint) (A : FSt) (ins : OffsetInstruction)
    (pend : FPend) : Option (Option FSt × FPend) :=
  match stepHintsF A hs with
  | none => none
  | some A =>
    let A := addNzs A ((Fn.nzr.get i).getD [])
    match ins with
    | .jump c d f =>
      if A.hasW c && A.hasW d && A.hasW f then
        optSeq (A.st.env.get c) fun cv ↦
          if isZero cv then some (some A, pend)
          else if isNonzero cv then
            (jumpF Fn i A (jumpExit Fn.F Fn.entry Fn.len i A.st d f) pend).map fun p ↦ (none, p)
          else (jumpF Fn i A (jumpExit Fn.F Fn.entry Fn.len i A.st d f) pend).map fun p ↦ (some A, p)
      else none
    | ins => (stepF Fn.Ob Fn.S i A ins).map fun A ↦ (some (execF Fn.F (Fn.entry + i) A ins), pend)

/-- At offset `i`: the live path met with the edges into it. -/
noncomputable def joinF (i : ℕ) (cur : Option FSt) (pend : FPend) : Option FSt × FPend :=
  match popF i pend with
  | (some P, ps) => (some (match cur with
      | some A => A.meet P
      | none => P), ps)
  | (none, ps) => (cur, ps)

/-- One path is in `B`'s state when every fact of `B` is one of `A`'s. -/
def FSt.sub (B A : FSt) : Bool :=
  B.st.env.sub Sym.beq A.st.env && Bits.sub B.w A.w && Bits.sub B.nz A.nz &&
    B.hq.sub (fun _ _ ↦ true) A.hq && B.hs.sub (fun _ _ ↦ true) A.hs && B.cp.sub Nat.beq A.cp &&
    B.one.sub Nat.beq A.one

/-- The live path is at least the cut's: both none, or the cut's state weaker. -/
def curSub : Option FSt → Option FSt → Bool
  | none, none => true
  | some S, some T => S.sub T
  | _, _ => false

/-- The pending groups are at least the cut's: the same targets, in order, each cut state weaker. -/
def pendSub : FPend → FPend → Bool
  | [], [] => true
  | (k, ts, S) :: ss, (k', us, T) :: tt => k == k' && ts == us && S.sub T && pendSub ss tt
  | _, _ => false

/-- The cut's live path and groups, `Exec`'s states restarted. -/
noncomputable def cutSt (c : Option FSt × FPend) : Option FSt × FPend :=
  (c.1.map FSt.reset, c.2.map fun g ↦ (g.1, g.2.1, g.2.2.reset))

/-- At a cut, the live path and pending groups at least the cut's, which the walk goes on from. -/
noncomputable def cutF (Fn : FFun) (i : ℕ) (cur : Option FSt) (pend : FPend) :
    Option (Option FSt × FPend) :=
  match Fn.cutAt i with
  | some c => if curSub c.1 cur && pendSub c.2 pend then some (cutSt c) else none
  | none => some (cur, pend)

/-- `k o`, `o` and its state evaluated first. -/
def optFSeq {β : Type} (o : Option FSt) (k : Option FSt → β) : β :=
  match o with
  | none => k none
  | some A => A.force fun A ↦ k (some A)

/-- The hints' entries from pc `pc` on (a cursor into a function's hints). -/
def advC (c : List (ℕ × List Hint)) (pc : ℕ) : List (ℕ × List Hint) :=
  c.dropWhile fun p ↦ decide (p.1 < pc)

/-- The hints at pc `pc`, the cursor at `pc`. -/
def hintsC (c : List (ℕ × List Hint)) (pc : ℕ) : List Hint :=
  match c with
  | (p, h) :: _ => if p = pc then h else []
  | [] => []

/-- One offset of the pass, `run` walking the rest. -/
noncomputable def passF (Fn : FFun) (ins : OffsetInstruction)
    (run : ℕ → List (ℕ × List Hint) → Option FSt → FPend → Option (Option FSt × FPend))
    (i : ℕ) (c : List (ℕ × List Hint)) (cur : Option FSt) (pend : FPend) :
    Option (Option FSt × FPend) :=
  headSeq (advC c (Fn.entry + i)) fun c ↦
  match cutF Fn i cur pend with
  | none => none
  | some (cur, pend) =>
    match joinF i cur pend with
    | (none, pend) => natSeq (i + 1) fun i ↦ run i c none pend
    | (some A, pend) =>
      match offF Fn i (hintsC c (Fn.entry + i)) A ins pend with
      | some (cur, pend) => optFSeq cur fun cur ↦ headSeq pend fun pend ↦ natSeq (i + 1) fun i ↦
          run i c cur pend
      | none => none

/-- **The pass** over the code from offset `i`, the hints' cursor at `c`: the live path and the
pending edges after it. -/
noncomputable def frameRun (Fn : FFun) (code : List OffsetInstruction) :
    ℕ → List (ℕ × List Hint) → Option FSt → FPend → Option (Option FSt × FPend) :=
  List.rec (motive := fun _ ↦ ℕ → List (ℕ × List Hint) → Option FSt → FPend → Option (Option FSt × FPend))
    (fun _ _ cur pend ↦ some (cur, pend)) (fun ins _ run ↦ passF Fn ins run) code

/-- The written cells at entry: the signature's entry cells and self frame pointer cell. -/
def entryW (G : Mode.Sig) : ℕ :=
  Bits.ofList (match G.self with
    | some o => o :: G.entry
    | none => G.entry)

/-- The state at entry. -/
noncomputable def entryF (Fn : FFun) : FSt :=
  ⟨St.init Fn.F.entryEnv, entryW Fn.sig, 0, .nil, .nil, .nil, .nil⟩

/-- `Exec`'s entry environment is at most the self frame pointer cell's. -/
def envOk (Fn : FFun) : Bool :=
  Fn.F.env.all fun p ↦ match p.2, Fn.sig.self with
    | .fpg 0, some o => p.1 == o
    | _, _ => false

/-- Every table's arms: increasing offsets in the function. -/
noncomputable def armsOk (Fn : FFun) : Bool :=
  trieAll (fun ts ↦ incrF ts && ts.all fun t ↦ decide (t < Fn.len)) Fn.arms

/-- **The frame walk accepts a function's code**: it goes through from the entry state, no path
falling through its end and no edge left pending. -/
noncomputable def frameOk (Fn : FFun) (code : List OffsetInstruction) : Bool :=
  oracleChk Fn && envOk Fn && armsOk Fn && match frameRun Fn code 0 Fn.hints (some (entryF Fn)) [] with
    | some (none, []) => true
    | _ => false

/-- **A window** `[a, b)` of the pass: from the cut at `a` (the entry state at `0`), it goes
through to the cut at `b`, or through the code's end (`Fn.len`, the code's length, not recomputed).
The function's `envOk` and `armsOk` are decided once, apart from its windows. -/
noncomputable def frameWin (Fn : FFun) (code : List OffsetInstruction) (a b : ℕ) : Bool :=
  (match Fn.cutAt a with
    | some c => some (cutSt c)
    | none => if a = 0 then some (some (entryF Fn), []) else none).elim false fun S ↦
  match frameRun Fn ((code.drop a).take (b - a)) a Fn.hints S.1 S.2 with
  | some (cur, pend) =>
    if b < Fn.len then (cutF Fn b cur pend).isSome
    else match cur, pend with
      | none, [] => true
      | _, _ => false
  | none => false

end

end LeanVM.Guest.CoreMode
