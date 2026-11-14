/-
  LeanVM.Guest.Bridge.AlignDefs

  The hint bridge's alignment check: a forward pass over a function's code pairing its flow hints, branches, table jumps, call sites and returns with body positions, kept as zippers into the body.
-/

module

public import LeanVM.Guest.Bridge.Defs
public import LeanVM.Guest.Check

/-!
# The alignment check

A **cursor** `(up, k)` names a body position: index `k` of the innermost block, `up` the enclosing statements' indices with the sub-block taken (an `ite`'s `0` zero side, `1` other side; a `match`'s arm), innermost first. `blockAt body up` is the innermost block, `posOf body up k` the statements left from there: the rest of the block, then the rest of each enclosing block past its statement.

The pass carries a cursor with its statements, a **zipper** (`Zip`): each enclosing level's index, sub-block and statements after it, and the innermost block's statements from `k`, so a step reads the head and never walks from the body's root. `Zip.pos` is the position. `normZ` pops finished blocks and skips the atoms that pop nothing (neither witness nor computed hints), so two arrivals at one offset agree when their cursors (`Zip.keyEq`) are equal.

`alignGo`: a forward pass over the code's offsets (`stepI`), each reached one with its zipper (by fall-through, or from an earlier jump; arrivals at one offset must have one cursor). The flow hints at an offset consume the head flow hint atoms, each compiling its own (`compiles` under the cell map `AlignCtx.locAt`, the certificate's cells but for the hint-only ones); a non-jump instruction falls through. A `JUMP oc od of` is, by its cells (`stat`: the frame's fixed cells, `sites`: the call sites by callee frame cell, `arms`: the table jumps by target cell, the chained `match`es' among them, `pows`: the powers of `g` the constants name, `jt`: the jump table, `ents`: the callees by entry): a jump never taken (`oc` the constant `0`); a forward jump in the frame (`oc` a nonzero constant, `of` the own frame, `od` a constant pc of the function past this one); else by the head statement: an `ite c` (`oc` the cell of `c`; the zero side falls through, the other at `od`'s pc), a `match x` (its table jump through `od`, of selector `x` and table base `base`; arm `j` at the jump table's target of slot `base + j`), a `call` (its site's callee frame `of`, `od` the callee's entry; the rest at the site's return pc), a `callIf c` (`oc` the cell of `c`: a conditional call at its site returning to the next offset, or a loop's tail call to the next frame `fp·g^S` before the closing `ret []`; the rest falls through), a `dispatch` (its site's callee frame and target cells; the rest at the return pc), a `ret` (`od = 0`, `of = 1`; `main`: the halting jump). `alignOk`: the advice's pcs increase from the entry, and the pass reaches the end with no fall-through past it and nothing pending. `alignAt`: the position at each offset reached.

The kernel evaluates by substitution, sharing nothing between a term's copies, so the pass is written for it: the context's tables are tries (`Check.getF`) built once and handed on evaluated (`AlignCtx.seq`), the certificate's cells packed `2^20`-ary, 64 to a chunk (`packGo`), the chunks a trie built by halves (`buildT`); arrivals pending are kept by offset (`insP`), so an offset takes its own from the front (`spanP`); and each recursive walk is a recursor, its state passed on evaluated.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree Trie natSeq)
open LeanVM.Guest.Check (getF setF)

@[expose] public section

/-- A body position: the enclosing statements' indices and sub-blocks, innermost first, and the
index in the innermost block. -/
abbrev Cur := List (ℕ × ℕ) × ℕ

/-- Sub-block `c` of a statement: an `ite`'s zero side (`0`) or other side, a `match`'s arm `c`. -/
def subBlock : Stmt → ℕ → List Stmt
  | .ite _ z n, c => bif Nat.beq c 0 then z else n
  | .match_ _ arms, c => arms.getD c []
  | _, _ => []

/-- The innermost block of a cursor's enclosing statements. -/
def blockAt (body : List Stmt) : List (ℕ × ℕ) → List Stmt
  | [] => body
  | (k, c) :: up => subBlock ((blockAt body up).getD k default) c

/-- **The statements left at a cursor**: the rest of its block, then of each enclosing one. -/
def posOf (body : List Stmt) : List (ℕ × ℕ) → ℕ → List Stmt
  | [], k => body.drop k
  | (k', c) :: up, k => (blockAt body ((k', c) :: up)).drop k ++ posOf body up (k' + 1)

/-- An atom the frame's flow carries: a witness or computed hint. -/
def flowAtom : Atom → Bool
  | .hint h => coreFlow h
  | _ => false

/-- The statements are the closing `ret []`. -/
def retNil : List Stmt → Bool
  | [.ret []] => true
  | _ => false

/-! ## Zippers -/

/-- **A cursor with its statements**: each enclosing level's statement index, sub-block and the
statements after it in its block, innermost first; the index in the innermost block and the
statements from there. -/
structure Zip where
  up : List (ℕ × ℕ × List Stmt)
  k : ℕ
  cur : List Stmt

namespace Zip

/-- The cursor. -/
def key (z : Zip) : Cur := (z.up.map fun e ↦ (e.1, e.2.1), z.k)

/-- The statements left. -/
def pos (z : Zip) : List Stmt := z.cur ++ (z.up.map (·.2.2)).flatten

/-- Into sub-block `c` of the head statement `s`, the statements `ss` after it. -/
def enter (z : Zip) (s : Stmt) (ss : List Stmt) (c : ℕ) : Zip := ⟨(z.k, c, ss) :: z.up, 0, subBlock s c⟩

/-- Past the head statement, the statements `ss` after it. -/
def next (z : Zip) (ss : List Stmt) : Zip := natSeq (Nat.succ z.k) fun k ↦ ⟨z.up, k, ss⟩

/-- The enclosing levels' cursors agree. -/
def upEq : List (ℕ × ℕ × List Stmt) → List (ℕ × ℕ × List Stmt) → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && upEq as bs
  | _, _ => false

/-- The cursors agree. -/
def keyEq (a b : Zip) : Bool := Nat.beq a.k b.k && upEq a.up b.up

/-- The body's start. -/
def init (body : List Stmt) : Zip := ⟨[], 0, body⟩

end Zip

/-- One step of the normalization, `r` the rest of it. -/
def normStep (r : Zip → Option Zip) : Zip → Option Zip
  | ⟨up, k, s :: ss⟩ => match s with
    | .atom a => bif flowAtom a then some ⟨up, k, s :: ss⟩ else natSeq (Nat.succ k) fun k ↦ r ⟨up, k, ss⟩
    | _ => some ⟨up, k, s :: ss⟩
  | ⟨[], k, []⟩ => some ⟨[], k, []⟩
  | ⟨(k', _, ss) :: up, _, []⟩ => natSeq (Nat.succ k') fun k ↦ r ⟨up, k, ss⟩

/-- **The zipper normalized**, within `f` steps: finished blocks popped, atoms that pop nothing
skipped. -/
def normZ (f : ℕ) : Zip → Option Zip :=
  Nat.rec (motive := fun _ ↦ Zip → Option Zip) (fun _ ↦ none) (fun _ r ↦ normStep r) f

/-! ## The context -/

/-- A list's entries stored into the trie `t`, each evaluated, a later entry winning over an earlier
one of its key. -/
noncomputable def trieGo {α : Type} : List (ℕ × α) → Trie α → Trie α
  | [], t => t
  | p :: l, t => (setF p.2 Exec.indexDepth t p.1).seq fun t ↦ trieGo l t

/-- A list's entries as a trie, a later entry winning over an earlier one of its key. -/
noncomputable def trieOf {α : Type} (l : List (ℕ × α)) : Trie α := trieGo l .nil

/-- The entries at even positions. -/
def evens {α : Type} : List α → List α
  | a :: _ :: l => a :: evens l
  | l => l

/-- **A list as a trie**, entry `i` at key `i`, within `d` levels: built by halves, not by stores,
and evaluated. -/
def buildT {α : Type} : ℕ → List α → Trie α
  | 0, _ => .nil
  | _ + 1, [] => .nil
  | d + 1, a :: l => (buildT d (evens l)).seq fun lt ↦ (buildT d (evens l.tail)).seq fun rt ↦ .node (some a) lt rt

/-- The width of a packed cell. -/
def cellBits : ℕ := 20

/-- **The cells packed** `2^cellBits`-ary, 64 to a chunk, the first the lowest digit; `j` cells in
the current chunk `acc`. -/
def packGo : List ℕ → ℕ → ℕ → List ℕ
  | [], _, acc => [acc]
  | c :: cs, j, acc => natSeq (Nat.add acc (Nat.shiftLeft c (Nat.mul cellBits j))) fun a ↦
      bif Nat.beq j 63 then a :: packGo cs 0 0 else natSeq (Nat.succ j) fun j ↦ packGo cs j a

/-- Digit `j` of a packed chunk. -/
def digit (ch j : ℕ) : ℕ := Nat.mod (Nat.shiftRight ch (Nat.mul cellBits j)) (2 ^ cellBits)

/-- What the alignment check reads of a function beyond its body and code: its cells (`loc`, the
certificate's packed, `locOk` that each fits, and `extra`), entry, whether it is `main`, its fixed
cells, call sites by callee frame cell, table jumps by target cell (selector and table base), the
powers of `g` its constants name, the jump table, its callees by entry, the halting pc, its length,
and the normalization's fuel. -/
structure AlignCtx where
  loc : Trie ℕ
  locOk : Bool
  extra : List (ℕ × ℕ)
  entry : ℕ
  main : Bool
  stat : Trie B2C.PC
  sites : Trie B2C.Site
  arms : Trie (ℕ × ℕ)
  pows : PowTree
  jt : Trie ℕ
  ents : Trie String
  halt : ℕ
  len : ℕ
  fuel : ℕ

/-- The table jumps by target cell: a `match`'s, and the chained `match`es' arms' ends'. -/
def armsOf (p : B2C.Plumb) : List (ℕ × ℕ × ℕ) :=
  p.arms.map (fun a ↦ (a.2.1, a.1, a.2.2)) ++
    p.chains.flatMap fun ch ↦ ch.2.2.1.map fun t ↦ (t, ch.2.2.2.1, ch.2.2.2.2)

/-- **The context from a function's data**: its certificate's cells, hint-only cells, entry, whether
it is `main`, plumbing, callees with their entries and length, with the program's powers of `g` and
jump table. -/
noncomputable def AlignCtx.ofData (locs : List ℕ) (extra : List (ℕ × ℕ)) (entry : ℕ) (main : Bool)
    (p : B2C.Plumb) (pows : PowTree) (jt : Trie ℕ) (ents : List (String × ℕ)) (halt len : ℕ) : AlignCtx :=
  ⟨buildT 32 (packGo locs 0 0), locs.all (fun c ↦ Nat.blt c (2 ^ cellBits)), extra, entry, main, trieOf p.stat,
    trieOf (p.sites.map fun s ↦ (s.q, s)), trieOf (armsOf p), pows, jt, trieOf (ents.map fun e ↦ (e.2, e.1)),
    halt, len, 1048576⟩

namespace AlignCtx

variable (X : AlignCtx)

/-- `k X`, the context's tables and numbers evaluated first. -/
def seq {β : Type} (k : AlignCtx → β) : β :=
  X.loc.seq fun loc ↦ X.stat.seq fun stat ↦ X.sites.seq fun sites ↦ X.arms.seq fun arms ↦
    X.ents.seq fun ents ↦ natSeq X.entry fun entry ↦ natSeq X.halt fun halt ↦ natSeq X.len fun len ↦
      natSeq X.fuel fun fuel ↦
        k ⟨loc, X.locOk, X.extra, entry, X.main, stat, sites, arms, X.pows, X.jt, ents, halt, len, fuel⟩

/-- The cell map. -/
noncomputable def locAt (i : ℕ) : ℕ :=
  (X.extra.lookup i).getD (match getF X.loc (Nat.div i 64) with
    | some ch => digit ch (Nat.mod i 64)
    | none => 0)

/-- The fixed word of cell `o`. -/
noncomputable def statOf (o : ℕ) : Option B2C.PC := getF X.stat o

/-- Cell `o` holds the constant `0`. -/
noncomputable def zeroAt (o : ℕ) : Bool := match X.statOf o with
  | some (.k k0 k1) => Nat.beq k0 0 && Nat.beq k1 0
  | _ => false

/-- Cell `o` holds a nonzero constant. -/
noncomputable def nzAt (o : ℕ) : Bool := match X.statOf o with
  | some (.k k0 k1) => !(Nat.beq k0 0 && Nat.beq k1 0)
  | _ => false

/-- Cell `o` holds the own frame's address (`main`'s: `g^0`). -/
noncomputable def selfAt (o : ℕ) : Bool := match X.statOf o with
  | some (.fpg 0) => true
  | some (.k 1 0) => X.main
  | _ => false

/-- The pc whose power cell `o` holds as a constant. -/
noncomputable def pcAt (o : ℕ) : Option ℕ := match X.statOf o with
  | some (.k k0 0) => X.pows.find k0
  | _ => none

/-- The next frame `fp·g^S`, `S ≠ 0`, cell `o` holds. -/
noncomputable def nextAt (o : ℕ) : Bool := match X.statOf o with
  | some (.fpg S) => !(Nat.beq S 0)
  | _ => false

/-- The call site of callee frame cell `q`, by its values. -/
noncomputable def siteAt (q : ℕ) (args rets : List V) : Option B2C.Site := match getF X.sites q with
  | some s => bif s.args == args.map (·.idx) && s.rets == rets.map (·.idx) then some s else none
  | none => none

/-- `f` is the callee of entry `t`. -/
noncomputable def entOk (t : ℕ) (f : String) : Bool := match getF X.ents t with
  | some f' => f' == f
  | none => false

/-- A pc of the function past offset `i`, as an offset. -/
def fwdOff (i t : ℕ) : Option ℕ :=
  bif Nat.blt (Nat.add X.entry i) t then natSeq (Nat.sub t X.entry) some else none

end AlignCtx

/-! ## The pass -/

/-- The zippers of a `match`'s arms from `j` on, at their targets from slot `base + j`. -/
noncomputable def armZs (X : AlignCtx) (i : ℕ) (z : Zip) (s : Stmt) (ss : List Stmt) (base : ℕ) :
    ℕ → List (List Stmt) → Option (List (ℕ × Zip))
  | _, [] => some []
  | j, _ :: as => match getF X.jt (Nat.add base j), normZ X.fuel (z.enter s ss j) with
    | some t, some c => match X.fwdOff i t, armZs X i z s ss base (j + 1) as with
      | some o, some l => some ((o, c) :: l)
      | _, _ => none
    | _, _ => none

/-- A forward jump in the frame: `oc` a nonzero constant, `of` the own frame, `od` a constant pc of
the function past offset `i`. -/
noncomputable def fwdJ (X : AlignCtx) (i oc od of : ℕ) : Bool :=
  X.nzAt oc && X.selfAt of && (match X.pcAt od with
    | some t => (X.fwdOff i t).isSome && Nat.blt t (Nat.add X.entry X.len)
    | none => false)

/-- A table jump from `z` through the table at `base` was registered, its arrivals all still pending
past offset `i`. -/
def tabHit (tabs : List (ℕ × Zip × ℕ)) (base : ℕ) (z : Zip) (i : ℕ) : Bool :=
  tabs.any fun t ↦ Nat.beq t.1 base && Zip.keyEq t.2.1 z && Nat.blt i t.2.2

/-- **A jump by the head statement**, at offset `i`, the zipper `z`, the table jumps registered `tabs`
(a chained `match`'s arms each jump through one table, to one set of arrivals). -/
noncomputable def headStep (X : AlignCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) (z : Zip) :
    Option (Option Zip × List (ℕ × Zip)) :=
  match z.cur with
  | s@(.ite c _ _) :: ss =>
    bif Nat.beq (X.locAt c.idx) oc && X.selfAt of then
      match X.pcAt od, normZ X.fuel (z.enter s ss 0), normZ X.fuel (z.enter s ss 1) with
      | some t, some cz, some cn => (X.fwdOff i t).map fun o ↦ (some cz, [(o, cn)])
      | _, _, _ => none
    else none
  | s@(.match_ x arms) :: ss =>
    bif X.selfAt of then
      match getF X.arms od with
      | some a => bif Nat.beq a.1 x.idx then
          bif tabHit tabs a.2 z i then some (none, []) else (armZs X i z s ss a.2 0 arms).map fun l ↦ (none, l)
        else none
      | none => none
    else none
  | .call f args rets :: ss =>
    match X.siteAt of args rets, X.pcAt od, normZ X.fuel (z.next ss) with
    | some s, some t, some c =>
      bif X.entOk t f then (X.fwdOff i s.r).map fun o ↦ (none, [(o, c)]) else none
    | _, _, _ => none
  | .callIf c f args :: ss =>
    bif Nat.beq (X.locAt c.idx) oc then
      match X.pcAt od, normZ X.fuel (z.next ss) with
      | some t, some ca =>
        bif X.entOk t f then
          bif X.nextAt of then
            bif retNil ca.pos then some (some ca, []) else none
          else match X.siteAt of args [] with
            | some s => bif Nat.beq s.r (X.entry + i + 1) then some (some ca, []) else none
            | none => none
        else none
      | _, _ => none
    else none
  | .dispatch _ _ args rets :: ss =>
    match X.siteAt of args rets, normZ X.fuel (z.next ss) with
    | some s, some c => bif Nat.beq s.tgt od then (X.fwdOff i s.r).map fun o ↦ (none, [(o, c)]) else none
    | _, _ => none
  | .ret _ :: _ =>
    bif X.main then
      bif X.selfAt of && X.pcAt od == some X.halt then some (none, []) else none
    else bif Nat.beq od 0 && Nat.beq of 1 then some (none, []) else none
  | _ => none

/-- **A `JUMP oc od of` at offset `i`**, the zipper `z`: the zipper falling through, and the offsets
jumped to with theirs. -/
noncomputable def jumpStep (X : AlignCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) (z : Zip) :
    Option (Option Zip × List (ℕ × Zip)) :=
  bif X.zeroAt oc then some (some z, []) else
  bif fwdJ X i oc od of then (X.pcAt od).bind fun t ↦ (X.fwdOff i t).map fun o ↦ (none, [(o, z)])
  else headStep X i oc od of tabs z

/-- One hint at an offset, `r` the rest: a flow hint consumes the zipper's head flow hint atom,
compiling it. -/
noncomputable def hintStep (X : AlignCtx) (r : Zip → Option Zip) (h : Prover.Exec.Hint) (z : Zip) : Option Zip :=
  bif isaFlowHint h then
    match z.cur with
    | .atom (.hint hc) :: ss => bif compiles X.locAt hc h then (normZ X.fuel (z.next ss)).bind r else none
    | _ => none
  else r z

/-- The flow hints at an offset consume the zipper's head flow hint atoms, each compiling its own. -/
noncomputable def hintsStep (X : AlignCtx) (hs : List Prover.Exec.Hint) : Zip → Option Zip :=
  List.rec (motive := fun _ ↦ Zip → Option Zip) some (fun h _ r ↦ hintStep X r h) hs

/-- One instruction at offset `i` from zipper `z`, past its hints. -/
noncomputable def insStep (X : AlignCtx) (i : ℕ) (ins : OffsetInstruction) (tabs : List (ℕ × Zip × ℕ))
    (z : Zip) : Option (Option Zip × List (ℕ × Zip)) :=
  match ins with
  | .jump oc od of => jumpStep X i oc od of tabs z
  | _ => some (some z, [])

/-- The hints at pc `pc` and the rest, the advice's list being by increasing pc. -/
def hintsAt (pc : ℕ) : List (ℕ × List Prover.Exec.Hint) → List Prover.Exec.Hint × List (ℕ × List Prover.Exec.Hint)
  | (p, l) :: hs => bif Nat.beq p pc then (l, hs) else ([], (p, l) :: hs)
  | [] => ([], [])

/-- A pending arrival inserted by offset. -/
def insP (a : ℕ × Zip) (l : List (ℕ × Zip)) : List (ℕ × Zip) :=
  List.rec (motive := fun _ ↦ List (ℕ × Zip)) [a] (fun b l r ↦ bif Nat.blt b.1 a.1 then b :: r else a :: b :: l) l

/-- Pending arrivals inserted by offset. -/
def mergeP (as l : List (ℕ × Zip)) : List (ℕ × Zip) :=
  List.rec (motive := fun _ ↦ List (ℕ × Zip)) l (fun a _ r ↦ insP a r) as

/-- The arrivals at offset `i` in front, and the rest. -/
def spanP (i : ℕ) (l : List (ℕ × Zip)) : List (ℕ × Zip) × List (ℕ × Zip) :=
  List.rec (motive := fun _ ↦ List (ℕ × Zip) × List (ℕ × Zip)) ([], [])
    (fun a l r ↦ bif Nat.beq a.1 i then (match r with | (h, t) => (a :: h, t)) else ([], a :: l)) l

/-- **The pass's state** at offset `i`: the hints from it, the zipper falling in, the arrivals
pending, and the table jumps registered. -/
structure St where
  i : ℕ
  hs : List (ℕ × List Prover.Exec.Hint)
  cur : Option Zip
  pend : List (ℕ × Zip)
  tabs : List (ℕ × Zip × ℕ)

/-- The least offset of arrivals. -/
def minOff (tg : List (ℕ × Zip)) : ℕ := tg.foldr (fun p m ↦ Nat.min p.1 m) (2 ^ 64)

/-- A `match`'s table jump at the zipper `z`, through the table at `base`, to the arrivals `tg`,
registered. -/
noncomputable def tabReg (X : AlignCtx) (ins : OffsetInstruction) (z : Zip) (tg : List (ℕ × Zip))
    (tabs : List (ℕ × Zip × ℕ)) : List (ℕ × Zip × ℕ) :=
  match ins, z.cur, tg with
  | .jump _ od _, .match_ _ _ :: _, _ :: _ => match getF X.arms od with
    | some a => (a.2, z, minOff tg) :: tabs
    | none => tabs
  | _, _, _ => tabs

/-- The arrivals at an offset have the cursor of `c`. -/
def allKey (here : List (ℕ × Zip)) (c : Zip) : Bool := here.all fun p ↦ Zip.keyEq p.2 c

/-- Offset `i` reached with zipper `c`, normalized before its hints `h1`, to offset `i'` with the
hints `hs'`, the arrivals `rest` pending; with what it records. -/
noncomputable def visit (X : AlignCtx) (ins : OffsetInstruction) (i i' : ℕ) (h1 : List Prover.Exec.Hint)
    (hs' : List (ℕ × List Prover.Exec.Hint)) (rest : List (ℕ × Zip)) (tabs : List (ℕ × Zip × ℕ)) (c : Zip) :
    Option (St × Option (ℕ × Zip)) :=
  ((normZ X.fuel c).bind (hintsStep X h1)).bind fun z ↦ (insStep X i ins tabs z).map fun r ↦
    (⟨i', hs', r.1, mergeP r.2 rest, tabReg X ins z r.2 tabs⟩, some (i, c))

/-- **One offset of the pass**: the zipper falling in, or else the first arrival pending, normalized
before its hints; the offset with its zipper, where reached. -/
noncomputable def stepI (X : AlignCtx) (ins : OffsetInstruction) (st : St) : Option (St × Option (ℕ × Zip)) :=
  natSeq (Nat.succ st.i) fun i' ↦
  match spanP st.i st.pend, hintsAt (Nat.add X.entry st.i) st.hs with
  | (here, rest), (h1, hs') =>
    match st.cur, here with
    | some c, _ => bif allKey here c then visit X ins st.i i' h1 hs' rest st.tabs c else none
    | none, [] => some (⟨i', hs', none, rest, st.tabs⟩, none)
    | none, p :: _ => bif allKey here p.2 then visit X ins st.i i' h1 hs' rest st.tabs p.2 else none

/-- **The forward pass** over the instructions from the state's offset, recording in `acc` each
offset reached with its zipper. -/
noncomputable def alignGo (X : AlignCtx) (code : List OffsetInstruction) :
    St → List (ℕ × Zip) → Option (St × List (ℕ × Zip)) :=
  List.rec (motive := fun _ ↦ St → List (ℕ × Zip) → Option (St × List (ℕ × Zip))) (fun st acc ↦ some (st, acc))
    (fun ins _ r st acc ↦ (stepI X ins st).bind fun p ↦ r p.1 (p.2.toList ++ acc)) code

/-- The pass's end: no fall-through past the code and nothing pending. -/
def alignEnd (st : St) (acc : List (ℕ × Zip)) : Option (List (ℕ × Zip)) :=
  bif st.cur.isNone && st.pend.isEmpty then some acc else none

/-- The zipper at each offset reached, from the body's start at offset `0`. -/
noncomputable def alignRun (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Option (List (ℕ × Zip)) :=
  (alignGo X code ⟨0, d.2.2, some (Zip.init body), [], []⟩ []).bind fun p ↦ alignEnd p.1 p.2

/-- **The alignment check**, the context evaluated first. -/
noncomputable def alignOk (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  X.seq fun X ↦ X.locOk && Nat.beq d.1 X.entry && pcsUp d.2.2 &&
    d.2.2.all (fun p ↦ Nat.ble X.entry p.1) && (alignRun X body code d).isSome

/-- **The body position at offset `off`**, where the pass reaches it. -/
noncomputable def alignAt (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : Option (List Stmt) :=
  ((alignRun X body code d).bind fun l ↦ l.lookup off).map Zip.pos

/-! ## Windows

A long function's pass is checked in windows of offsets. A state is named by its cursors (`KSt`: the
offset, the hints consumed, the cursor falling in, the arrivals pending), each zipper rebuilt from the
body (`zipOf`), and `winOk` runs the pass from one named state over the window's instructions to the
next. -/

/-- The enclosing levels of a cursor with their statements after them. -/
def zUp (body : List Stmt) : List (ℕ × ℕ) → List (ℕ × ℕ × List Stmt)
  | [] => []
  | (k', c) :: up => (k', c, (blockAt body up).drop (k' + 1)) :: zUp body up

/-- **The zipper of a cursor.** -/
def zipOf (body : List Stmt) (up : List (ℕ × ℕ)) (k : ℕ) : Zip := ⟨zUp body up, k, (blockAt body up).drop k⟩

/-- **A pass state by its cursors**: the offset, the hints consumed, the cursor falling in, the
arrivals pending. -/
structure KSt where
  i : ℕ
  nd : ℕ
  cur : Option Cur
  pend : List (ℕ × Cur)
  tabs : List (ℕ × Cur × ℕ)
  deriving DecidableEq

/-- The state a `KSt` names. -/
def stOfK (body : List Stmt) (hs : List (ℕ × List Prover.Exec.Hint)) (K : KSt) : St :=
  ⟨K.i, hs.drop K.nd, K.cur.map (fun c ↦ zipOf body c.1 c.2), K.pend.map (fun p ↦ (p.1, zipOf body p.2.1 p.2.2)),
    K.tabs.map fun t ↦ (t.1, zipOf body t.2.1.1 t.2.1.2, t.2.2)⟩

/-- The length of `l` plus `n`, by a tail call the kernel runs in a loop. -/
def lenTR {α : Type} : List α → ℕ → ℕ
  | [], n => n
  | _ :: l, n => natSeq (Nat.succ n) fun n ↦ lenTR l n

/-- The name of a state, its hints from `hs`. -/
def keyOfSt (hs : List (ℕ × List Prover.Exec.Hint)) (st : St) : KSt :=
  ⟨st.i, lenTR hs 0 - lenTR st.hs 0, st.cur.map Zip.key, st.pend.map (fun p ↦ (p.1, p.2.key)),
    st.tabs.map fun t ↦ (t.1, t.2.1.key, t.2.2)⟩

/-- **A window of the pass**: from the state `Ka` at offset `Ka.i` over the instructions to offset
`Kb.i`, the pass reaches `Kb`. -/
noncomputable def winOk (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (Ka Kb : KSt) : Bool :=
  X.seq fun X ↦ decide ((alignGo X ((code.drop Ka.i).take (Kb.i - Ka.i)) (stOfK body d.2.2 Ka) []).map
    (fun p ↦ keyOfSt d.2.2 p.1) = some Kb)

/-- The last state of a chain: at the end, no fall-through past it, nothing pending. -/
def chainEnd (code : List OffsetInstruction) (K : KSt) : Bool :=
  Nat.beq K.i (lenTR code 0) && K.cur.isNone && K.pend.isEmpty

/-- The checks of `alignOk` but the pass's. -/
noncomputable def alignPre (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  X.locOk && Nat.beq d.1 X.entry && pcsUp d.2.2 && d.2.2.all (fun p ↦ Nat.ble X.entry p.1)

end

end LeanVM.Guest.Bridge
