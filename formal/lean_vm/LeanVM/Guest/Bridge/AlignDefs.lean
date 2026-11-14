/-
  LeanVM.Guest.Bridge.AlignDefs

  The hint bridge's alignment check: a forward pass over a function's code pairing its flow hints, branches, table jumps, call sites and returns with body positions, kept as cursors into the body.
-/

module

public import LeanVM.Guest.Bridge.Defs
public import LeanVM.Guest.ExecCore

/-!
# The alignment check

A **cursor** `(up, k)` names a body position: index `k` of the innermost block, `up` the enclosing statements' indices with the sub-block taken (an `ite`'s `0` zero side, `1` other side; a `match`'s arm), innermost first. `blockAt body up` is the innermost block, `posOf body up k` the statements left from there: the rest of the block, then the rest of each enclosing block past its statement. `normC` pops finished blocks and skips the atoms that pop nothing (neither witness nor computed hints), so two arrivals at one offset agree when their cursors are equal.

`alignGo`: a forward pass over the code's offsets, each reached one with its cursor (by fall-through, or from an earlier jump; arrivals at one offset must agree). The flow hints at an offset consume the cursor's head flow hint atoms, each compiling its own (`compiles` under the cell map `locOf locs extra`); a non-jump instruction falls through. A `JUMP oc od of` is, by its cells (`stat`: the frame's fixed cells, `sites`: the call sites, `arms`: the table jumps, `pows`: the powers of `g` the constants name, `jt`: the jump table): a jump never taken (`oc` the constant `0`); a forward jump in the frame (`oc` a nonzero constant, `of` the own frame, `od` a constant pc of the function past this one); else by the statement at the cursor: an `ite c` (`oc` the cell of `c`; the zero side falls through, the other at `od`'s pc), a `match x` (its table jump `(x, od, base)`; arm `j` at the jump table's target of slot `base + j`), a `call` (its site's callee frame `of`, `od` the callee's entry; the rest at the site's return pc), a `callIf c` (`oc` the cell of `c`: a conditional call at its site returning to the next offset, or a loop's tail call to the next frame `fp·g^S` before the closing `ret []`; the rest falls through), a `dispatch` (its site's callee frame and target cells; the rest at the return pc), a `ret` (`od = 0`, `of = 1`; `main`: the halting jump). `alignOk`: the advice's pcs increase from the entry, and the pass reaches the end with no fall-through past it and nothing pending. `alignAt`: the cursor at each offset reached.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree Trie)

@[expose] public section

/-- A body position: the enclosing statements' indices and sub-blocks, innermost first, and the
index in the innermost block. -/
abbrev Cur := List (ℕ × ℕ) × ℕ

/-- Sub-block `c` of a statement: an `ite`'s zero side (`0`) or other side, a `match`'s arm `c`. -/
def subBlock : Stmt → ℕ → List Stmt
  | .ite _ z n, c => bif c == 0 then z else n
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

/-- **The cursor normalized**: finished blocks popped, atoms that pop nothing skipped. -/
def normC (body : List Stmt) : ℕ → List (ℕ × ℕ) → ℕ → Option Cur
  | 0, _, _ => none
  | f + 1, up, k => match (blockAt body up)[k]? with
    | some (.atom a) => bif flowAtom a then some (up, k) else normC body f up (k + 1)
    | some _ => some (up, k)
    | none => match up with
      | [] => some ([], k)
      | (k', _) :: up' => normC body f up' (k' + 1)

/-- The statements are the closing `ret []`. -/
def retNil : List Stmt → Bool
  | [.ret []] => true
  | _ => false

/-- What the alignment check reads of a function beyond its body and code: its cells (`locs`,
`extra`), entry, whether it is `main`, its fixed cells, call sites and table jumps, the powers of
`g` its constants name, the jump table, its callees' entries, the halting pc, its
length, and the normalization's fuel. -/
structure AlignCtx where
  locs : List ℕ
  extra : List (ℕ × ℕ)
  entry : ℕ
  main : Bool
  stat : List (ℕ × B2C.PC)
  sites : List B2C.Site
  arms : List (ℕ × ℕ × ℕ)
  pows : PowTree
  jt : Trie ℕ
  ents : List (String × ℕ)
  halt : ℕ
  len : ℕ
  fuel : ℕ

namespace AlignCtx

variable (X : AlignCtx)

/-- The cell map. -/
def loc : ℕ → ℕ := locOf X.locs X.extra

/-- The fixed word of cell `o`. -/
def statOf (o : ℕ) : Option B2C.PC := X.stat.lookup o

/-- Cell `o` holds the constant `0`. -/
def zeroAt (o : ℕ) : Bool := X.statOf o == some (.k 0 0)

/-- Cell `o` holds a nonzero constant. -/
def nzAt (o : ℕ) : Bool := match X.statOf o with
  | some (.k k0 k1) => !(k0 == 0 && k1 == 0)
  | _ => false

/-- Cell `o` holds the own frame's address (`main`'s: `g^0`). -/
def selfAt (o : ℕ) : Bool := match X.statOf o with
  | some (.fpg 0) => true
  | some (.k 1 0) => X.main
  | _ => false

/-- The pc whose power cell `o` holds as a constant. -/
def pcAt (o : ℕ) : Option ℕ := match X.statOf o with
  | some (.k k0 0) => X.pows.find k0
  | _ => none

/-- The next frame `fp·g^S`, `S ≠ 0`, cell `o` holds. -/
def nextAt (o : ℕ) : Bool := match X.statOf o with
  | some (.fpg S) => !(S == 0)
  | _ => false

/-- The call site of a call by its values. -/
def siteFor (args rets : List V) : Option B2C.Site :=
  X.sites.find? fun s ↦ s.args == args.map (·.idx) && s.rets == rets.map (·.idx)

/-- A pc of the function past offset `i`, as an offset. -/
def fwdOff (i t : ℕ) : Option ℕ := bif Nat.blt (X.entry + i) t then some (t - X.entry) else none

end AlignCtx

/-- The cursors of a `match`'s arms from `j` on, at their targets from slot `base + j`. -/
def armCurs (X : AlignCtx) (body : List Stmt) (i : ℕ) (up : List (ℕ × ℕ)) (k base : ℕ) :
    ℕ → List (List Stmt) → Option (List (ℕ × Cur))
  | _, [] => some []
  | j, _ :: as => match X.jt.get (base + j), normC body X.fuel ((k, j) :: up) 0 with
    | some t, some c => match X.fwdOff i t, armCurs X body i up k base (j + 1) as with
      | some o, some l => some ((o, c) :: l)
      | _, _ => none
    | _, _ => none

/-- **A `JUMP oc od of` at offset `i`**, the cursor `(up, k)`: the cursor falling through, and the
offsets jumped to with theirs. -/
def jumpStep (X : AlignCtx) (body : List Stmt) (i oc od of : ℕ) (up : List (ℕ × ℕ)) (k : ℕ) :
    Option (Option Cur × List (ℕ × Cur)) :=
  bif X.zeroAt oc then some (some (up, k), []) else
  bif X.nzAt oc && X.selfAt of && (match X.pcAt od with
      | some t => (X.fwdOff i t).isSome && Nat.blt t (X.entry + X.len)
      | none => false) then
    (X.pcAt od).bind fun t ↦ (X.fwdOff i t).map fun o ↦ (none, [(o, (up, k))])
  else
  let after := normC body X.fuel up (k + 1)
  match (blockAt body up)[k]? with
  | some (.ite c _ _) =>
    bif X.loc c.idx == oc && X.selfAt of then
      match X.pcAt od, normC body X.fuel ((k, 0) :: up) 0, normC body X.fuel ((k, 1) :: up) 0 with
      | some t, some cz, some cn => (X.fwdOff i t).map fun o ↦ (some cz, [(o, cn)])
      | _, _, _ => none
    else none
  | some (.match_ x arms) =>
    bif X.selfAt of then
      match X.arms.find? (fun a ↦ a.1 == x.idx && a.2.1 == od) with
      | some a => (armCurs X body i up k a.2.2 0 arms).map fun l ↦ (none, l)
      | none => none
    else none
  | some (.call f args rets) =>
    match X.siteFor args rets, X.pcAt od, X.ents.lookup f, after with
    | some s, some t, some t', some c =>
      bif s.q == of && t == t' then (X.fwdOff i s.r).map fun o ↦ (none, [(o, c)]) else none
    | _, _, _, _ => none
  | some (.callIf c f args) =>
    bif X.loc c.idx == oc then
      match X.pcAt od, X.ents.lookup f, after with
      | some t, some t', some ca =>
        bif t == t' then
          bif X.nextAt of then
            bif retNil (posOf body ca.1 ca.2) then some (some ca, []) else none
          else match X.siteFor args [] with
            | some s => bif s.q == of && s.r == X.entry + i + 1 then some (some ca, []) else none
            | none => none
        else none
      | _, _, _ => none
    else none
  | some (.dispatch _ _ args rets) =>
    match X.siteFor args rets, after with
    | some s, some c => bif s.q == of && s.tgt == od then (X.fwdOff i s.r).map fun o ↦ (none, [(o, c)])
        else none
    | _, _ => none
  | some (.ret _) =>
    bif X.main then
      bif X.selfAt of && X.pcAt od == some X.halt then some (none, []) else none
    else bif od == 0 && of == 1 then some (none, []) else none
  | _ => none

/-- The flow hints at an offset consume the cursor's head flow hint atoms, each compiling its own. -/
def hintsStep (X : AlignCtx) (body : List Stmt) : List Prover.Exec.Hint → Cur → Option Cur
  | [], c => some c
  | h :: hs, (up, k) => bif isaFlowHint h then
      match (blockAt body up)[k]? with
      | some (.atom (.hint hc)) =>
        bif compiles X.loc hc h then (normC body X.fuel up (k + 1)).bind (hintsStep X body hs) else none
      | _ => none
    else hintsStep X body hs (up, k)

/-- One instruction at offset `i` from cursor `(up, k)`, past its hints. -/
def insStep (X : AlignCtx) (body : List Stmt) (i : ℕ) (ins : OffsetInstruction) (c : Cur) :
    Option (Option Cur × List (ℕ × Cur)) :=
  match ins with
  | .jump oc od of => jumpStep X body i oc od of c.1 c.2
  | _ => some (some c, [])

/-- The hints at pc `pc` and the rest, the advice's list being by increasing pc. -/
def hintsAt (pc : ℕ) : List (ℕ × List Prover.Exec.Hint) → List Prover.Exec.Hint × List (ℕ × List Prover.Exec.Hint)
  | (p, l) :: hs => bif p == pc then (l, hs) else ([], (p, l) :: hs)
  | [] => ([], [])

/-- **The forward pass** from offset `i`, the cursor falling into it and the offsets jumped to:
each offset reached with its cursor, which is normalized before its hints. -/
def alignGo (X : AlignCtx) (body : List Stmt) : ℕ → List OffsetInstruction → List (ℕ × List Prover.Exec.Hint) →
    Option Cur → List (ℕ × Cur) → Option (List (ℕ × Cur))
  | _, [], _, cur, pend => bif cur.isNone && pend.isEmpty then some [] else none
  | i, ins :: code, hs, cur, pend =>
    let here := pend.filter (·.1 == i)
    let rest := pend.filter (·.1 != i)
    let hh := hintsAt (X.entry + i) hs
    match (match cur with
      | some c => some c
      | none => here.head?.map (·.2)) with
    | none => alignGo X body (i + 1) code hh.2 none rest
    | some c =>
      bif here.all (·.2 == c) then
        match ((normC body X.fuel c.1 c.2).bind (hintsStep X body hh.1)).bind (insStep X body i ins) with
        | some (cur', tg) => (alignGo X body (i + 1) code hh.2 cur' (tg ++ rest)).map ((i, c) :: ·)
        | none => none
      else none

/-- The cursor at each offset reached, from the body's start at offset `0`. -/
def alignRun (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Option (List (ℕ × Cur)) :=
  alignGo X body 0 code d.2.2 (some ([], 0)) []

/-- **The alignment check.** -/
def alignOk (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  d.1 == X.entry && pcsUp d.2.2 && d.2.2.all (fun p ↦ Nat.ble X.entry p.1) && (alignRun X body code d).isSome

/-- **The body position at offset `off`**, where the pass reaches it. -/
def alignAt (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : Option (List Stmt) :=
  ((alignRun X body code d).bind fun l ↦ l.lookup off).map fun c ↦ posOf body c.1 c.2

end

end LeanVM.Guest.Bridge
