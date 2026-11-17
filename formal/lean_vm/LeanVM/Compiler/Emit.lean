/-
  LeanVM.Compiler.Emit

  Emission: a placed function to its labelled code, each placed statement the instructions the
  Rust lowering emits for it (`crates/zkdsl_compiler/src/lower.rs`, `lower/call.rs`).
-/

module

public import LeanVM.Compiler.Ir
public import LeanVM.Compiler.Map

/-!
# Emission

`emitBlock` writes a block of placed statements onto the code so far, by structural recursion.
It allocates nothing and reads no pool: the only thing it computes is positions. A `SET` of a
jump target names the instruction it jumps to by its index in the function (`KVal.local`), which
is the length of the code before the target: `size` gives the length of a statement's code, so
every target is known where its `SET` is written, with no backpatching.

The calling convention (`lib.rs`, "Calling convention"; `Abi` in `lower.rs`): a frame's cells
`0` and `1` hold the return pc and the caller's frame pointer, the arguments follow from cell
`2`, then the return cells.

Invariants (stated, not proved here): `(emitBlock f b acc).1.size = acc.size + blockSize b`
(`emitBlock_size`), which is what makes every `KVal.local` the index of the instruction meant;
and the slots a `chain` fills are those of its tables, each once.
-/

namespace LeanVM.Compiler

open LeanVM.Guest LeanVM.Semantics

@[expose] public section

/-- The first argument cell of a frame (`Abi::arg`). -/
def argBase : Nat := 2

/-- A jump table slot's value: the slot and the instruction it enters. -/
abbrev Fill := Nat × KVal

mutual
/-- The number of instructions of a placed statement. -/
def stmtSize : PStmt → Nat
  | .op _ _ => 1
  | .ite _ _ _ _ zero hasElse _ _ nonzero =>
      2 + blockSize zero + (if hasElse then 2 + blockSize nonzero else 0)
  | .chain _ _ _ _ _ _ _ stages => 3 + stagesSize stages
  | .call _ c => 1 + c.args.length + (if c.loop.isSome then 1 else 0) + 3 + c.rets.length
  | .loopNext _ _ _ _ _ _ args => 1 + args.length + 4
  | .dispatch _ _ _ _ _ _ _ _ args rets => args.length + 5 + rets.length
  | .ret _ _ => 1
  | .halt _ _ _ => 2

def blockSize : List PStmt → Nat
  | [] => 0
  | s :: ss => stmtSize s + blockSize ss

def armsSize : List (List PStmt) → Nat
  | [] => 0
  | a :: as => blockSize a + armsSize as

def stagesSize : List (List (List PStmt)) → Nat
  | [] => 0
  | s :: ss => armsSize s + stagesSize ss
end

/-- An instruction with no hint. -/
def bare (o : LOp) : LInstr := ⟨o, []⟩

/-- The instructions of a call (`lower_call`): `SET entry`, the arguments stored through the
callee's frame pointer (the frame's allocation hint on the first store), a registered loop's own
frame pointer, the return target (this frame's own for a tail call), the jump, and the returned
words read back. -/
def emitCall (hints : List LHint) (c : CallSite) : List LInstr :=
  let n := c.args.length
  let alloc : LHint := match c.loop with
    | some count => .allocLoopFrames c.nfp c.callee count (argBase + n + 1)
    | none => .allocFrame c.nfp c.callee
  let stores : List LOp :=
    (c.args.zipIdx.map fun (a, k) => LOp.deref c.nfp (argBase + k) a .cell) ++
    (if c.loop.isSome then [LOp.deref c.nfp (argBase + n) c.nfp .cell] else []) ++
    (if c.tail then [LOp.deref c.nfp 1 1 .cell, LOp.deref c.nfp 0 0 .cell]
     else [LOp.deref c.nfp 1 0 .fp, LOp.deref c.nfp 0 0 .pc])
  let stores : List LInstr := match stores with
    | [] => []
    | s :: ss => ⟨s, [alloc]⟩ :: ss.map bare
  [⟨.set c.entry (.entry c.callee), hints⟩] ++ stores ++ [bare (.jump c.oc c.entry c.nfp)] ++
    c.rets.zipIdx.map fun (r, i) => bare (.deref c.nfp (argBase + n + i) r .cell)

/-- The instructions of a loop helper's closing call (`lower_call`, the loop arm): the arguments,
the next frame's pointer and the return registers copied into the next frame, then the jump. -/
def emitLoopNext (hints : List LHint) (callee : String) (nfp entry oc one : Cell)
    (args : List Cell) : List LInstr :=
  [⟨.set entry (.entry callee), hints⟩] ++
    (args.zipIdx.map fun (a, k) => bare (.mulNextFrame a one (argBase + k))) ++
    [bare (.mulNextFrame nfp one (argBase + args.length)), bare (.mulNextFrame 1 one 1),
     bare (.mulNextFrame 0 one 0), bare (.jump oc entry nfp)]

/-- The instructions of a fused `match` of calls (`lower_dispatched_call`), the first at
instruction `pos`: the shared frame's arguments and return frame pointer, its return pc set to
the join past the jump, the jump through the table, and the returned words read back. -/
def emitDispatch (pos : Nat) (hints : List LHint) (callees : List String)
    (nfp joinCell x entry one : Cell) (first : Nat) (args rets : List Cell) : List LInstr :=
  let n := args.length
  let stores : List LOp :=
    (args.zipIdx.map fun (a, k) => LOp.deref nfp (argBase + k) a .cell) ++ [LOp.deref nfp 1 0 .fp]
  let stores : List LInstr := match stores with
    | [] => []
    | s :: ss => ⟨s, hints ++ [.allocFrameMax nfp callees]⟩ :: ss.map bare
  stores ++
    [bare (.set joinCell (.local (pos + n + 5))), bare (.deref nfp 0 joinCell .cell),
     bare (.slot x first entry), bare (.jump one entry nfp)] ++
    rets.zipIdx.map fun (r, i) => bare (.deref nfp (argBase + n + i) r .cell)

mutual
/-- The code of a placed statement of the function `f`, onto the code so far, and the jump
table slots it fills. -/
def emitStmt (f : String) : PStmt → Rev LInstr × Rev Fill → Rev LInstr × Rev Fill
  | .op hints o, (code, fills) => (code.push ⟨o, hints⟩, fills)
  | .ite hints c bdest sfp zero hasElse edest one nonzero, (code, fills) =>
      let pos := code.size
      let afterZero := pos + 2 + blockSize zero
      let elseAt := if hasElse then afterZero + 2 else afterZero
      let code := (code.push ⟨.set bdest (.local elseAt), hints⟩).push (bare (.jump c bdest sfp))
      let (code, fills) := emitBlock f zero (code, fills)
      if !hasElse then (code, fills)
      else
        let code := (code.push (bare (.set edest (.local (elseAt + blockSize nonzero))))).push
          (bare (.jump one edest sfp))
        emitBlock f nonzero (code, fills)
  | .chain hints join x entry one sfp firsts stages, (code, fills) =>
      let pos := code.size
      let code := ((code.push ⟨.set join (.local (pos + 3 + stagesSize stages)), hints⟩).push
        (bare (.slot x (firsts.headD 0) entry))).push (bare (.jump one entry sfp))
      emitStages f firsts stages (code, fills)
  | .call hints c, (code, fills) => (code.appendList (emitCall hints c), fills)
  | .loopNext hints callee nfp entry oc one args, (code, fills) =>
      (code.appendList (emitLoopNext hints callee nfp entry oc one args), fills)
  | .dispatch hints callees nfp joinCell x entry one first args rets, (code, fills) =>
      (code.appendList (emitDispatch code.size hints callees nfp joinCell x entry one first args
        rets), fills)
  | .ret hints one, (code, fills) => (code.push ⟨.jump one 0 1, hints⟩, fills)
  | .halt hints one dest, (code, fills) =>
      ((code.push ⟨.set dest .endSentinel, hints⟩).push (bare (.jump one dest one)), fills)

def emitBlock (f : String) : List PStmt → Rev LInstr × Rev Fill → Rev LInstr × Rev Fill
  | [], acc => acc
  | s :: ss, acc => emitBlock f ss (emitStmt f s acc)

/-- The arms of a `match` whose table is at `first`, from arm `j`: each fills its slot with its
first instruction. -/
def emitArms (f : String) (first : Nat) :
    List (List PStmt) → Nat → Rev LInstr × Rev Fill → Rev LInstr × Rev Fill
  | [], _, acc => acc
  | a :: as, j, (code, fills) =>
      emitArms f first as (j + 1) (emitBlock f a (code, fills.push (first + j, .at f code.size)))

def emitStages (f : String) : List Nat → List (List (List PStmt)) →
    Rev LInstr × Rev Fill → Rev LInstr × Rev Fill
  | _, [], acc => acc
  | firsts, s :: ss, acc => emitStages f firsts.tail ss (emitArms f (firsts.headD 0) s 0 acc)
end

/-- The labelled code of a placed function, and the jump table slots it fills. -/
def emitFn (p : PFn) : Lowered × Array Fill :=
  let (code, fills) := emitBlock p.name p.body ({}, {})
  ({ name := p.name, code := code.toList.toArray, frameSize := p.frameSize }, fills.toList.toArray)

/-- Emission adds exactly a block's size to the code. -/
def EmitBlockSize : Prop :=
  ∀ (f : String) (b : List PStmt) (acc : Rev LInstr × Rev Fill),
    (emitBlock f b acc).1.size = acc.1.size + blockSize b

end
end LeanVM.Compiler
