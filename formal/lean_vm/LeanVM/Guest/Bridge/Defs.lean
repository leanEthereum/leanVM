/-
  LeanVM.Guest.Bridge.Defs

  The hint bridge's data: which ISA hint compiles which core hint atom, and the check that a function's flow hints are its body's leading atoms, run before its first jump.
-/

module

public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.Code
public import Statement.Prover.Execute

/-!
# The hint bridge: definitions

The executor runs the compiler's hints (`Prover.Exec.Hint`, by pc); the core IR has hint atoms (`Core.Hint`, in its bodies). `compiles loc h h'`: the ISA hint `h'` is the compilation of the core hint `h` under the cell map `loc` (a value's index to its frame cell, the certificate's `Cert.locs`): the same stream or computation, its operands and destinations at the cells of the atom's values.

A **flow** hint is a witness or computed one (it pops or writes words the instructions read); allocations and plumbing (frame addresses, callee frames, dispatch frames, loop frames, advised sizes) are not, and are bridged apart (allocations by the bump pointer, plumbing by `B2C`'s fixed cells).

`prefixOk loc body code adv`: the **prefix class**. The body's flow hints are all among its leading atoms (`atomPrefix`), the rest of the body has no witness hint (`Stmt.noWitList`), and the function's ISA flow hints (`isaFlow`, from the advice by function: entry, length, hints by pc) sit at offsets up to its first jump and compile those leading flow hints one for one, in order (`pairsOk`). The frame's run passes those offsets in order before it can branch, call or return, so its flow hints run in body order.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The values `vs` sit in consecutive cells from `b` under `loc`. -/
def consecutive (loc : ℕ → ℕ) : ℕ → List V → Bool
  | _, [] => true
  | b, v :: vs => loc v.idx == b && consecutive loc (b + 1) vs

/-- **The ISA hint `h'` compiles the core hint `h`** under the cell map `loc`. -/
def compiles (loc : ℕ → ℕ) : Core.Hint → Prover.Exec.Hint → Bool
  | .witness s (.stack vs), .witnessStack s' base len =>
    s == s' && vs.length == len && consecutive loc base vs
  | .witness s (.heap p off len), .witnessHeap s' ptr lo len' =>
    s == s' && loc p.idx == ptr && off == lo && len == len'
  | .inverse x d, .inverse x' d' => loc x.idx == x' && loc d.idx == d'
  | .limbs x ds, .fieldLimbs x' base len => loc x.idx == x' && ds.length == len && consecutive loc base ds
  | .alloc d n, .alloc p n' => loc d.idx == p && n == n'
  | .allocDyn d n, .allocDyn p n' => loc d.idx == p && loc n.idx == n'
  | _, _ => false

/-- A core hint the frame's flow carries: a witness or computed one. -/
def coreFlow : Core.Hint → Bool
  | .alloc .. | .allocDyn .. => false
  | _ => true

/-- An ISA hint the frame's flow carries: a witness or computed one. -/
def isaFlowHint : Prover.Exec.Hint → Bool
  | .witnessStack .. | .witnessHeap .. | .log2Ceil .. | .bitDecompose .. | .bitDecomposeExp ..
  | .windowsExp .. | .digitDecomposeExp .. | .fieldLimbs .. | .inverse .. => true
  | _ => false

/-- A block's leading atoms, and the statements after them. -/
def atomPrefix : List Stmt → List Atom × List Stmt
  | .atom a :: ss => ((atomPrefix ss).1.cons a, (atomPrefix ss).2)
  | ss => ([], ss)

/-- The flow hints among atoms, in order. -/
def flowOf : List Atom → List Core.Hint
  | [] => []
  | .hint h :: as => if coreFlow h then h :: flowOf as else flowOf as
  | _ :: as => flowOf as

/-- The flow hints of the hints at one pc, each with its offset. -/
def flowAt (entry : ℕ) (p : ℕ × List Prover.Exec.Hint) : List (ℕ × Prover.Exec.Hint) :=
  (p.2.filter isaFlowHint).map fun h ↦ (p.1 - entry, h)

/-- **A function's ISA flow hints**, each with its offset, in the advice's order (by pc, then in
the list at a pc): from the advice by function (entry, length, hints by pc). -/
def isaFlow (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : List (ℕ × Prover.Exec.Hint) :=
  d.2.2.flatMap (flowAt d.1)

/-- The offset of the first jump of the code, or its length. -/
def firstJump (code : List OffsetInstruction) : ℕ := code.findIdx OffsetInstruction.isJump

/-- The core hints and the ISA hints pair one for one, in order, each compiling its own. -/
def pairsOk (loc : ℕ → ℕ) : List Core.Hint → List Prover.Exec.Hint → Bool
  | [], [] => true
  | h :: hs, h' :: hs' => compiles loc h h' && pairsOk loc hs hs'
  | _, _ => false

/-- The advice's pcs strictly increase. -/
def pcsUp : List (ℕ × List Prover.Exec.Hint) → Bool
  | a :: b :: l => a.1 < b.1 && pcsUp (b :: l)
  | _ => true

/-- **The prefix class**: the body's flow hints are its leading atoms', its rest has no witness
hint, and the function's ISA flow hints, at offsets up to its first jump and pcs from its entry,
compile them one for one, in order. -/
def prefixOk (loc : ℕ → ℕ) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  Stmt.noWitList (atomPrefix body).2 && pcsUp d.2.2 && d.2.2.all (fun p ↦ d.1 ≤ p.1) &&
    (isaFlow d).all (fun p ↦ p.1 ≤ firstJump code) &&
    pairsOk loc (flowOf (atomPrefix body).1) ((isaFlow d).map (·.2))

end

end LeanVM.Guest.Bridge
