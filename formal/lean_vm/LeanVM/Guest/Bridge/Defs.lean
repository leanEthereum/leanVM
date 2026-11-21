/-
  LeanVM.Guest.Bridge.Defs

  The hint bridge's data: which ISA hint compiles which core hint atom, and the check that a function's flow hints are its body's leading atoms, run before its first jump.
-/

module

public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.Code
public import LeanVM.Guest.B2C.Types
public import Statement.Prover.Execute

/-!
# The hint bridge: definitions

The executor runs the compiler's hints (`Prover.Exec.Hint`, by pc); the core IR has hint atoms (`Core.Hint`, in its bodies). `compiles loc h h'`: the ISA hint `h'` is the compilation of the core hint `h` under the cell map `loc` (a value's index to its frame cell): the same stream or computation, its operands and destinations at the cells of the atom's values (`destOk`: a run of frame values from the hint's base, or a buffer's pointer and offset). An `allocDyn` whose size the compiler knows is compiled to a static `alloc`.

The cell map is the certificate's (`Cert.locs`) but for the values only hints touch, which the certificate places at cell `0` (`log2_ceil_in_the_exponent`'s bit buffer): `locOf locs extra` reads those from `extra`, generated per function, and `cellsFresh` checks that each such cell is no certificate cell, no header cell and no plumbing cell (`plumbCells`), so the reference memory can hold the hint's word there.

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

/-- A destination compiled under `loc`, `n` words from `pos` on: the frame values in consecutive
cells from `base + pos`, or the buffer's pointer at the cell `ptr` and its offset `pos`. -/
def destOk (loc : ℕ → ℕ) : Dest → Prover.Exec.BitsDest → ℕ → ℕ → Bool
  | .stack vs, .stack base, pos, n => vs.length == n && consecutive loc (base + pos) vs
  | .heap p off len, .heap ptr, pos, n => loc p.idx == ptr && off == pos && len == n
  | _, _, _, _ => false

/-- A start cell compiled under `loc`. -/
def startOk (loc : ℕ → ℕ) : Option V → Option ℕ → Bool
  | none, none => true
  | some c, some c' => loc c.idx == c'
  | _, _ => false

/-- **The ISA hint `h'` compiles the core hint `h`** under the cell map `loc`. -/
def compiles (loc : ℕ → ℕ) : Core.Hint → Prover.Exec.Hint → Bool
  | .witness s (.stack vs), .witnessStack s' base len =>
    s == s' && vs.length == len && consecutive loc base vs
  | .witness s (.heap p off len), .witnessHeap s' ptr lo len' =>
    s == s' && loc p.idx == ptr && off == lo && len == len'
  | .bits v start nbits d, .bitDecompose x bd n =>
    start == 0 && loc v.idx == x && nbits == n && destOk loc d bd 0 nbits
  | .bitsExp v nbits d, .bitDecomposeExp x bd n =>
    loc v.idx == x && nbits == n && decide (nbits ≤ 62) && destOk loc d bd 0 nbits
  | .digitsExp v nbits ndigits digitBits start sc d,
    .digitDecomposeExp x bd nbits' ndigits' digitBits' start' sc' =>
    loc v.idx == x && nbits == nbits' && ndigits == ndigits' && digitBits == digitBits' &&
      start == start' && decide (nbits ≤ 62) && startOk loc sc sc' && destOk loc d bd 0 ndigits
  | .windowsExp v start width count d, .windowsExp x bd pos start' width' count' =>
    loc v.idx == x && start == start' && width == width' && count == count' && destOk loc d bd pos count
  | .log2Ceil b nbits floor dst, .log2Ceil bd dst' nbits' floor' =>
    destOk loc b bd 0 nbits && loc dst.idx == dst' && nbits == nbits' && floor == floor'
  | .inverse x d, .inverse x' d' => loc x.idx == x' && loc d.idx == d'
  | .limbs x ds, .fieldLimbs x' base len => loc x.idx == x' && ds.length == len && consecutive loc base ds
  | .alloc d n, .alloc p n' => loc d.idx == p && n == n'
  | .allocDyn d n, .allocDyn p n' => loc d.idx == p && loc n.idx == n'
  | .allocDyn d _, .alloc p _ => loc d.idx == p
  | _, _ => false

/-- **The cell map**: the certificate's cells `locs`, but for the values of `extra`, the cells only
hints touch. -/
def locOf (locs : List ℕ) (extra : List (ℕ × ℕ)) (i : ℕ) : ℕ := (extra.lookup i).getD (locs.getD i 0)

/-- The cells a function's frame holds beyond its core values: its fixed cells, its call sites'
callee frames and dispatch targets, and its table jumps' targets. -/
def plumbCells (p : B2C.Plumb) : List ℕ :=
  p.stat.map (·.1) ++ p.sites.flatMap (fun s ↦ [s.q, s.tgt]) ++ p.arms.map (·.2.1)

/-- **The hint-only cells are fresh**: each value of `extra` has certificate cell `0` or `1` (none),
and its cell is past the header and neither a certificate cell nor one of `plumb`. -/
def cellsFresh (locs plumb : List ℕ) (extra : List (ℕ × ℕ)) : Bool :=
  extra.all fun p ↦ decide (locs.getD p.1 0 < 2) && decide (2 ≤ p.2) && !locs.contains p.2 &&
    !plumb.contains p.2

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
