/-
  LeanVM.Guest.Backend.Piece

  The check of one function's placement, emission and assembly against the statement's bytecode,
  which the kernel evaluates function by function on the guest (`Backend/Guest/Piece/`).
-/

module

public import LeanVM.Guest.Backend.Assemble
public import LeanVM.Guest.Backend.Place

/-!
# A function's piece

`pieceOk loops sigs l t tf o pc0 frame cf` places the traced function `tf` from the jump tables `t`,
emits it, and checks what that gives against `o` and the compiled function `cf`:

* the jump tables after it are `t.after o`: `o.len` slots, and the shared tables `o.shared` made
  before `t`'s (only the new ones are compared: placement only adds to the front, `placeFn_tables`);
* the jump table slots it fills are `o.fills`, as `(slot, instruction)` of its own code;
* its frame size and code size are `o.frame` and `o.size`;
* `cf` is it, at entry `pc0`: its name, entry, length, and its code resolved at the layout `l`
  with frame size `frame` (`main`'s frame holds the jump tables too) and cut in chunks.

`Sound/Piece.lean` proves what a success says (`pieceOk_spec`) and composes the pieces of a
program into `lowerProgram`'s result and the assembled functions.
-/

namespace LeanVM.Guest.Backend

@[expose] public section

/-- What placement and emission give of one function, as the guest's data records it. -/
structure FnOut where
  /-- The jump tables' length after it. -/
  len : Nat
  /-- The shared tables it made, the last first. -/
  shared : List (List String × Nat)
  /-- The jump table slots it fills: slot, and the index of the instruction in its code. -/
  fills : List (Nat × Nat)
  /-- Its frame size. -/
  frame : Nat
  /-- Its number of instructions. -/
  size : Nat

/-- The jump tables after a function that gives `o`. -/
def Tables.after (t : Tables) (o : FnOut) : Tables := ⟨o.len, o.shared ++ t.shared⟩

/-- A jump table slot filled with instruction `i` of the function. -/
def fillIs : Fill → Nat × Nat → Bool
  | (s, .at _ i), (s', i') => s == s' && i == i'
  | _, _ => false

/-- Two lists, element by element. -/
def allPairs {α β : Type} (r : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => r a b && allPairs r as bs
  | _, _ => false

/-- A lowered function as the layout reads it: name, number of instructions, frame size. -/
def infoOf (f : Lowered) : String × Nat × Nat := (f.name, f.code.size, f.frameSize)

/-- The layout of functions given by `infoOf`, with no table of powers (`Layout.pow` computes
them): `layout`'s, but for its table (`layout_eq_info`). -/
def layoutInfo (info : List (String × Nat × Nat)) (tablesBase : Nat) : Layout :=
  let (entry, frame, total) := info.foldl (init := (({} : SMap Nat), ({} : SMap Nat), 0))
    fun (entry, frame, pc) (n, size, fs) => (entry.insert n pc, frame.insert n fs, pc + size)
  { entry, frame, tablesBase, sentinel := nextPow2 (total + 1) - 1, gpow := #[] }

/-- `__jump_tables`, `main`'s frame from `base` (`withTables`). -/
def jtOf (base : Nat) (slots : Array KVal) : Lowered :=
  ⟨"__jump_tables", slots.zipIdx.map fun (k, j) => (⟨.set (base + j) k, []⟩ : LInstr),
    base + slots.size⟩

/-- The jump table slots a function gives `o` fills, as `lowerProgram` lists them. -/
def fillsOfOut (tf : TracedFn) (o : FnOut) : List Fill :=
  o.fills.map fun x => (x.1, KVal.at tf.core.name x.2)

/-- **A function's piece**: placed from `t` and emitted, the function gives `o`, and resolved at
the layout `l` from `pc0` with frame size `frame` it is `cf`. -/
def pieceOk (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout) (t : Tables) (tf : TracedFn)
    (o : FnOut) (pc0 frame : Nat) (cf : CompiledFunction) : Bool :=
  match placeFn loops sigs t tf with
  | .error _ => false
  | .ok (pf, t') =>
      let e := emitFn pf.fn
      t'.len == o.len && t'.shared.length == o.shared.length + t.shared.length &&
        decide (t'.shared.take o.shared.length = o.shared) && allPairs fillIs e.2.toList o.fills &&
        pf.fn.frameSize == o.frame && e.1.code.size == o.size && decide (cf.name = tf.core.name) &&
        cf.entryPc == pc0 && cf.instructionCount == o.size &&
        decide (chunked (resolvedFn l pc0 { e.1 with frameSize := frame }) = cf.chunks)

end
end LeanVM.Guest.Backend
