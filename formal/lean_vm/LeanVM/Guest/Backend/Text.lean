/-
  LeanVM.Guest.Backend.Text

  An assembled program in the line format of `crates/isa/src/text.rs`, which the Rust prover loads.
-/

module

public import LeanVM.Guest.Backend.Ir

/-!
# The line format

`render` writes an `Assembled` as `CompiledProgram::__to_text` writes a Rust `isa::CompiledProgram`:
its padded size, `main`'s frame, a line a function, a line an instruction before the padding, a
line a hint in pc order. `lake exe guest-backend export` and `lake exe guest-artifact` write it.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Semantics

@[expose] public section

/-- An instruction's line. -/
def showOp : OffsetInstruction → String
  | .xor a b c => s!"X {a} {b} {c}"
  | .mul a b c => s!"M {a} {b} {c}"
  | .set o k0 k1 => s!"S {o} {k0} {k1}"
  | .deref o1 o2 o3 mode =>
      let m := match mode with
        | .cell => 0
        | .pc => 1
        | .fp => 2
      s!"D {o1} {o2} {o3} {m}"
  | .jump oc od of => s!"J {oc} {od} {of}"
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
      s!"K {m0} {m1} {m2} {m3} {tail} {b8} {cap} {out} {inOdd.toNat} {outOdd.toNat} {outCells.cellCount}"

def showBits : BitsDest → String
  | .stack b => s!"stack {b}"
  | .heap p => s!"heap {p}"

/-- A hint's line. -/
def showHint (pc : Nat) : RHint → String
  | .frameAddress offset => s!"H {pc} frame {offset}"
  | .allocFrames ptr size bound inv tail => s!"H {pc} frames {ptr} {size} {bound} {inv} {tail}"
  | .alloc ptr size => s!"H {pc} alloc {ptr} {size}"
  | .allocDyn ptr size => s!"H {pc} allocdyn {ptr} {size}"
  | .witnessStack s base len => s!"H {pc} wstack {s} {base} {len}"
  | .witnessHeap s ptr lo len => s!"H {pc} wheap {s} {ptr} {lo} {len}"
  | .log2Ceil bits dst nbits floor => s!"H {pc} log2 {showBits bits} {dst} {nbits} {floor}"
  | .bitDecompose v bits nbits => s!"H {pc} bits {v} {showBits bits} {nbits}"
  | .bitDecomposeExp v bits nbits => s!"H {pc} bitsexp {v} {showBits bits} {nbits}"
  | .digitDecomposeExp v dst nbits ndigits digitBits start sc =>
      let sc := match sc with
        | some c => s!"{c}"
        | none => "-"
      s!"H {pc} digits {v} {showBits dst} {nbits} {ndigits} {digitBits} {start} {sc}"
  | .windowsExp v dest skip start width count =>
      s!"H {pc} windows {v} {showBits dest} {skip} {start} {width} {count}"
  | .fieldLimbs v base len => s!"H {pc} limbs {v} {base} {len}"
  | .inverse v dst => s!"H {pc} inverse {v} {dst}"

/-- A program in the line format of `crates/isa/src/text.rs` (`CompiledProgram::__to_text`). -/
def render (c : Assembled) : String :=
  let head := #[s!"size {c.size}", s!"main_frame {c.mainFrame}"]
  let fns := c.fns.map fun (name, entry, len) => s!"F {name} {entry} {len}"
  let hints := c.hints.flatMap fun (pc, hs) => (hs.map (showHint pc)).toArray
  "\n".intercalate (head ++ fns ++ c.code.map showOp ++ hints).toList ++ "\n"

end

end LeanVM.Guest.Backend
