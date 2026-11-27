/-
  LeanVM.Guest.Packed.NatLit

  `nat_hex% "…"`: a natural number literal read from its hexadecimal digits by compiled code.
-/

module

public meta import Lean.Elab.Term

/-!
# Hexadecimal literals

The elaborator reads a numeral in time quadratic in its length, too slow for the packed vectors
of the guest's certificates (`LeanVM/Guest/Packed/`), numbers of megabytes. `nat_hex% "1f…"` reads
the digits (most significant first, `0-9`, `a-f`, `A-F`) by splitting them in halves joined by a
shift, in time linear-logarithmic in the length, the leaves read by compiled code (the interpreter
runs this module's own code, slower per digit), and elaborates to the raw literal
(`mkRawNatLit`), which the kernel holds as one number. Nothing here is trusted: the literal is the
term the kernel checks. `formal/lean_vm/scripts/packed.py` writes such literals.
-/

namespace LeanVM.Guest.Packed.NatLit

open Lean Elab Term

public meta section

/-- `nat_hex% "…"`: the natural number the hexadecimal digits write. -/
syntax:max (name := natHex) "nat_hex% " str : term

/-- The number the digits at bytes `[lo, hi)` of `s` write, most significant first: each leaf of at
most 32 digits read by the compiled decoder of Lean's `0x` numerals. -/
def ofHexRange (s : String) (lo hi : Nat) : Option Nat :=
  if hi ≤ lo + 32 then
    Syntax.decodeNatLitVal? ("0x" ++ String.Pos.Raw.extract s ⟨lo⟩ ⟨hi⟩)
  else
    let mid := (lo + hi) / 2
    return (← ofHexRange s lo mid) <<< (4 * (hi - mid)) ||| (← ofHexRange s mid hi)
termination_by hi - lo

/-- The number the hexadecimal string `s` writes: ASCII without separators, so that byte positions
are digits. (`splitOn` is compiled; `String.contains` is inlined here, so interpreted.) -/
def ofHex (s : String) : Option Nat :=
  if s.isEmpty || (s.splitOn "_").length != 1 || s.length != s.utf8ByteSize then none
  else ofHexRange s 0 s.utf8ByteSize

@[term_elab natHex] def elabNatHex : TermElab := fun stx _ ↦ do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  let some n := ofHex s | throwErrorAt stx[1] "nat_hex%: not a string of hexadecimal digits"
  return mkRawNatLit n

end

end LeanVM.Guest.Packed.NatLit
