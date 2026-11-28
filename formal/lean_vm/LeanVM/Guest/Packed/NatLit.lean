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
the digits (most significant first, `0-9`, `a-f`, `A-F`) in leaves of 15, each a machine word,
joined by shifts in a balanced tree, in time linear-logarithmic in the length, and elaborates to the
raw literal (`mkRawNatLit`), which the kernel holds as one number. Lake compiles this module to a
native library (`precompileModules` in `lakefile.toml`) that every module importing it loads: the
interpreter would pay a call for each step of the loops. Nothing here is trusted: the literal is the
term the kernel checks. `formal/lean_vm/scripts/packed.py` writes such literals.
-/

namespace LeanVM.Guest.Packed.NatLit

open Lean Elab Term

public meta section

/-- `nat_hex% "…"`: the natural number the hexadecimal digits write. -/
syntax:max (name := natHex) "nat_hex% " str : term

/-- The value of the hexadecimal digit whose ASCII code is `c` (`c ||| 32` lowers a letter's case),
or `16` if it is none. -/
def hexDigit (c : UInt8) : UInt64 :=
  if 48 ≤ c && c ≤ 57 then (c - 48).toUInt64
  else if 97 ≤ c ||| 32 && c ||| 32 ≤ 102 then ((c ||| 32) - 87).toUInt64
  else 16

/-- The number the digits at bytes `[i, j)` of `b` write after those of `acc`, in a machine word
(at most 16 digits). -/
def ofHexWord (b : ByteArray) (i j : Nat) (acc : UInt64) : Option UInt64 :=
  if i < j then
    let d := hexDigit b[i]!
    if d < 16 then ofHexWord b (i + 1) j (acc <<< 4 ||| d) else none
  else some acc
termination_by j - i

/-- The number the digits at bytes `[lo, hi)` of `b` write, most significant first: leaves of 15
digits counted from `hi`, small `Nat`s, joined by shifts in a balanced tree. -/
def ofHexRange (b : ByteArray) (lo hi : Nat) : Option Nat :=
  if hi ≤ lo + 15 then (·.toNat) <$> ofHexWord b lo hi 0
  else
    let mid := hi - 15 * ((hi - lo + 14) / 30)
    return (← ofHexRange b lo mid) <<< (4 * (hi - mid)) ||| (← ofHexRange b mid hi)
termination_by hi - lo

/-- The number the hexadecimal string `s` writes, or `none` if it is empty or has a byte that is no
digit (`_`, a non-ASCII character). -/
def ofHex (s : String) : Option Nat :=
  if s.isEmpty then none else ofHexRange s.toUTF8 0 s.utf8ByteSize

@[term_elab natHex] def elabNatHex : TermElab := fun stx _ ↦ do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  let some n := ofHex s | throwErrorAt stx[1] "nat_hex%: not a string of hexadecimal digits"
  return mkRawNatLit n

end

end LeanVM.Guest.Packed.NatLit
