/-
  LeanVM.Guest.B1.Gkr.Interface

  B1 of `verify_bus_gkr`: the specification's program it runs (`gkrPhase`) and the statement of
  its soundness (`verify_bus_gkr_Spec`).
-/

module

public import LeanVM.Guest.B1.Gkr.Fs

/-!
# `verify_bus_gkr` (TRIAGE G #43): the interface

`verify_bus_gkr(fs0, …, fs4, cursor, g_bus_mu, zeta)` (G:1763-1935) runs the bus's one GKR
grand product over push, pull and count (`verifyGkrGrandProducts`, V:1379-1414): it reads the
shared root and the count root (asserted nonzero, V:1490), runs one binary layer when the depth
is odd and then layers of two levels (`gkrLayers`), writes the final point to `zeta`
(`zeta[g^k]`, `k < depth`) and returns the carried capacity, the cursor past the words it read
and the three trees' values at the point.

At depth `0` the guest drops the two roots waiting in the sponge (G:1785-1788) where the
specification keeps them waiting; `verify_sub` only calls it at `depth = μ ≥ 16`, so the
statement asks `g_bus_mu ≠ 1`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The GKR walk and the count root's check (V:1488-1490): what `verify_bus_gkr` runs. -/
def gkrPhase (depth : ℕ) : VerifierProgram (E × List E × List E) := do
  let r ← verifyGkrGrandProducts depth
  VerifierProgram.require (r.1 ≠ 0)
  return r

/-- **`verify_bus_gkr`'s outcome** on its arguments `[fs0, …, fs4, cursor, g_bus_mu, zeta]`:
`g_bus_mu = g^depth` with `depth < 33`; from the carried capacity, the words `xs` at the cursor
run `gkrPhase depth` to `(count, point, values)`; the point, of `depth` coordinates, is at
`zeta`; and the function returns the new capacity, the cursor past `xs` and the three values. -/
def GkrOut (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, gmu, zeta], rets =>
      ∃ (depth : ℕ) (xs : List E) (r : E × List E × List E) (cap' : List E),
        gmu = gen ^ depth ∧ depth < 33 ∧ TbReadsAt rd cur xs ∧
        RunsTo (gkrPhase depth) ⟨[f0, f1, f2, f3, f4], []⟩ xs r ⟨cap', []⟩ ∧
        r.2.1.length = depth ∧ r.2.2.length = 3 ∧ TbReadsAt rd zeta r.2.1 ∧
        rets = cap' ++ [cur * gen ^ xs.length] ++ r.2.2
  | _, _ => False

/-- **`verify_bus_gkr` is sound**: at a depth other than `0`, its relation implies `GkrOut`.
Proved for every memory of at most `2^32` words (`verify_bus_gkr_holds`). -/
def verify_bus_gkr_Spec (rd : Reader) : Prop :=
  ∀ args rets, args.getD 6 0 ≠ 1 →
    coreProgram.Rel rd "verify_bus_gkr" args rets → GkrOut rd args rets

end
end LeanVM.Guest.B1.Tables
