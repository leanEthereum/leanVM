/-
  LeanVM.Guest.B1.Gkr.Interface

  B1 of `verify_bus_gkr`: the specification's program it runs (`gkrPhase`) and the statement of
  its soundness (`verify_bus_gkr_Spec`).
-/

module

public import LeanVM.Guest.B1.Gkr.Fs

/-!
# `verify_bus_gkr`: the interface

`verify_bus_gkr(fs0, …, fs4, cursor, g_bus_mu, zeta, tabs)` (`lean_ethereum.py` at leanVM
`914612b6`, G below, G:1908-2089) runs the bus's one GKR grand product over the push, pull and
count trees (`verifyGkrGrandProducts`): it reads the shared root and the count root (asserted
nonzero), runs the root-most layer on its own (binary at an odd depth, else radix four, with
`gkr_children`, `gkr_product_check`), then the radix-four layers of `__loop6` (`gkrLayers`),
writes the final point to `zeta` (`zeta[g^k]`, `k < depth`) and returns the carried capacity,
the cursor past the words it read and a heap buffer of the three trees' values at the point.

Every grind of the walk is of `0` bits at the deployed parameters (`grindingBits` of `2`, `3`, `4`
and `5`), so `fs_grind_squeeze` is a plain permutation there and `tabs` goes unread. At depth `0`
the guest still runs a radix-four root layer where the specification runs none; `verify_sub`
only calls it at `depth = μ ≥ 16`, so the statement asks `g_bus_mu ≠ 1`.
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

/-- **`verify_bus_gkr`'s outcome** on its arguments `[fs0, …, fs4, cursor, g_bus_mu, zeta, tabs]`:
`g_bus_mu = g^depth` with `depth < 33`; from the carried capacity, the words `xs` at the cursor
run `gkrPhase depth` to `(count, point, values)`; the point, of `depth` coordinates, is at
`zeta`; and the function returns the new capacity, the cursor past `xs` and a pointer to the
three values. -/
def GkrOut (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, gmu, zeta, _tabs], rets =>
      ∃ (depth : ℕ) (xs : List E) (r : E × List E × List E) (cap' : List E) (leaves : E),
        gmu = gen ^ depth ∧ depth < 33 ∧ TbReadsAt rd cur xs ∧
        RunsTo (gkrPhase depth) ⟨[f0, f1, f2, f3, f4], []⟩ xs r ⟨cap', []⟩ ∧
        r.2.1.length = depth ∧ r.2.2.length = 3 ∧ TbReadsAt rd zeta r.2.1 ∧
        TbReadsAt rd leaves r.2.2 ∧ rets = cap' ++ [cur * gen ^ xs.length, leaves]
  | _, _ => False

/-- **`verify_bus_gkr` is sound**: at a depth other than `0`, its relation implies `GkrOut`.
Proved for every memory of at most `2^32` words (`verify_bus_gkr_holds`). -/
def verify_bus_gkr_Spec (rd : Reader) : Prop :=
  ∀ args rets, args.getD 6 0 ≠ 1 →
    coreProgram.Rel rd "verify_bus_gkr" args rets → GkrOut rd args rets

end
end LeanVM.Guest.B1.Tables
