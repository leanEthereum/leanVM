/-
  LeanVM.Guest.B1.Tables.TCtx

  What `verify_tables` hands `check_opening_terminal`: where each column claim's point lies.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# `TCtx`: the claims' points

`verify_tables` pools `112` column claims (`N_CLAIMS`) in the specification's order: the bus's
five framework claims (`memory0..2`, the memory's and the bytecode's final counters), each
table's columns in table order, then the public input's three (`tablesSeg`). The terminal reads
their values from `claim_pool`, and rebuilds their points from three buffers and a challenge
(`CLAIM_POINT_BUF`):

* the bus's claims lie on a prefix of the GKR point, at `zeta` (`g_bus_mu = g^|point|`);
* the tables' claims lie on a prefix of the table sumcheck's point, at `chi` (`g_zc_n`), which
  is no longer than the GKR point;
* the public input's claims lie at `(rm, 0, …, 0)`;

each of the first `109` with `g^|point|` in `claim_cplen_g` (the public input's slots are left
unwritten: the terminal takes their length from `g_log_mem`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The claims' global columns, in `tablesSeg`'s order: the bus's, each table's columns, the
public input's. -/
def claimColumns : List ℕ :=
  [memory0, memory1, memory2, memoryFinalCounters, bytecodeFinalCounters] ++
    tables.flatMap (fun t ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·)) ++
    [memory0, memory1, memory2]

/-- The claims pooled before the public input's: `N_CLAIMS - 3`. -/
abbrev nPooled : ℕ := nClaims - 3

/-- **`TCtx`** over `[zeta, chi, rm, g_bus_mu, g_zc_n, claim_cplen_g]`: the claims are
`claimColumns`'s, the bus's on a prefix of the bus point at `zeta`, the tables' on a prefix of
`chis` at `chi`, the public input's at `(rm, 0, …, 0)`, and the first `109` have `g^|point|` in
`claim_cplen_g`. -/
def TCtx (rd : Reader) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) :
    List E → Prop
  | [zeta, chi, rm, gmu, gzcn, cplen] =>
      ∃ chis : List E, ReadsAt rd zeta bus.point ∧ gmu = gen ^ bus.point.length ∧
        ReadsAt rd chi chis ∧ gzcn = gen ^ chis.length ∧ chis.length ≤ bus.point.length ∧
        claims.length = nClaims ∧ claims.map (·.column) = claimColumns ∧
        ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
          (j < nPooled → LoadHolds rd cplen j (gen ^ p.length)) ∧
          (j < 5 → p = bus.point.take p.length) ∧
          (5 ≤ j → j < nPooled → p = chis.take p.length) ∧
          (nPooled ≤ j →
            p = rm :: List.replicate ((layout.placements.getD memory0 default).vars - 1) 0)
  | _ => False

/-- `claimColumns` has one column per claim. -/
theorem claimColumns_length : claimColumns.length = nClaims := by decide

end
end LeanVM.Guest.B1.VerifySub
