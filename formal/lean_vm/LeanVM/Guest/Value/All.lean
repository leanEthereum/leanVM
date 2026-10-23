/-
  LeanVM.Guest.Value.All

  The value-level lemmas the B1 proofs of the aggregation guest rest on.
-/

module

public import LeanVM.Guest.Value.Tower
public import LeanVM.Guest.Value.Cells
public import LeanVM.Guest.Value.Hash
public import LeanVM.Guest.Value.FiatShamir
public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.Value.Tables
public import LeanVM.Guest.Value.Pigeonhole

/-!
# The guest's values

Lemmas about Lean values (field words, cells, bytes, digests, integers, lists), independent of
how the guest's code is represented, on which the per-function refinement lemmas (B1,
`Guest/DESIGN.md`) rest:

| module | what |
|---|---|
| `Tower` | `y`, `y⁻¹`, `pack64x2`, the limb splits pinned by `assert_in_k`, integers as bit patterns |
| `Cells` | cells as bytes, the metadata cell, the IV cells, one `BLAKE2S` as a compression |
| `Hash` | chained BLAKE2s over cells equals `blake2sBytes` |
| `FiatShamir` | `fs_compress`, `obs`, `squeeze_state`, `squeeze`, `challenge_from_state`, `grind_check` |
| `Bits` | bit decompositions, g-power products, the range check, `log2Ceil` by two bounds |
| `Tables` | `exponent_tables` |
| `Pigeonhole` | write-once bijections, sorted orders, coverage as `List.Forall₂` |
-/
