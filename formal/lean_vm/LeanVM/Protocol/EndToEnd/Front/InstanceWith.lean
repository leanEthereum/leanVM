/-
  LeanVM.Protocol.EndToEnd.Front.InstanceWith

  The leanISA instance with any Keccak region: the deployed one at `QKECCAK`, the
  reduction-blind one with none. Everything the bus, the table sumcheck and the public input read
  of it is the deployed instance's.
-/

module

public import LeanVM.Protocol.LeanIsa

/-!
# The leanISA instance with any Keccak region

`leanIsaWith prog s kr` is `leanIsaInstance prog s` with the Keccak region `kr`: the deployed
instance at `kr = some (keccakRegion prog s)` (`leanIsaWith_some`, by `rfl`), and the
reduction-blind instance at `kr = none`, whose relation has no Keccak predicate
(`M3Instance.aux` holds of every stack, `aux_none`).

The region is read only by the Keccak predicate: the bus, the table sumcheck's claims and the
public input read the same fields at every `kr`. The statements about them that the front phases
prove at the deployed instance are stated at every `kr` (`TableFidLeanIsa`, `PubPhase`,
`BusTable`); here, the bus phase's side conditions (`leanIsaWith_conditions`), whose leaf counts
are the same at every region (`leafCount_leanIsaWith`).
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.LeanIsa

@[expose] public section

/-- **The leanISA instance with the Keccak region `fl`**: `leanIsaInstance prog s` but for its
region. -/
abbrev leanIsaWith (prog : LeanIsaProgram) (s : Sizes)
    (fl : Option (KeccakRegion (shape prog s))) : M3Instance where
  toShape := shape prog s
  Stmt := PublicInput
  constraints := constraints
  flushes := flushes
  d := 2
  constraints_degree := constraints_degree
  flushes_degree := flushes_degree
  counts := counts
  rows := rows prog s
  rows_le := rows_le prog s
  padRow := padRow
  boundary := boundary prog s
  μ := leanIsaμ prog s
  layout := layout prog s
  derived := derived prog s
  nLines := 2
  publicLines := publicLines prog s
  keccak := fl

variable (prog : LeanIsaProgram) (s : Sizes)

/-- A side's leaf count, from its blocks' log-heights. -/
theorem leafCount_eq_κ (I : M3Instance) (k : Fin 3) :
    Bus.leafCount I k = (((Bus.sources I k).map Bus.Source.κ).map (2 ^ ·)).sum := by
  rw [Bus.leafCount, List.map_map]
  rfl

/-- **The leaf counts do not depend on the region.** -/
theorem leafCount_leanIsaWith (fl fl' : Option (KeccakRegion (shape prog s))) (k : Fin 3) :
    Bus.leafCount (leanIsaWith prog s fl) k = Bus.leafCount (leanIsaWith prog s fl') k := by
  rw [leafCount_eq_κ, leafCount_eq_κ]
  fin_cases k
  · change (((Bus.sideSources _ .push).map Bus.Source.κ).map _).sum =
      (((Bus.sideSources _ .push).map Bus.Source.κ).map _).sum
    rw [Bus.sideSources_map_κ, Bus.sideSources_map_κ]
  · change (((Bus.sideSources _ .pull).map Bus.Source.κ).map _).sum =
      (((Bus.sideSources _ .pull).map Bus.Source.κ).map _).sum
    rw [Bus.sideSources_map_κ, Bus.sideSources_map_κ]
  · change (((Bus.countSources _).map Bus.Source.κ).map _).sum =
      (((Bus.countSources _).map Bus.Source.κ).map _).sum
    rw [Bus.countSources_map_κ, Bus.countSources_map_κ]

/-- **The bus phase's side conditions hold at every region**: they are the deployed instance's
(`leanIsa_conditions`). -/
theorem leanIsaWith_conditions (fl : Option (KeccakRegion (shape prog s))) :
    Bus.Conditions (leanIsaWith prog s fl) :=
  have h := leanIsa_conditions prog s
  { one_le_d := h.one_le_d
    constrained := h.constrained
    pull_fits := by
      rw [leafCount_leanIsaWith prog s fl (some (keccakRegion prog s))]
      exact h.pull_fits
    count_fits := by
      rw [leafCount_leanIsaWith prog s fl (some (keccakRegion prog s))]
      exact h.count_fits
    separator := h.separator }

end
end LeanVM.Protocol
