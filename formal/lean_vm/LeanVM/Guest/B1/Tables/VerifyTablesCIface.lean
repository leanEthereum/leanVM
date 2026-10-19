/-
  LeanVM.Guest.B1.Tables.VerifyTablesCIface

  The pieces of `verify_tables`' completeness proved elsewhere, as statements.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSort
public import LeanVM.Guest.B1.VerifySub.CData

/-!
# `verify_tables`' completeness: pieces

`VtSortComplete` (g5b): the certified block order's segment (`vtPre` from 213, 1225 statements,
values `129 ..< 1732`) completes when `sort_order` holds `stackOrder`'s order of each of the push
and count sides, `block_side_tab` the sides, `block_kappa` the log-heights `ks`, `g_squares` the
squares, and `block_off_g` the sides' `stackOffsets` offsets, on a memory defined below `2^κ`,
`κ ≥ 7` (the range checks against `102`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- **The certified block order completes** on the honest order and offsets. -/
def VtSortComplete : Prop :=
  ∀ (κ : ℕ), 7 ≤ κ → ∀ (rd : Reader), LowDef κ rd → ∀ (ks : ℕ → ℕ), (∀ b < 102, ks b < 34) →
    ∀ (σ : Val) (so side bk sq off : E), σ (.n 24) = so → σ (.n 25) = side → σ (.n 9) = bk →
      σ (.n 10) = sq → σ (.n 128) = off →
      (∀ r < 37, LoadHolds rd so r (gen ^ (stackOrder ((List.range 37).map ks)).getD r 0)) →
      (∀ r < 28, LoadHolds rd so (74 + r)
        (gen ^ (74 + (stackOrder ((List.range 28).map fun i => ks (74 + i))).getD r 0))) →
      (∀ b < 102, LoadHolds rd side b (word (vtBlockSide b) 0 0)) →
      (∀ b < 102, LoadHolds rd bk b (gen ^ ks b)) →
      (∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) →
      (∀ i < 37, LoadHolds rd off i (gen ^ (stackOffsets ((List.range 37).map ks)).1.getD i 0)) →
      (∀ i < 28, LoadHolds rd off (74 + i)
        (gen ^ (stackOffsets ((List.range 28).map fun i => ks (74 + i))).1.getD i 0)) →
      Completes (coreProgram.Rel rd) rd 129 1732 ((vtPre.drop 213).take 1225) σ (fun _ => True)

end
end LeanVM.Guest.B1.VerifySub
