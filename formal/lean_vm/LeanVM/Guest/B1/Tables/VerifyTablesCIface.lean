/-
  LeanVM.Guest.B1.Tables.VerifyTablesCIface

  The pieces of `verify_tables`' completeness proved elsewhere, as statements.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSort
public import LeanVM.Guest.B1.Tables.VerifyTablesSel
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

/-- **A push or count block's selector completes** (g5c; G:1572-1594): selector `i < 65` (block
`b = selBlk i`, first statement `selStmt i`, first value `v = selVal i`, values `v ..< v + 27`) of
log-height `k ≤ μ = |point|`, at an offset `off < 2^μ` aligned to `2^k`, on a memory defined below
`2^κ` holding `block_kappa`, `block_off_g`, `g_squares`, the bus point at `zeta`, and the block's
three buffers at the hinted pointers `p12` (`offset_bits`: the offset's 34 bits), `p15`
(`eq_chain`) and `p16` (`goff_chain`), each chain's `μ - k + 1` prefix products. It returns the
selector `eqAbove` at `v + 23` and keeps the size and the pointers. -/
def VtSelComplete : Prop :=
  ∀ (i : ℕ), i < 65 → ∀ (κ : ℕ), 6 ≤ κ → ∀ (rd : Reader), LowDef κ rd →
    ∀ (σ : Val) (zeta bk sq offP p12 p15 p16 : E) (point : List E) (k off : ℕ),
      σ (.n 5) = zeta → σ (.n 6) = gen ^ point.length → σ (.n 9) = bk → σ (.n 10) = sq →
      σ (.n 128) = offP → k ≤ point.length → point.length < 33 → off < 2 ^ point.length →
      2 ^ k ∣ off → LoadHolds rd bk (selBlk.getD i 0) (gen ^ k) →
      LoadHolds rd offP (selBlk.getD i 0) (gen ^ off) → ReadsAt rd zeta point →
      (∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) →
      ReadsAt rd p12 ((List.range 34).map fun j => bitE (off.testBit j)) →
      ReadsAt rd p15 ((List.range (point.length - k + 1)).map fun t =>
        ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) + point.getD (k + j) 0)) →
      ReadsAt rd p16 ((List.range (point.length - k + 1)).map fun t =>
        ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) * (gen ^ 2 ^ (k + j) + 1))) →
      Completes (coreProgram.Rel rd) rd (selVal.getD i 0) (selVal.getD i 0 + 27)
        ((vtPre.drop (selStmt.getD i 0)).take 28) σ (fun σ' =>
          σ' (.n (selVal.getD i 0 + 23)) = ({ vars := k, index := off } : Placement).eqAbove point ∧
            σ' (.n (selVal.getD i 0)) = gen ^ k ∧ σ' (.n (selVal.getD i 0 + 12)) = p12 ∧
            σ' (.n (selVal.getD i 0 + 15)) = p15 ∧ σ' (.n (selVal.getD i 0 + 16)) = p16)

end
end LeanVM.Guest.B1.VerifySub
