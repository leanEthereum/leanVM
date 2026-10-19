/-
  LeanVM.Guest.B1.Tables.VerifyTablesCIface

  The pieces of `verify_tables`' completeness proved elsewhere, as statements.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSort
public import LeanVM.Guest.B1.Tables.VerifyTablesSel
public import LeanVM.Guest.B1.Tables.VerifyTablesReads
public import LeanVM.Guest.B1.FiatShamir
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

/-! ## The honest buffers -/

/-- The rounds' states. -/
def zcRoundsW (cvr : ℕ → Digest) (cur : E) (cl : ℕ → E) (n : ℕ) : List E :=
  (List.range (n + 1)).flatMap fun r =>
    [(digestScalars (cvr r)).1, (digestScalars (cvr r)).2, cur * gen ^ (5 + 3 * r), cl r]

/-- The challenges' running products. -/
def zcCprodW (ch : ℕ → E) (n : ℕ) : List E := (List.range (n + 1)).map fun r => ∏ j ∈ Finset.range r, ch j

/-- The equality prefix's running products. -/
def zcPeqW (point chis : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).map fun k => ∏ j ∈ Finset.range k, (1 + point.getD j 0 + chis.getD j 0)

/-- **The table sumcheck's setup, rounds and equality prefix complete** (g5b; G:1690-1742):
statements `4273 ..< 4374` (values `4554 ..< 4660`). `g^n` is hinted with `n` the largest of the
tables' log-heights `τs` (read from `dims`), `n ≤ μ = |point|`; `ξ` is squeezed from the state
`cvB` after the bus's reads; the bus target is `ξ²·T₀ + ξ³·T₁ + ξ⁴·T₂` on the three totals; the
rounds run from the cursor five words on (`cl`, `cvr`, `wsr`, `ch`, the round `r` reading
`wsr r`), the challenges stored reversed at `chi`, on the honest buffers `pR` (round states),
`pC` (challenges' products) and `pP` (equality prefix). It returns `g^n`, `ξ` and its powers, the
three pointers and the state, cursor and claim after the last round. -/
def VtZcComplete : Prop :=
  ∀ (κ : ℕ), 6 ≤ κ → ∀ (rd : Reader), LowDef κ rd →
    ∀ (σ : Val) (dims chiP zeta cur pR pC pP T0 T1 T2 : E) (point chis : List E) (τs : ℕ → ℕ) (n : ℕ)
      (cvB : Digest) (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E),
      σ (.n 7) = dims → σ (.n 6) = gen ^ point.length → σ (.n 2) = cur → σ (.n 15) = chiP →
      σ (.n 5) = zeta → (σ (.n 3422), σ (.n 3423)) = digestScalars cvB → σ (.n 3326) = T0 →
      σ (.n 3705) = T1 → σ (.n 4553) = T2 →
      (∀ t < 6, LoadHolds rd dims (t + 1) (gen ^ τs t)) → (∀ t < 6, τs t ≤ n) → (∃ t < 6, τs t = n) →
      n ≤ point.length → point.length < 33 → ReadsAt rd zeta point → ReadsAt rd chiP chis →
      chis = ((List.range n).map ch).reverse →
      cl 0 = challengeOf (sqCv cvB) ^ 2 * T0 + challengeOf (sqCv cvB) ^ 3 * T1 +
        challengeOf (sqCv cvB) ^ 4 * T2 →
      cvr 0 = sqCv cvB →
      (∀ r < n, RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) →
      ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr) →
      ReadsAt rd pR (zcRoundsW cvr cur cl n) → ReadsAt rd pC (zcCprodW ch n) →
      ReadsAt rd pP (zcPeqW point chis n) →
      Completes (coreProgram.Rel rd) rd 4554 4660 ((vtPre.drop 4273).take 101) σ (fun σ' =>
        σ' (.n 4554) = gen ^ n ∧ σ' (.n 4621) = challengeOf (sqCv cvB) ∧
          (∀ k < 5, σ' (.n (4622 + k)) = challengeOf (sqCv cvB) ^ k) ∧
          σ' (.n 4636) = pR ∧ σ' (.n 4639) = pC ∧ σ' (.n 4655) = pP ∧
          (σ' (.n 4649), σ' (.n 4650)) = digestScalars (cvr n) ∧ σ' (.n 4651) = cur * gen ^ (5 + 3 * n) ∧
          σ' (.n 4652) = cl n)

/-- **A column evaluation completes** (g5c; G:1752-1758): evaluation `j < 104` (`evT j`, first
statement `evStmt j`, values `v ..< v + 16` for `v = evVal j`): from the state `cv` in the cells
before it, its word `w` read at the cursor's offset `j`, absorbed, and stored in `claim_pool` and,
its table's `g^τ`, in `claim_cplen_g` at slot `5 + j`. -/
def VtEvComplete : Prop :=
  ∀ (j : ℕ), j < 104 → ∀ (rd : Reader) (σ : Val) (cur pool cplen w g : E) (cv : Digest),
    σ (.n 4651) = cur → σ (.n 13) = pool → σ (.n 14) = cplen → σ (.n (evTau.getD j 0)) = g →
    (σ (.n (if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13)),
      σ (.n ((if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13) + 1))) = digestScalars cv →
    LoadHolds rd cur j w → LoadHolds rd pool (5 + j) w → LoadHolds rd cplen (5 + j) g →
    Completes (coreProgram.Rel rd) rd (evVal.getD j 0) (evVal.getD j 0 + 16)
      ((vtPre.drop (evStmt.getD j 0)).take 16) σ (fun σ' =>
        σ' (.n (evVal.getD j 0)) = w ∧ σ' (.n (evVal.getD j 0 + 15)) = w ∧
          (σ' (.n (evVal.getD j 0 + 13)), σ' (.n (evVal.getD j 0 + 14))) = digestScalars (obsCv cv w))

/-- The tables' constraint windows: first statements, ends, first values, ends, and each table's
`g^τ` value. -/
def airA : List ℕ := [4615, 5103, 5520, 5909, 6416, 7286]
def airB : List ℕ := [4863, 5392, 5669, 6192, 6694, 7854]
def airLo : List ℕ := [4901, 5389, 5806, 6195, 6702, 7572]
def airHi : List ℕ := [5149, 5678, 5955, 6478, 6980, 8140]
def tauV : List ℕ := [4660, 5148, 5677, 5954, 6477, 6979]

/-- **A table's constraint window completes** (g5c; G:1759-1770): window `t < 6`, the statements
`airA t ..< airB t` (values `airLo t ..< airHi t`) after table `t`'s evaluations: its
`constraint_eval` and bus forms on `fp_w`, its weight `cprod[n - τ]·peq[τ]` read at the hinted
`g^n` and the table's `g^τ`, and (for `t < 5`) the next table's `g^τ` read from `dims`. -/
def VtAirComplete : Prop :=
  ∀ (t : ℕ), t < 6 → ∀ (rd : Reader) (σ : Val) (fpw dims pC pP : E) (n τ : ℕ),
    σ (.n 11) = fpw → σ (.n 7) = dims → σ (.n 4639) = pC → σ (.n 4655) = pP → σ (.n 4554) = gen ^ n →
    σ (.n (tauV.getD t 0)) = gen ^ τ → τ ≤ n → (∀ i < 16, ∃ v, LoadHolds rd fpw i v) →
    (∃ v, LoadHolds rd pC (n - τ) v) → (∃ v, LoadHolds rd pP τ v) →
    (t < 5 → ∃ v, LoadHolds rd dims (t + 2) v) →
    Completes (coreProgram.Rel rd) rd (airLo.getD t 0) (airHi.getD t 0)
      ((vtPre.drop (airA.getD t 0)).take (airB.getD t 0 - airA.getD t 0)) σ (fun σ' =>
        t < 5 → ∀ v, LoadHolds rd dims (t + 2) v → σ' (.n (tauV.getD (t + 1) 0)) = v)

end
end LeanVM.Guest.B1.VerifySub
