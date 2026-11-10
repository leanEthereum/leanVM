/-
  LeanVM.Guest.B1.KeccakGkr.Interface

  B1 of the Keccak GKR reduction: the guest's records of a claim and of a round, the meanings of
  `keccak_plain_rounds`, `keccak_layer` and `verify_keccak`, and the statements that their core
  IR computes them.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Tables.Base

/-!
# The Keccak GKR reduction (TRIAGE G #53-63): the interface

`verify_keccak` (`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM `98ceacf2`, G
below, G:3131-3302) runs the specification's `verifyKeccak`, then permutes the last four slices
waiting, the full queue the next grind's nonce finds (`absorb`). Its callees:

| function | G | meaning |
| --- | --- | --- |
| `keccak_plain_rounds__L{n}_L{k0}` | 3086-3112 | `n` plain rounds of degree two (`sumcheck _ 3 (replicate n none)`), `k0` scalars waiting |
| `keccak_layer__L{first}` | 2900-3083 | `verifyKeccakLayer` on a claim record |
| `verify_keccak` | 3131-3302 | `verifyKeccak`, then the full queue permuted |

Its grinds are of `0` bits at the deployed parameters (`grindingBits` of `2`, `3` and of the
segment and lane's `keccakSegmentBits + keccakLaneBits`), plain permutations, but for the one before
a layer's `s`, of `grindingBits (productBits - 1) = 3` bits: its nonce is the stream word at the
cursor and `grind_check` reads the window table `tabs`.

The pack rounds of a layer run in two loops (`__loop37` .. `__loop40`, `PackLoop`): eight
equality-mode rounds an iteration, then one an iteration. The inline helpers (`carry_step`,
`carry_wrap`, `keccak_shifts_eq`, `fold_node`, `fold_shifts`, `keccak_form`, `slice_weight`,
`keccak_slot_lanes`, G:2745-2899, 3115-3128) have no core function of their
own: they are lemmas of `B1/KeccakGkr/`.

**Records.** A round record (`KR_*`, G:241-251) holds a sponge's capacity, a cursor, a claim
and a scale, its fields `KR_CAP = 16` words apart (`RoundRec`). A claim record (`KC_*`,
G:232-239) holds a `KeccakClaim` in the guest's factored form (`ClaimRec`): its value,
`κ = Σ μ`, a pointer to its point, its sixteen instance weights `μ`, and its position weights as
a lane table times a slice table, `firstWeights lanes` for the first claim (a word's bits, `x^z`)
and `laterWeights lanes slices` after a layer (through the transpose of θ, ρ, π,
`keccakLinearTranspose`), the slices `eqKernel` of the claim's local point's six slice
coordinates; after a layer also its weights at the positions `ι` can flip, `2^i - 1` of lane `0`
(`flipsOf`, `KC_FLIPS`).

Statements (`…_Spec`, soundness, proved as `…_holds`; `…_complete_Spec`, the converse, where it
is stated):

* `keccak_plain_rounds_Spec`, `keccak_plain_rounds_complete_Spec`;
* `keccak_layer_Spec`: from a claim record of the claim `c`, the two specializations run
  `verifyKeccakLayer (y + 3) step c` (`y` the point's length) on the carried sponge, the guest's
  `iota` being the specification's (`keccakIota`), and write the next claim's record;
* `verify_keccak_Spec`: `verifyKeccak τ (chis.take τ) outs`, then the full queue permuted, on the
  carried capacity, `τ` the `KECCAK` table's log-height (`9 ≤ τ ≤ 28`), `chis` the table sumcheck's point
  at `chi`, `outs` the table's output lane values; the committed outputs' claim's point at `z_vals`,
  the input opening's point at `z_vals·g^39` (`QKECCAK_VARS_CAP`), the slices at `slices`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The guest's constants -/

/-- `KR_CAP`: a round record's fields are `16` words apart. -/
abbrev krCap : ℕ := 16

/-- `KC_SIZE = KC_MU + KECCAK_PACK`: a claim record's words. -/
abbrev kcSize : ℕ := 22

/-- `QKECCAK_VARS_CAP`: the two opening points of `verify_keccak` are `39` words apart. -/
abbrev qkeccakVarsCap : ℕ := 39

/-! ## Round records -/

/-- The round record at `rec`, from offset `k` (record `rec·g^k`): the capacity cells `cap`, the
cursor `cur`, the claim and the scale, its fields `KR_CAP` words apart (`KR_FS = 0`,
`KR_CURSOR = 5`, `KR_CLAIM = 6`, `KR_SCALE = 7`). -/
def RoundRec (rd : Reader) (rec : E) (k : ℕ) (cap : List E) (cur claim scale : E) : Prop :=
  CapAt rd rec k krCap cap ∧ LoadHolds rd rec (k + 5 * krCap) cur ∧
    LoadHolds rd rec (k + 6 * krCap) claim ∧ LoadHolds rd rec (k + 7 * krCap) scale

/-- **One equality-mode round of degree two** (a pack round of `keccak_layer`, G:2978-2994): `g₁`,
`g₂` absorbed,
the challenge `c` squeezed; with `r` the round's coordinate, the claim becomes
`(1 + r + c)·(claim + (r + c)·g₁ + (r + c²)·g₂)` (`(1 + r + c)·polyEval message c` of
`sumcheckRoundPoly 3 claim (some r)`) and the scale is multiplied by
`1 + r + c`. The challenge, the claim, the scale and the sponge after it. -/
def eqRound (s : Fs) (g1 g2 r claim scale : E) : E × E × E × Fs :=
  let q := (s.absorbAll [g1, g2] dsObserve).squeeze
  (q.1, (1 + (r + q.1)) * (claim + (r + q.1) * g1 + (r + q.1 * q.1) * g2),
    scale * (1 + (r + q.1)), q.2)

/-! ## Plain rounds -/

/-- **Plain rounds of degree two** (`sumcheck claim 3 (replicate n none)`): per round
`c₀`, `c₂` absorbed, the challenge `c` squeezed, the claim `c₀ + c·((claim + c₂) + c·c₂)`
(`polyEval [c₀, claim + c₂, c₂] c`). The challenges, the final claim and the final
sponge. -/
def plainRun : List (E × E) → E → Fs → List E × E × Fs
  | [], v, s => ([], v, s)
  | (c0, c2) :: rest, v, s =>
    let q := ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze
    let r := plainRun rest (c0 + q.1 * ((v + c2) + q.1 * c2)) q.2
    (q.1 :: r.1, r.2.1, r.2.2)

/-- The sponge `keccak_plain_rounds` starts from: the carried capacity, and with `k0 = 1` one
scalar `w` waiting, its rate cells `p0`, `p1`. -/
def plainStart (k0 : ℕ) (cap : List E) (w : E) : Fs :=
  ⟨cap, if k0 = 1 then [(w, dsObserve)] else []⟩

/-- **`keccak_plain_rounds(fs0..fs4, p0, p1, cursor, value, point, tabs, n, k0)`** (G:3086-3112): the
`2n` stream words at the cursor are the rounds' `c₀`, `c₂`; and for every scalar `w` whose rate cells are `p0`, `p1` with `k0 = 1`
(`Keccak.scalarCells w dsObserve`, the scalar waiting), the rounds (`plainRun`) store their
challenges at `point`, and the function returns the final capacity, the cursor `2n` words on and
the final claim. -/
def MeaningPlainRounds (n k0 : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, p0, p1, cur, value, point, _tabs], rets =>
      ∃ rounds : List (E × E), rounds.length = n ∧
        ReadsAt rd cur (rounds.flatMap fun c ↦ [c.1, c.2]) ∧
        ∀ w : E, (k0 = 1 → (p0, p1) = Keccak.scalarCells w dsObserve) →
          let r := plainRun rounds value (plainStart k0 [f0, f1, f2, f3, f4] w)
          ReadsAt rd point r.1 ∧ rets = r.2.2.cap ++ [cur * gen ^ (2 * n), r.2.1]
  | _, _ => False

/-- With `k0 = 1`, the cells `p0`, `p1` (arguments `5`, `6`) are a scalar's rate cells. -/
def PlainCellsOk (k0 : ℕ) (args : List E) : Prop :=
  k0 = 1 → ∃ w : E, (args.getD 5 0, args.getD 6 0) = Keccak.scalarCells w dsObserve

/-- The two specializations: `(n, k0) = (6, 0)` (the slot, `QKECCAK_SLOT_LOG = 6`) and `(4, 1)`
(the pack, `KECCAK_PACK_LOG = 4`, after the committed outputs' word). -/
def plainName : ℕ → String
  | 1 => "keccak_plain_rounds__L4_L1"
  | _ => "keccak_plain_rounds__L6_L0"

/-- The rounds of a specialization: `4` with a scalar waiting, else `6`. -/
def plainCount (k0 : ℕ) : ℕ := if k0 = 1 then 4 else 6

/-- `keccak_plain_rounds`' two specializations compute their meanings. -/
def keccak_plain_rounds_Spec : Prop :=
  ∀ k0 < 2, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd (plainName k0) args rets → MeaningPlainRounds (plainCount k0) k0 rd args rets

/-- The converse, for completeness, the waiting cells being a scalar's. -/
def keccak_plain_rounds_complete_Spec : Prop :=
  ∀ k0 < 2, ∀ (rd : Reader) (args rets : List E), PlainCellsOk k0 args →
    MeaningPlainRounds (plainCount k0) k0 rd args rets → coreProgram.Rel rd (plainName k0) args rets

/-! ## Claim records -/

/-- The first claim's position weights: bit `z` of lane `l` weighs `lanes[l]·x^z`. -/
def firstWeights (lanes : List E) : List E :=
  (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))

/-- A later claim's position weights (factored): the transpose of θ, ρ, π applied to
the lane table times the slice table. -/
def laterWeights (lanes slices : List E) : List E :=
  keccakLinearTranspose
    ((List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * slices.getD (j % 64) 0)

/-- A later claim's weights at the positions `ι` can flip, `2^i - 1` of lane `0`, `i < 7`
(`KC_FLIPS`). -/
def flipsOf (ws : List E) : List E := (List.range 7).map fun i ↦ ws.getD (2 ^ i - 1) 0

/-- **The claim record at `rec`** (`KC_*`, G:232-239) of the claim `c` on `y`-coordinate points:
`KC_VALUE = 0` the value, `KC_KAPPA = 1` the sum of the instance weights, `KC_POINT = 2` a pointer
to the point, `KC_MU = 6..21` the sixteen instance weights, `KC_LANES = 3` a pointer to the
twenty-five lane weights; the first claim's position weights are `firstWeights`; a later claim's
`laterWeights` of its lanes and its slices, `eqKernel` of the first six coordinates of its local
point (eleven words at `KC_LOCAL = 4`), and `KC_FLIPS = 5` points to its weights at the positions
`ι` can flip (`flipsOf`). -/
def ClaimRec (rd : Reader) (first : Bool) (rec : E) (c : KeccakClaim) (y : ℕ) : Prop :=
  c.mu.length = pack ∧ c.point.length = y ∧
  LoadHolds rd rec 0 c.value ∧ LoadHolds rd rec 1 (sumE c.mu) ∧
  (∀ i < pack, LoadHolds rd rec (6 + i) (c.mu.getD i 0)) ∧
  (∃ pp, LoadHolds rd rec 2 pp ∧ ReadsAt rd pp c.point) ∧
  ∃ (lp : E) (lanes : List E), LoadHolds rd rec 3 lp ∧ lanes.length = 25 ∧ ReadsAt rd lp lanes ∧
    if first then c.weights = firstWeights lanes
    else ∃ (lc fl : E) (loc : List E), LoadHolds rd rec 4 lc ∧ loc.length = keccakLocalBits ∧
      ReadsAt rd lc loc ∧ LoadHolds rd rec 5 fl ∧ ReadsAt rd fl (flipsOf c.weights) ∧
      c.weights = laterWeights lanes (eqKernel (loc.take 6))

/-- The `ι` term of `verifyKeccakLayer logSteps step c`: per segment, the claim's
weights where the segment's round constant has a bit, scaled by the segment's equality weight. -/
def keccakIota (logSteps step : ℕ) (c : KeccakClaim) : E :=
  let segments := eqKernel (c.point.drop (logSteps - 4))
  sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (c.weights.getD z 0) else none))

/-! ## A layer -/

/-- The specialization of `keccak_layer` at `first`. -/
def layerName : ℕ → String
  | 1 => "keccak_layer__L1"
  | _ => "keccak_layer__L0"

/-- `KR_STEP`: the pack rounds' first loop runs eight rounds an iteration. -/
abbrev krStep : ℕ := 8

/-- **`keccak_layer(fs0..fs4, p0, p1, cursor, y_g, step_g, rem_g, claim, out, iota, tabs, first)`**
(G:2900-3083): on the window table `tabs` (`WinTabs`, which `s`'s grind reads), for every reading of its arguments as the claim `c` on points of
`y = 8·⌊y/8⌋ + y % 8` coordinates (`y_g = g^y`, `step_g = g^⌊y/8⌋`, `rem_g = g^(y % 8)`) whose
record is at `claim`, the step `step`'s `ι` term (`keccakIota`), and with `first = 1` the
committed outputs' word `w` waiting in the sponge (rate cells `p0`, `p1`): from the carried
capacity, the stream words `xs` at the cursor run `verifyKeccakLayer (y + 3) step c` to the claim
`c'`, whose record the function writes at `out`; it returns the capacity after the run and the
cursor past `xs`. -/
def MeaningKeccakLayer (first : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, p0, p1, cur, yg, sg, rg, claim, out, iota, tabs], rets =>
      WinTabs rd tabs → ∀ (y step : ℕ) (c : KeccakClaim) (w : E), 1 ≤ y → y < 32 → yg = gen ^ y →
        sg = gen ^ (y / krStep) → rg = gen ^ (y % krStep) → ClaimRec rd (first = 1) claim c y →
        (first = 1 → (p0, p1) = Keccak.scalarCells w dsObserve) →
        iota = keccakIota (y + 3) step c →
        ∃ (xs : List E) (c' : KeccakClaim) (cap' : List E), ReadsAt rd cur xs ∧
          RunsTo (verifyKeccakLayer (y + 3) step c) (plainStart first [f0, f1, f2, f3, f4] w) xs c'
            ⟨cap', []⟩ ∧
          ClaimRec rd false out c' y ∧ rets = cap' ++ [cur * gen ^ xs.length]
  | _, _ => False

/-- `keccak_layer`'s two specializations compute their meanings on the reader `rd` (proved on a
memory image, where `grind_check` has its meaning). -/
def keccak_layer_Spec (rd : Reader) : Prop :=
  ∀ first < 2, ∀ (args rets : List E),
    coreProgram.Rel rd (layerName first) args rets → MeaningKeccakLayer first rd args rets

/-! ## `verify_keccak` -/

/-- **`verify_keccak(fs0..fs4, cursor, tau_g, chi, output_lanes, z_vals, slices, tabs)`**
(G:3131-3302): on the window table `tabs` (`WinTabs`, which the layers' grinds read), for the
`KECCAK` table's log-height `τ` (`tau_g = g^τ`, `9 ≤ τ ≤ 28`, which
`verify_tables` certifies), the table sumcheck's point `chis` at `chi` (at least `τ`
coordinates) and the table's twenty-five output lane values `outs` at `output_lanes`: from the
carried capacity, the stream words `xs` at the cursor run `verifyKeccak τ (chis.take τ) outs` to
the committed outputs' claim `⟨qkeccak, op, word⟩`, the input opening's point and slices, leaving
the sponge `s'` with a full queue, the last four slices; `op` is at `z_vals`, the point at
`z_vals·g^39`, the slices at `slices`; the function returns the capacity after that queue's
permutation (which the next grind's `absorb` makes), the cursor past `xs` and `word`. -/
def MeaningVerifyKeccak (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, tg, chi, ol, zv, sl, tabs], rets =>
      WinTabs rd tabs → ∀ (τ : ℕ) (chis outs : List E), 9 ≤ τ → τ ≤ 28 → tg = gen ^ τ → τ ≤ chis.length →
        ReadsAt rd chi chis → outs.length = 25 → ReadsAt rd ol outs →
        ∃ (xs op point slices : List E) (word : E) (s' : Fs), ReadsAt rd cur xs ∧
          RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨[f0, f1, f2, f3, f4], []⟩ xs
            ([⟨qkeccak, op, word⟩], point, slices) s' ∧ s'.pend.length = rateScalars ∧
          ReadsAt rd zv op ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) point ∧ ReadsAt rd sl slices ∧
          op.length = τ + qkeccakSlotBits ∧ point.length = τ + qkeccakSlotBits ∧
          slices.length = 64 ∧ rets = capOf s'.perm ++ [cur * gen ^ xs.length, word]
  | _, _ => False

/-- `verify_keccak`'s core IR computes its meaning on the reader `rd` (proved on a memory image). -/
def verify_keccak_Spec (rd : Reader) : Prop :=
  ∀ (args rets : List E),
    coreProgram.Rel rd "verify_keccak" args rets → MeaningVerifyKeccak rd args rets

end
end LeanVM.Guest.B1.VerifySub
