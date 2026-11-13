/-
  LeanVM.Protocol.Verifier.Cost

  The query cost of leanVM's verifier program: per-phase cost bounds, an explicit bound over every
  announced size the verifier accepts, the Fiat-Shamir seed as a seeding, and the total query
  bound of the compiled verifier against the random oracles that `romSound` asks for.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.Compile.Cost
public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.WithHash

/-!
# The query cost of the leanVM verifier

`leanVmVerifierProgram bytecode publicInput` (`LeanVM.Protocol.Verifier`) is costed in the calculus
of `LeanVM.Protocol.Compile.Cost`, phase by phase, in quarters of a query: a scalar read costs `1`
(the sponge permutes once per four absorptions), a challenge `4` (one permutation), a proof of
work `5` (charged even where it grinds nothing), a commitment `2`, and an opening of `k` positions
`4 · k · (1 + height)` (one hash per leaf and per level). A run's shape depends on the sizes the
proof announces, but a run that is not rejected has sizes inside the window the program checks:
memory and table log-heights at most `30`, a bytecode of at most `2^30` tuples, a stack of
`16 ≤ μ ≤ 30` variables, a rate exponent `1 ≤ R ≤ 4`, and the WHIR ladder
`Parameters.Whir.ladder μ R`. The cost is maximised over that window:

* the sizes (`readAnnouncedSizes`): `8` reads;
* the stack's root (`commitStack`): one commitment, `2`, and its out-of-domain sample
  (`readOod`): a proof of work, at most `30` challenges and a read;
* the bus (`verifyBusBalance`): the proof of work, the `16` slot weights and `β`, the GKR walk over
  the push side's depth, at most `36` (`3 + 51` blocks of at most `2^30` rows), `gkrCost 36 0 =
  gkrBound`, the framework's reads and the bytecode's sumcheck;
* the table sumcheck (`tablePhase`): a proof of work and `ξ`, at most `30` rounds, the tables'
  columns read once;
* the public input: one challenge (the prover sends nothing);
* `KECCAK`'s reduction (`keccakPhase`, `verifyKeccak`) at a point of at most `27` coordinates:
  `keccakCost 27`;
* ring switching: a proof of work and `16` challenges;
* the stacked opening: the batching challenge and the WHIR levels (`whirCost`), at most
  `whirBound` over the 60 admissible ladders (`ladder_cost`, decided), every commitment of height
  at most `costHeight = 28`.

In total `leanVmCost` quarters (`costLE_leanVmProgram`). The seed of `spongeSeedWith` is one hash
and one permutation (`leanVmSeed`, `seedRun_leanVmSeed`), so the compiled verifier makes at most
`leanVmQueryBound = 1 + 1 + leanVmCost / 4` queries on every proof (`isTotalQueryBound_leanVm`),
evaluated in `leanVmQueryBound_eq`. The bound is crude where a tight one would cost proof without
changing the soundness bound, in which it enters linearly: the bus depth, the table heights and
the Keccak point are bounded by the announced sizes' window (`30`), not by the stack's size, the
WHIR query positions are charged at the largest height rather than at their level's, and a sample
right after a proof of work, which permutes nothing, is charged a permutation.

## Deployed behaviour

The bound is a statement on the program `leanVmVerifierProgram` as transcribed in
`Statement.LeanVmVerifier`,; it covers every proof, accepted or
not, and the deferring program `deferringVerifierProgram` alike (`costLE_deferringProgram`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

@[expose] public section

/-! ## Cost functions -/

/-- The cost of one round of a sumcheck whose round polynomial has `count` coefficients: the
polynomial's reads (one fewer than its coefficients, at least one), its proof of work, the
challenge. -/
def roundCost (count : ℕ) : ℕ := max count 2 - 1 + 5 + 4

/-- The cost of one GKR step of `step` levels at a point of `L` coordinates: a proof of work and
the combiner, the sumcheck's `L` rounds, the three trees' children, a proof of work and the new
coordinates. -/
def gkrStepCost (step L : ℕ) : ℕ :=
  5 + 4 + L * roundCost (2 ^ step + 1) + 3 * 2 ^ step + 5 + 4 * step

/-- The cost of the GKR walk over `n` remaining levels from a point of `L` coordinates, following
`gkrLayers`. -/
def gkrCost : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, L => gkrStepCost 1 L + gkrCost 0 (1 + L)
  | n + 2, L =>
    if n % 2 = 1 then gkrStepCost 1 L + gkrCost (n + 1) (1 + L)
    else gkrStepCost 2 L + gkrCost n (2 + L)

/-- The bound on the GKR walk: the push side's depth is at most `36`. -/
def gkrBound : ℕ := gkrCost 36 0

/-- The cost of the bus phase: the proof of work, the slot weights and `β`, the roots and the GKR
walk, the framework's four reads, and the bytecode's share, sumcheck and value. -/
def busCost : ℕ :=
  5 + 4 * 2 ^ busBits + 4 + (2 + gkrBound) + 4 + (1 + busBits * roundCost 3 + 1)

/-- The tables' columns. -/
def tableWidthSum : ℕ := (tables.map Table.width).sum

/-- The cost of the table phase: a proof of work and `ξ`, at most `30` rounds of four
coefficients, every table's columns. -/
def tableCost : ℕ := 5 + 4 + (30 * roundCost 4 + tableWidthSum)

/-- The rounds of `sample_queries` for `count` positions of `depth` bits: one challenge yields
`128 / depth` positions. -/
def queryRounds (depth count : ℕ) : ℕ :=
  if 128 / depth = 0 then count else (count + 128 / depth - 1) / (128 / depth)

/-- The cost of one fold round: four reads, a proof of work and `α, β`. -/
def foldRoundCost : ℕ := 4 + 5 + 2 * 4

/-- The cost of the WHIR levels from a message of `μ` variables, following `whirLevels`: per
level its fold rounds; on a non-final level the commitment, its high part, the out-of-domain
point and its value, the proofs of work, the query positions and the batching challenge, and the
openings at `height`; on the final level the folded lane, the proof of work, the query
positions and the openings, and the tail sumcheck. -/
def whirCost (height : ℕ) : ℕ → List Whir.Level → ℕ
  | _, [] => 0
  | μ, [level] =>
    foldRoundCost * level.fold + (2 ^ (μ - level.fold) + level.fold) + 5 +
      4 * queryRounds (μ - level.fold + level.logInvRate) level.queries +
      VerifierProgram.openCost height level.queries + (μ - level.fold) * roundCost 3
  | μ, level :: next :: rest =>
    foldRoundCost * level.fold + 2 + level.fold + 5 + 4 * (μ - level.fold) + 1 + 5 +
      4 * queryRounds (μ - level.fold + level.logInvRate) level.queries +
      4 + VerifierProgram.openCost height level.queries +
      whirCost height (μ - level.fold) (next :: rest)

/-- Every commitment the WHIR levels read from a message of `μ` variables has height at most
`height`. -/
def whirHeightsLE (height : ℕ) : ℕ → List Whir.Level → Bool
  | _, [] => true
  | _, [_] => true
  | μ, level :: next :: rest =>
    decide (μ - level.fold - next.fold + next.logInvRate ≤ height) &&
      whirHeightsLE height (μ - level.fold) (next :: rest)

/-- The stack's commitment, read at the first level's shape, has height at most `height`. -/
def stackHeightLE (height μ : ℕ) : List Whir.Level → Bool
  | [] => true
  | level :: _ => decide (μ - level.fold + level.logInvRate ≤ height)

/-- Every query position of every admissible ladder has between `1` and `64` bits. -/
def queryDepthsLE : ℕ → List Whir.Level → Bool
  | _, [] => true
  | μ, level :: rest =>
    decide (1 ≤ μ - level.fold + level.logInvRate ∧ μ - level.fold + level.logInvRate ≤ 64) &&
      queryDepthsLE (μ - level.fold) rest

/-- The bound on every commitment's height. -/
def costHeight : ℕ := 28

/-- The bound on the WHIR levels' cost over every admissible ladder (`ladder_cost`). -/
def whirBound : ℕ := 43140

/-- The cost of one layer of the Keccak reduction at a point of `L` coordinates: the product
polynomial, its proof of work and point, the pack rounds, the bit-position sumcheck, the three
values, and the proof of work and combiner. -/
def keccakLayerCost (L : ℕ) : ℕ :=
  productBits + 5 + 4 + L * roundCost 3 + keccakLocalBits * roundCost 4 + 3 + 5 + 4

/-- The cost of `verifyKeccak` at a point of `L` coordinates after the instances. -/
def keccakCost (L : ℕ) : ℕ :=
  5 + 4 * keccakSegmentBits + 4 * keccakLaneBits + 1 + keccakDepth * keccakLayerCost L +
    (qkeccakSlotBits * roundCost 3 + 1) + 4 * roundCost 3 + qkeccakSlotBits * roundCost 3 + kBits

/-- The cost of the stack's out-of-domain sample: a proof of work, at most `30` challenges and a
read. -/
def oodCost : ℕ := 5 + 4 * Whir.maxLogStack + 1

/-- The cost of ring switching: a proof of work and sixteen challenges. -/
def ringCost : ℕ := 5 + 4 * (2 * ringMapWidth)

/-- **The cost of the leanVM verifier program**, phase by phase, in quarters of a query. -/
def leanVmCost : ℕ :=
  8 + 2 + oodCost + busCost + tableCost + 4 + keccakCost 27 + ringCost + (4 + whirBound)

/-! ## Sumcheck rounds -/

section Phases

variable {height : ℕ}

/-- A pure step that may fail costs nothing, and returns what the option holds. -/
theorem costs_liftOption {α : Type} (o : Option α) (n : ℕ) :
    VerifierProgram.Costs height (liftOption o) n fun a ↦ o = some a := by
  cases o
  · trivial
  · rfl

/-- A round polynomial of `count` coefficients reads `count - 1` of them (at least one), then
grinds. -/
theorem costs_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    VerifierProgram.Costs height (sumcheckRoundPoly count claim eq) (max count 2 - 1 + 5)
      fun _ ↦ True := by
  cases eq with
  | none =>
    refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
        VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _)
      (fun _ _ ↦ VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _)
        (fun _ _ ↦ trivial) ?_) ?_) ?_ <;> omega
  | some r =>
    exact VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦ trivial) (by omega))
      (by omega)

/-- A sumcheck of `k` rounds costs `k · roundCost count`, and returns `k` challenges. -/
theorem costs_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    VerifierProgram.Costs height (sumcheck claim count eqs) (eqs.length * roundCost count)
      fun r ↦ r.1.length = eqs.length
  | _, [] => rfl
  | claim, e :: es => by
    refine VerifierProgram.Costs.seq (costs_sumcheckRoundPoly count claim e) (fun msg _ ↦
      VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun c _ ↦
        VerifierProgram.Costs.seq (costs_sumcheck count _ es) (fun r hr ↦ ?_) ?_) ?_) ?_
    · obtain ⟨point, final⟩ := r
      show (c :: point).length = (e :: es).length
      simpa using hr
    all_goals simp only [List.length_cons, Nat.succ_mul, roundCost]; omega

/-! ## The bus -/

theorem costs_gkrStep (step : ℕ) (last : Bool) (s : GkrState) :
    VerifierProgram.Costs height (gkrStep step last s) (gkrStepCost step s.point.length)
      fun t ↦ t.point.length = step + s.point.length := by
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦
    VerifierProgram.Costs.seq (costs_sumcheck _ _ (s.point.map some)) (fun r hr ↦ ?_) ?_) ?_) ?_
  · obtain ⟨x, claim⟩ := r
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun c0 _ ↦
        VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _)
      (fun c1 _ ↦ VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun c2 _ ↦
        VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
          VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
          VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN step) (fun y hy ↦ ?_) ?_) ?_)
            ?_) ?_) ?_) ?_
    · show (y ++ x).length = step + s.point.length
      simp only [List.length_map] at hr
      simp [hy, hr]
    all_goals simp only [gkrStepCost, List.length_map]; omega
  all_goals simp only [gkrStepCost, List.length_map]; omega

/-- The GKR walk costs `gkrCost`. -/
theorem costs_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    VerifierProgram.Costs height (gkrLayers n s) (gkrCost n s.point.length) fun _ ↦ True
  | 0, _ => trivial
  | 1, s => by
    refine VerifierProgram.Costs.seq (costs_gkrStep 1 true s) (fun t ht ↦
      (costs_gkrLayers 0 t).mono (by simp [gkrCost]) fun _ h ↦ h) ?_
    simp only [gkrCost]; omega
  | n + 2, s => by
    simp only [gkrLayers, gkrCost]
    split
    · refine VerifierProgram.Costs.seq (costs_gkrStep 1 false s) (fun t ht ↦
        (costs_gkrLayers (n + 1) t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)
    · refine VerifierProgram.Costs.seq (costs_gkrStep 2 _ s) (fun t ht ↦
        (costs_gkrLayers n t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)

/-- The GKR grand products: the two roots and the walk. -/
theorem costs_verifyGkrGrandProducts (depth : ℕ) :
    VerifierProgram.Costs height (verifyGkrGrandProducts depth) (2 + gkrCost depth 0) fun _ ↦
        True := by
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦ VerifierProgram.Costs.seq
      VerifierProgram.Costs.readE
    (fun _ _ ↦ VerifierProgram.Costs.seq (costs_gkrLayers depth _) (fun _ _ ↦ trivial) ?_)
        ?_) ?_ <;>
    (try simp only [List.length_nil]) <;> omega

/-- The bytecode's share: a read, a sumcheck over the tuple slot, a read. -/
theorem costs_bytecodeShare (weights bytecodeLow : List E) :
    VerifierProgram.Costs height (bytecodeShare weights bytecodeLow)
      (1 + busBits * roundCost 3 + 1) fun _ ↦ True := by
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
    VerifierProgram.Costs.seq (costs_sumcheck 3 _ _) (fun r _ ↦ ?_) ?_) ?_
  · obtain ⟨slotPoint, claim⟩ := r
    exact VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ trivial)
        (Nat.zero_le _)) (by rw [List.length_replicate]; omega)
  all_goals (try simp only [List.length_replicate]); omega

/-- The claims on `KECCAK` output lanes are at points of at most `30` coordinates. -/
def ClaimsShort (claims : List ColumnClaim) : Prop :=
  ∀ c ∈ claims, c.column ∈ keccakOutputColumns → c.point.length ≤ 30

/-- The bus phase, at the push side's depth, for a check of the fixed polynomial's value that
costs nothing. -/
theorem costs_verifyBusBalance (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, VerifierProgram.Costs height (ev w p v) 0 fun _ ↦ True) (layout : Layout)
    (hm : layout.logMemory ≤ 30) (hb : layout.logBytecode ≤ 30) :
    VerifierProgram.Costs height (verifyBusBalance ev layout)
      (5 + 4 * 2 ^ busBits + 4 + (2 + gkrCost (busLayout [0, layout.logMemory, layout.logBytecode]
        layout.push).depth 0) + 4 + (1 + busBits * roundCost 3 + 1))
      fun r ↦ ClaimsShort r.claims := by
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun _ _ ↦
      VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE
    (fun _ _ ↦ VerifierProgram.Costs.seq (costs_verifyGkrGrandProducts _) (fun r _ ↦ ?_) ?_) ?_)
      ?_) ?_) (Nat.zero_le _)
  · obtain ⟨countRoot, point, treeValues⟩ := r
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
        VerifierProgram.Costs.seq (VerifierProgram.Costs.readN 2)
      (fun memory hmem ↦ VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
          VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
            VerifierProgram.Costs.seq (costs_bytecodeShare _ _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_)
        (Nat.zero_le _)
    · obtain ⟨share, bytecodePoint, value⟩ := r
      refine VerifierProgram.Costs.seq (hev _ _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      intro c hc _
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
        simp only [List.getElem_zipWith, List.length_take]
        omega
      · simp only [List.length_take]; omega
      · simp only [List.length_take]; omega
    all_goals omega
  all_goals omega

end Phases

/-! ## The bus depth -/

/-- `log2Ceil v ≤ k` when `v ≤ 2^k`. -/
theorem log2Ceil_le {v k : ℕ} (h : v ≤ 2 ^ k) : log2Ceil v ≤ k := by
  unfold log2Ceil bitLength
  split
  · exact Nat.zero_le _
  · rename_i hv
    have := (Nat.log2_lt hv).mpr (by omega : v - 1 < 2 ^ k)
    omega

private theorem foldl_place_snd_le (size : ℕ → ℕ) (M : ℕ) (hM : ∀ i, size i ≤ M) :
    ∀ (order : List ℕ) (acc : List ℕ × ℕ),
      (order.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i)) acc).2 ≤
        acc.2 + order.length * 2 ^ M
  | [], acc => by simp
  | i :: is, acc => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := foldl_place_snd_le size M hM is (acc.1.set i acc.2, acc.2 + 2 ^ size i)
    have h2 : 2 ^ size i ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) (hM i)
    simp only at h1
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- The stacked cube of blocks of at most `2^M` rows, at most `2^c` of them, has at most
`M + c` variables. -/
theorem stackOffsets_snd_le (sizes : List ℕ) (M c : ℕ) (hs : ∀ x ∈ sizes, x ≤ M)
    (hl : sizes.length ≤ 2 ^ c) : (stackOffsets sizes).2 ≤ M + c := by
  unfold stackOffsets
  refine log2Ceil_le ?_
  refine (foldl_place_snd_le (fun i ↦ sizes.getD i 0) M (fun i ↦ ?_) _ _).trans ?_
  · rw [List.getD_eq_getElem?_getD]
    cases h : sizes[i]? with
    | none => simp
    | some x => exact hs x (List.mem_of_getElem? h)
  · simp only [List.length_mergeSort, List.length_range, Nat.zero_add]
    rw [Nat.pow_add, Nat.mul_comm (2 ^ M)]
    exact Nat.mul_le_mul_right _ hl

/-- Every push block has the log-height of a table. -/
theorem busBlocks_push_logRows (hs rows : List ℕ) :
    ∀ b ∈ (busBlocks hs rows).1, b.logRows ∈ hs := by
  intro b hb
  simp only [busBlocks, List.mem_flatMap, List.mem_map] at hb
  obtain ⟨⟨t, h, n⟩, hmem, c, -, rfl⟩ := hb
  exact (List.of_mem_zip (List.of_mem_zip hmem).2).1

/-- The tables flush `51` pushes. -/
theorem busBlocks_push_length (hs rows : List ℕ) (h : hs.length = 6) (hr : rows.length = 6) :
    (busBlocks hs rows).1.length = 51 := by
  match hs, rows, h, hr with
  | [_, _, _, _, _, _], [_, _, _, _, _, _], _, _ => rfl

/-! ## The announced sizes -/

/-- What `buildLayout` guarantees of a layout it returns. -/
structure LayoutBounds (layout : Layout) : Prop where
  /-- The memory has at most `2^30` cells. -/
  logMemory_le : layout.logMemory ≤ 30
  /-- The bytecode has at most `2^30` tuples. -/
  logBytecode_le : layout.logBytecode ≤ 30
  /-- One height per table. -/
  heights_length : layout.tableLogHeights.length = 6
  /-- Every table has at most `2^30` rows. -/
  heights_le : ∀ h ∈ layout.tableLogHeights, h ≤ 30
  /-- The push side's blocks are the tables' push flushes, at some row count per table. -/
  push_eq : ∃ tableRows : List ℕ, tableRows.length = 6 ∧
    layout.push = (busBlocks layout.tableLogHeights tableRows).1

/-- A layout `buildLayout` returns is within its bounds. -/
theorem layoutBounds_of_buildLayout {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    LayoutBounds layout := by
  unfold buildLayout at h
  split at h
  · simp at h
  · split_ifs at h with hc
    rename_i logLength _
    obtain ⟨-, -, hm, hall, hb, hlen⟩ := hc
    set hts := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors
    rcases hbb : busBlocks hts tableRows with ⟨push, pull, count⟩
    rcases hpl : placementsOf (columnKappas logMemory (logLength - busBits) hts) with ⟨pl, sl⟩
    simp only [hbb, hpl, Option.some.injEq] at h
    subst h
    have hlen6 : tableRows.length = 6 := by simpa [tables] using hlen
    refine ⟨hm, hb, ?_, ?_, ⟨tableRows, hlen6, by simp [hbb]⟩⟩
    · simp [hts, hlen6, tableLogFloors]
    · simp only [List.all_eq_true, decide_eq_true_eq] at hall
      intro x hx
      obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hx
      simp only [hts, List.getElem_zipWith] at hx
      rw [← hx]
      have hi1 : i < tableRows.length := by simp [hts] at hi; omega
      have hi2 : i < tableLogFloors.length := by simp [hts] at hi; omega
      refine max_le (log2Ceil_le (hall _ (List.getElem_mem hi1))) ?_
      have : ∀ f ∈ tableLogFloors, f ≤ 30 := by decide
      exact this _ (List.getElem_mem hi2)

/-- The sizes a run of `readAnnouncedSizes` returns: a layout `buildLayout` built, the stack in the
window, the rate exponent in `1..4`. -/
def SizesOK (p : Layout × ℕ) : Prop :=
  LayoutBounds p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 4 ∧ Whir.minLogStack ≤ p.1.stackLog ∧
    p.1.stackLog ≤ Whir.maxLogStack

/-- The announced sizes: eight reads, and sizes in the window the program checks. -/
theorem costs_readSizes {height : ℕ} (bytecode : List K) :
    VerifierProgram.Costs height (readAnnouncedSizes bytecode) 8 SizesOK := by
  rw [readAnnouncedSizes_eq]
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _)
    (fun _ _ ↦ (costs_liftOption _ _).mono le_rfl fun x hx ↦ ?_) (by simp [tables])
  have s := sizesOf_spec hx
  exact ⟨layoutBounds_of_buildLayout s.layout, s.rate_ge, s.rate_le, s.stack_ge, s.stack_le⟩

/-- The push side of a built layout has depth at most `36`. -/
theorem pushDepth_le {layout : Layout} (h : LayoutBounds layout) :
    (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth ≤ 36 := by
  refine stackOffsets_snd_le _ 30 6 ?_ ?_
  · intro x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | rfl | rfl | ⟨b, hb, rfl⟩
    · omega
    · exact h.logMemory_le
    · exact h.logBytecode_le
    · obtain ⟨rows, -, hp⟩ := h.push_eq
      rw [hp] at hb
      exact h.heights_le _ (busBlocks_push_logRows _ _ _ hb)
  · obtain ⟨rows, hr, hp⟩ := h.push_eq
    simp [hp, busBlocks_push_length _ _ h.heights_length hr]

/-- The GKR walk over at most `36` levels costs at most `gkrBound`. -/
theorem gkrCost_le : ∀ D ≤ 36, gkrCost D 0 ≤ gkrBound := by decide


/-- **The bus phase** on a built layout. -/
theorem costs_verifyBusBalance_le {height : ℕ} (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, VerifierProgram.Costs height (ev w p v) 0 fun _ ↦ True) {layout : Layout}
    (h : LayoutBounds layout) :
    VerifierProgram.Costs height (verifyBusBalance ev layout) busCost
      fun r ↦ ClaimsShort r.claims :=
  (costs_verifyBusBalance ev hev layout h.logMemory_le h.logBytecode_le).mono
    (by have := gkrCost_le _ (pushDepth_le h); unfold busCost; omega) fun _ h ↦ h

/-! ## The table sumcheck and the public input -/

section Phases2

variable {height : ℕ}

/-- The tables' row evaluations: each table's columns read once; the claims at points of at most
the rows' heights. -/
theorem costs_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), ClaimsShort claims → (∀ r ∈ rows, r.2.1 ≤ 30) →
      VerifierProgram.Costs height
        (tableTermsClaims constraintPowers formPowers point rows cursor final claims)
        (rows.map (·.1.width)).sum fun r ↦ ClaimsShort r.2
  | [], _, _, claims, hc, _ => hc
  | (table, h, forms, weight) :: rest, cursor, final, claims, hc, hh => by
    have h0 : h ≤ 30 := hh _ List.mem_cons_self
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun evals _ ↦
      (costs_tableTerms constraintPowers formPowers point rest _ _ _ ?_
        fun r hr ↦ hh r (List.mem_cons_of_mem _ hr)).mono ?_ fun _ h ↦ h) ?_
    · intro c hc' hcol
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact hc c hc' hcol
      · obtain ⟨⟨v, col⟩, -, rfl⟩ := List.mem_map.mp hc'
        simp only [List.length_take]
        omega
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons, List.sum_cons]; omega

private theorem foldl_max_le (M : ℕ) : ∀ (l : List ℕ) (acc : ℕ), acc ≤ M → (∀ x ∈ l, x ≤ M) →
    l.foldl max acc ≤ M
  | [], _, h, _ => h
  | x :: xs, acc, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le M xs _ (max_le h (hl x List.mem_cons_self))
      fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)

/-- The widths of the first components of a zip are at most the widths of the list. -/
theorem sum_width_zip {β : Type} : ∀ (l : List Table) (m : List β),
    ((List.zip l m).map fun r ↦ r.1.width).sum ≤ (l.map Table.width).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | t :: l, _ :: m => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have := sum_width_zip l m
    omega

/-- The table sumcheck over tables of at most `2^30` rows. -/
theorem costs_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E)
    (hh : ∀ h ∈ heights, h ≤ 30) :
    VerifierProgram.Costs height
      (tableSumcheckClaims heights busForms constraintPowers formPowers equalityPoint target)
      (30 * roundCost 4 + tableWidthSum) fun cl ↦ ClaimsShort cl := by
  have hmax := foldl_max_le 30 heights 0 (Nat.zero_le _) hh
  have hr4 : roundCost 4 = 12 := rfl
  refine VerifierProgram.Costs.seq (costs_sumcheck _ _ _) (fun r _ ↦ ?_) ?_
  · obtain ⟨challenges, claim⟩ := r
    have hrows : ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse))), r.2.1 ≤ 30 := by
      intro r hr
      exact hh _ (List.of_mem_zip (List.of_mem_zip hr).2).1
    refine VerifierProgram.Costs.seq (costs_tableTerms _ _ _ _ 0 0 [] (fun _ h ↦
        by simp at h) hrows)
      (fun r hr ↦ ?_) ?_
    · obtain ⟨final, claims⟩ := r
      exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ hr)
          (Nat.zero_le _)
    · simp only [List.length_replicate, hr4]
      have := sum_width_zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse)))
      unfold tableWidthSum
      omega
  · simp only [List.length_replicate, hr4]
    omega

/-- **The table phase** on a built layout. -/
theorem costs_tablePhase {layout : Layout} (hl : LayoutBounds layout) (bus : BusResult)
    (hbus : ClaimsShort bus.claims) :
    VerifierProgram.Costs height (tablePhaseClaims layout bus) tableCost
      fun cl ↦ ClaimsShort cl :=
  VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
  VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦ VerifierProgram.Costs.seq
    (costs_tableSumcheck _ _ _ _ _ _ hl.heights_le) (fun cl hcl ↦ by
      intro c hc hcol
      rcases List.mem_append.mp hc with hc | hc
      · exact hbus c hc hcol
      · exact hcl c hc hcol) (by unfold tableCost; omega)) (by unfold tableCost; omega))
    (by unfold tableCost; omega)

/-- **The public-input phase**: one challenge; its claims are on the memory's columns. -/
theorem costs_publicInputPhase (layout : Layout) (publicInput : Digest) :
    VerifierProgram.Costs height (publicInputPhase layout publicInput) 4 fun cl ↦ ClaimsShort
        cl := by
  rw [publicInputPhase_eq]
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE
    (fun _ _ ↦ (costs_liftOption _ _).mono le_rfl fun cl hcl ↦ ?_) (by omega)
  rw [publicClaimsOf_spec hcl]
  simp only [publicClaims]
  intro c hc hcol
  exfalso
  have hbase : ∀ x ∈ keccakOutputColumns, 5 ≤ x := by
    intro x hx
    simp only [keccakOutputColumns, List.mem_map] at hx
    obtain ⟨_, -, rfl⟩ := hx
    have : 5 ≤ globalColumnBases.getD opKeccak 0 := by decide
    omega
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  simp only [List.getElem_zipWith] at hcol
  have hi' : i < 2 := by simp at hi; omega
  have hle : [memory0, memory1][i] < 2 := by
    interval_cases i <;> simp [memory0, memory1]
  have := hbase _ hcol
  omega

/-! ## Keccak and ring switching -/

/-- The pack rounds: one equality-mode round of three coefficients per coordinate, keeping the
point's length. -/
theorem costs_keccakPackRounds : ∀ (point : List E) (value scale : E),
    VerifierProgram.Costs height (keccakPackRounds point value scale) (point.length * roundCost 3)
      fun r ↦ r.2.2.length = point.length
  | [], _, _ => rfl
  | r :: rs, value, scale => by
    refine VerifierProgram.Costs.seq (costs_sumcheckRoundPoly 3 _ _) (fun _ _ ↦
        VerifierProgram.Costs.seq
      VerifierProgram.Costs.sampleE (fun c _ ↦ VerifierProgram.Costs.seq (costs_keccakPackRounds
          rs _ _)
        (fun t ht ↦ ?_) ?_) ?_) ?_
    · obtain ⟨v, s, p⟩ := t
      show (c :: p).length = (r :: rs).length
      simpa using ht
    all_goals simp only [List.length_cons, Nat.succ_mul, roundCost]; omega

/-- One layer of the Keccak reduction keeps the claim's point length. -/
theorem costs_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    VerifierProgram.Costs height (verifyKeccakLayer logSteps step claim)
      (keccakLayerCost claim.point.length) fun c ↦ c.point.length = claim.point.length := by
  have hr4 : roundCost 4 = 12 := rfl
  have hr3 : roundCost 3 = 11 := rfl
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
      VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦
      VerifierProgram.Costs.seq (costs_keccakPackRounds _ _ _) (fun r hr ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨value, scale, point⟩ := r
    refine VerifierProgram.Costs.seq (costs_sumcheck 4 _ _) (fun r _ ↦ ?_) ?_
    · obtain ⟨localPoint, value⟩ := r
      refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN 3) (fun _ _ ↦
          VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
            VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
            VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦ hr) ?_) ?_) ?_) ?_
      all_goals simp only [keccakLayerCost, List.length_replicate, hr4, hr3]
      all_goals omega
    · simp only [keccakLayerCost, List.length_replicate, hr4, hr3]
      omega
  all_goals simp only [keccakLayerCost, hr4, hr3]; omega

/-- The Keccak layers keep the claim's point length. -/
theorem costs_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    VerifierProgram.Costs height (keccakLayers logSteps steps claim)
      (steps.length * keccakLayerCost claim.point.length)
      fun c ↦ c.point.length = claim.point.length
  | [], _ => rfl
  | s :: ss, claim => by
    refine VerifierProgram.Costs.seq (costs_verifyKeccakLayer logSteps s claim) (fun c hc ↦
      (costs_keccakLayers logSteps ss c).mono (by
        rw [hc]; simp only [List.length_cons, Nat.succ_mul]; omega) fun _ h ↦ h.trans hc) ?_
    simp only [List.length_cons, Nat.succ_mul]; omega

/-- Opening `q_keccak`: a sumcheck over the slot. -/
theorem costs_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    VerifierProgram.Costs height (keccakOpen logSteps claim first count value)
      (qkeccakSlotBits * roundCost 3) fun _ ↦ True :=
  VerifierProgram.Costs.seq (costs_sumcheck 3 _ _) (fun _ _ ↦ trivial)
    (by simp only [List.length_replicate]; omega)

/-- **The Keccak reduction** at an instance point of at most `30` coordinates. -/
theorem costs_verifyKeccak (logSteps : ℕ) (inst output : List E) (hi : inst.length ≤ 30) :
    VerifierProgram.Costs height (verifyKeccak logSteps inst output) (keccakCost 27) fun _ ↦
        True := by
  have hL : (inst.drop 4).length + keccakSegmentBits ≤ 27 := by
    simp only [List.length_drop, keccakSegmentBits]
    have : log2Ceil keccakSegments = 1 := by decide
    omega
  have h1 : 1 < keccakSegments := by decide
  have hr3 : roundCost 3 = 11 := rfl
  unfold verifyKeccak
  simp only [h1, ↓reduceIte]
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun segment hseg ↦
      VerifierProgram.Costs.seq
    (VerifierProgram.Costs.sampleN _) (fun _ _ ↦ VerifierProgram.Costs.seq
        VerifierProgram.Costs.readE (fun committed _ ↦ ?_) ?_)
    ?_) ?_) ?_
  · have hpl : (inst.drop 4 ++ segment).length ≤ 27 := by
      rw [List.length_append, hseg]; exact hL
    have hlay : keccakDepth * keccakLayerCost (inst.drop 4 ++ segment).length ≤
        keccakDepth * keccakLayerCost 27 := by
      refine Nat.mul_le_mul_left _ ?_
      unfold keccakLayerCost
      have := Nat.mul_le_mul_right (roundCost 3) hpl
      omega
    refine VerifierProgram.Costs.seq (costs_keccakLayers logSteps (List.range keccakDepth) _)
      (fun claim _ ↦ VerifierProgram.Costs.seq (costs_keccakOpen logSteps _ 1 _ _) (fun r _ ↦
        VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun word _ ↦
            VerifierProgram.Costs.seq
          (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ VerifierProgram.Costs.seq
              (VerifierProgram.Costs.pure0 _)
            (fun outputs _ ↦ VerifierProgram.Costs.seq (costs_sumcheck 3 _ _) (fun r2 _ ↦
              VerifierProgram.Costs.seq (costs_keccakOpen logSteps _ 0 _ _) (fun r3 _ ↦
                VerifierProgram.Costs.seq (VerifierProgram.Costs.readN kBits) (fun slices _ ↦
                  VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
                      trivial)
                    (Nat.zero_le _)) ?_) ?_) ?_) (Nat.zero_le _)) (Nat.zero_le _)) ?_) ?_) ?_
    all_goals simp only [keccakCost, keccakFirstClaim, List.length_range, List.length_replicate,
      hr3] at hlay ⊢
    all_goals omega
  all_goals simp only [keccakCost, hr3]; omega

/-- The first claim on a `KECCAK` output lane is at a point of at most `30` coordinates. -/
theorem headD_filter_short : ∀ (l : List ColumnClaim), ClaimsShort l →
    ((l.filter fun c ↦ decide (c.column ∈ keccakOutputColumns)).headD default).point.length ≤ 30
  | [], _ => by
    show (default : ColumnClaim).point.length ≤ 30
    rw [show (default : ColumnClaim).point = [] from rfl]
    simp
  | c :: l, h => by
    by_cases hc : c.column ∈ keccakOutputColumns
    · simp only [List.filter_cons, hc, decide_true, ↓reduceIte, List.headD_cons]
      exact h c List.mem_cons_self hc
    · simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact headD_filter_short l fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')

/-- **The Keccak phase**, its claims at points of at most `30` coordinates. -/
theorem costs_keccakPhase (layout : Layout) (claims : List ColumnClaim)
    (hc : ClaimsShort claims) :
    VerifierProgram.Costs height (keccakPhaseClaims layout claims) (keccakCost 27) fun _ ↦
        True := by
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
      VerifierProgram.Costs.seq
    (costs_verifyKeccak _ _ _ (headD_filter_short claims hc)) (fun _ _ ↦ trivial) le_rfl)
    (Nat.zero_le _)

/-- **Ring switching**: a proof of work and sixteen challenges. -/
theorem costs_ringSwitch (point s : List E) :
    VerifierProgram.Costs height (ringSwitch point s) ringCost fun _ ↦ True := by
  rw [ringSwitch_eq]
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _)
      (fun _ _ ↦ (costs_liftOption _ _).mono le_rfl fun _ _ ↦ trivial)
      (by simp [ringCost])) (by simp [ringCost])

/-- **The stack's out-of-domain sample**, on a stack of at most `30` variables. -/
theorem costs_readOod (stackLog : ℕ) (h : stackLog ≤ Whir.maxLogStack) :
    VerifierProgram.Costs height (readOod stackLog) oodCost fun _ ↦ True := by
  rw [readOod_eq]
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun _ _ ↦
      VerifierProgram.Costs.seq VerifierProgram.Costs.readE
        (fun _ _ ↦ (costs_liftOption _ _).mono le_rfl fun _ _ ↦ trivial) (by
        unfold oodCost; omega)) (by unfold oodCost; omega)) (by unfold oodCost; omega)

end Phases2

/-! ## WHIR -/

section Whir

variable {height : ℕ}

/-- A fold round: four reads, a proof of work, two challenges; it appends one `α`. -/
theorem costs_foldRound (s : WhirState) :
    VerifierProgram.Costs height (foldRound s) foldRoundCost
      fun r ↦ r.1.alphas.length = s.alphas.length + 1 := by
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦ ?_)
      ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · show (s.alphas ++ [_]).length = s.alphas.length + 1
    simp
  all_goals simp only [foldRoundCost]; omega

/-- A level's fold rounds; they append one `α` each. -/
theorem costs_foldRounds : ∀ (n : ℕ) (s : WhirState),
    VerifierProgram.Costs height (foldRounds n s) (foldRoundCost * n)
      fun r ↦ r.1.alphas.length = s.alphas.length + n
  | 0, _ => rfl
  | n + 1, s => by
    refine VerifierProgram.Costs.seq (costs_foldRound s) (fun r hr ↦ ?_) ?_
    · obtain ⟨s', round⟩ := r
      refine VerifierProgram.Costs.seq (costs_foldRounds n s') (fun r' hr' ↦ ?_) ?_
      · obtain ⟨s'', rounds⟩ := r'
        show s''.alphas.length = s.alphas.length + (n + 1)
        simp only at hr hr'
        omega
      · rw [Nat.mul_succ]; omega
    · rw [Nat.mul_succ]; omega

/-- The query sampling loop: one challenge per `128 / depth` positions, and at most `remaining`
positions. -/
theorem costs_sampleQueriesAux (depth : ℕ) (hd1 : 1 ≤ depth) (hd : depth ≤ 64) :
    ∀ (fuel remaining : ℕ),
    VerifierProgram.Costs height (sampleQueriesAux depth fuel remaining) (4 * queryRounds depth
        remaining)
      fun qs ↦ qs.length ≤ remaining
  | 0, _ => Nat.zero_le _
  | fuel + 1, remaining => by
    have hper : 2 ≤ 128 / depth := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hq : queryRounds depth remaining = (remaining + 128 / depth - 1) / (128 / depth) := by
      simp [queryRounds, show 128 / depth ≠ 0 by omega]
    refine VerifierProgram.Costs.ite (fun _ ↦ Nat.zero_le _) fun hr ↦ VerifierProgram.Costs.seq
        VerifierProgram.Costs.sampleE
      (fun c _ ↦ VerifierProgram.Costs.seq (costs_sampleQueriesAux depth hd1 hd fuel _) (fun qs hqs
          ↦ ?_) ?_)
      ?_
    · show (List.map _ (List.range (min (128 / depth) remaining)) ++ qs).length ≤ remaining
      simp only [List.length_append, List.length_map, List.length_range]
      omega
    · have hq' : queryRounds depth (remaining - min (128 / depth) remaining) =
          (remaining - min (128 / depth) remaining + 128 / depth - 1) / (128 / depth) := by
        simp [queryRounds, show 128 / depth ≠ 0 by omega]
      rw [hq', hq]
      generalize 128 / depth = d at hper ⊢
      have key : (remaining - min d remaining + d - 1) / d + 1 ≤ (remaining + d - 1) / d := by
        rcases le_total d remaining with h | h
        · rw [min_eq_left h, show remaining - d + d - 1 = remaining - 1 by omega]
          rw [show remaining + d - 1 = (remaining - 1) + d * 1 by omega,
            Nat.add_mul_div_left _ _ (by omega)]
        · rw [min_eq_right h, Nat.sub_self, Nat.zero_add, Nat.div_eq_of_lt (by omega)]
          exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      omega
    · rw [hq]
      have h1 : 1 ≤ (remaining + 128 / depth - 1) / (128 / depth) :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      omega

theorem costs_sampleQueries (depth count : ℕ) (hd : 1 ≤ depth ∧ depth ≤ 64) :
    VerifierProgram.Costs height (sampleQueries depth count) (4 * queryRounds depth count)
      fun qs ↦ qs.length ≤ count :=
  costs_sampleQueriesAux depth hd.1 hd.2 count count

/-- Gluing a level's claims keeps the `α`s. -/
theorem glueLevel_alphas (s : WhirState) (lam : E) (mu : ℕ) (oodPoint : List E)
    (oodValue : E) (queries : List ℕ) (queryWeights : List E) (batched : E) :
    (glueLevel s lam mu oodPoint oodValue queries queryWeights batched).alphas = s.alphas := rfl

theorem openCost_mono {height : ℕ} {k k' : ℕ} (h : k ≤ k') :
    VerifierProgram.openCost height k ≤ VerifierProgram.openCost height k' := by
  unfold VerifierProgram.openCost; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)

/-- **The WHIR levels** from a message of `μ` variables cost `whirCost`, when their commitments
have height at most `height` and their query positions at most `64` bits. -/
theorem costs_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (μ : ℕ),
      logN - s.alphas.length = μ → whirHeightsLE height μ levels = true →
      queryDepthsLE μ levels = true →
      VerifierProgram.Costs height (whirLevels logN laneFolds evaluateBasis index levels s)
        (whirCost height μ levels) fun _ ↦ True
  | [], _, _, _, _, _, _ => trivial
  | [level], index, s, μ, hμ, _, hD => by
    simp only [queryDepthsLE, Bool.and_eq_true, decide_eq_true_eq] at hD
    have hr3 : roundCost 3 = 11 := rfl
    simp only [whirCost]
    generalize hP : 2 ^ (μ - level.fold) = P
    refine VerifierProgram.Costs.seq (costs_foldRounds level.fold s) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', rounds⟩ := r
    simp only at hr
    have hm : logN - s'.alphas.length = μ - level.fold := by rw [hr]; omega
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
          VerifierProgram.Costs.seq
        (costs_sampleQueries _ level.queries (by rw [hm]; exact hD.1)) (fun queries hq ↦ ?_)
          ?_) ?_) ?_
    · have hqm := openCost_mono (height := height) hq
      refine VerifierProgram.Costs.seq (VerifierProgram.Costs.queryP index queries) (fun words _ ↦
        VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
          VerifierProgram.Costs.seq (costs_sumcheck 3 _ _) (fun r _ ↦ ?_) ?_) (Nat.zero_le _)) ?_
      · obtain ⟨tail, claim⟩ := r
        exact (VerifierProgram.Costs.require (n := 0) _).mono (Nat.zero_le _) fun _ _ ↦ trivial
      all_goals (try simp only [hm, hP, hr3, List.length_replicate])
      all_goals omega
    all_goals (try simp only [hm, hP, hr3])
    all_goals omega
  | level :: next :: rest, index, s, μ, hμ, hH, hD => by
    simp only [whirHeightsLE, Bool.and_eq_true, decide_eq_true_eq] at hH
    rw [queryDepthsLE, Bool.and_eq_true, decide_eq_true_eq] at hD
    simp only [whirCost]
    refine VerifierProgram.Costs.seq (costs_foldRounds level.fold s) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', rounds⟩ := r
    simp only at hr
    have hm : logN - s'.alphas.length = μ - level.fold := by rw [hr]; omega
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.commitP _
        (by rw [hm]; exact hH.1)) (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun _ _ ↦
      VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦
      VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
      VerifierProgram.Costs.seq
        (costs_sampleQueries _ level.queries (by rw [hm]; exact hD.1)) (fun queries hq ↦ ?_)
          ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · have hqm := openCost_mono (height := height) hq
      refine VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun lam _ ↦
        VerifierProgram.Costs.seq (VerifierProgram.Costs.queryP index queries) (fun words _ ↦
          (costs_whirLevels logN laneFolds evaluateBasis (next :: rest) (index + 1) _
            (μ - level.fold) (by rw [glueLevel_alphas]; exact hm) hH.2 hD.2).mono ?_
            fun _ h ↦ h) ?_) ?_
      all_goals (try simp only [hm])
      all_goals omega
    all_goals (try simp only [hm])
    all_goals omega

/-- **WHIR** on a stack whose every ladder costs at most `W`. -/
theorem costs_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E)
    (W : ℕ) (hW : ∀ levels, Whir.ladder logN logInvRate = some levels →
      whirHeightsLE height logN levels = true ∧ queryDepthsLE logN levels = true ∧
        whirCost height logN levels ≤ W) :
    VerifierProgram.Costs height (verifyWhir logN logInvRate target evaluateBasis) W
      fun _ ↦ True :=
  VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun config hc ↦
    (costs_whirLevels logN _ evaluateBasis config 0 _ logN rfl (hW config hc).1
      (hW config hc).2.1).mono (by have := (hW config hc).2.2; omega) fun _ h ↦ h)
    (Nat.zero_le _)

/-- **The stack's commitment**, at a height the ladder bounds. -/
theorem costs_commitStack (logN logInvRate : ℕ)
    (hH : ∀ levels, Whir.ladder logN logInvRate = some levels →
      stackHeightLE height logN levels = true) :
    VerifierProgram.Costs height (commitStack logN logInvRate) 2 fun _ ↦ True := by
  rw [commitStack_eq]
  refine VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun shape hs ↦ ?_) (Nat.zero_le _)
  obtain ⟨level, rest, hl, rfl⟩ := commitShapeOf_spec hs
  have h := hH _ hl
  simp only [stackHeightLE, decide_eq_true_eq] at h
  exact VerifierProgram.Costs.commitP _ h

/-- **The stacked opening**: the batching challenge and WHIR. -/
theorem costs_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (W : ℕ) (hW : ∀ levels, Whir.ladder stackLog logInvRate = some levels →
      whirHeightsLE height stackLog levels = true ∧ queryDepthsLE stackLog levels = true ∧
        whirCost height stackLog levels ≤ W) :
    VerifierProgram.Costs height (verifyStackedOpening stackLog logInvRate claims) (4 + W)
      fun _ ↦ True := by
  rw [verifyStackedOpening_nf]
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
    VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦
      (costs_verifyWhir _ _ _ _ W hW).mono (by omega) fun _ h ↦ h) (by omega)) (Nat.zero_le _)

end Whir

/-! ## Every admissible ladder -/

/-- Over every ladder `Parameters.Whir.ladder` returns, the commitments have height at most
`costHeight`, the query positions at most `64` bits, and the WHIR levels cost at most
`whirBound`; decided over the 60 admissible pairs. -/
theorem ladder_cost (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) :
    whirHeightsLE costHeight μ levels = true ∧ stackHeightLE costHeight μ levels = true ∧
      queryDepthsLE μ levels = true ∧ whirCost costHeight μ levels ≤ whirBound := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (whirHeightsLE costHeight μ levels && stackHeightLE costHeight μ levels &&
            queryDepthsLE μ levels && decide (whirCost costHeight μ levels ≤ whirBound)) =
              true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨hk.1.1.1, hk.1.1.2, hk.1.2, hk.2⟩
  · simp [Whir.ladder, hadm] at h

/-! ## The whole program -/

/-- **The cost of `verify_execution`**, for a check of the fixed polynomial's value that costs
nothing. -/
theorem costs_verifyExecution (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, VerifierProgram.Costs costHeight (ev w p v) 0 fun _ ↦ True)
    (bytecode : List K) (publicInput : Digest) :
    VerifierProgram.Costs costHeight (verifyExecutionClaims ev bytecode publicInput) leanVmCost
      fun _ ↦ True := by
  unfold leanVmCost
  refine VerifierProgram.Costs.seq (costs_readSizes bytecode) (fun p hp ↦ ?_) (by omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, hmax⟩ := hp
  refine VerifierProgram.Costs.seq (costs_commitStack _ _ fun levels h ↦ (ladder_cost _ _ levels
      h).2.1) (fun _ _ ↦ VerifierProgram.Costs.seq (costs_readOod _ hmax) (fun ood _ ↦
    VerifierProgram.Costs.seq (costs_verifyBusBalance_le ev hev hl) (fun bus hbus ↦
        VerifierProgram.Costs.seq
      (costs_tablePhase hl bus hbus) (fun claims hcl ↦ VerifierProgram.Costs.seq
        (costs_publicInputPhase layout publicInput) (fun publicClaims hpc ↦
          VerifierProgram.Costs.seq (costs_keccakPhase layout _ ?_) (fun r _ ↦ ?_) ?_) ?_)
              ?_) ?_) ?_) ?_
  · intro c hc hcol
    rcases List.mem_append.mp hc with hc | hc
    · exact hcl c hc hcol
    · exact hpc c hc hcol
  · obtain ⟨claims', keccakPoint, keccakSlices⟩ := r
    refine VerifierProgram.Costs.seq (costs_ringSwitch keccakPoint keccakSlices) (fun r _ ↦ ?_) ?_
    · obtain ⟨ringTarget, ringWeight⟩ := r
      exact costs_verifyStackedOpening _ _ _ whirBound fun levels h ↦
        ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
          (ladder_cost _ _ levels h).2.2.2⟩
    · omega
  all_goals omega

/-- The deployed check of the fixed polynomial's value costs nothing. -/
theorem costs_computedBytecodeValue (w : List K) (p : List E) (v : E) :
    VerifierProgram.Costs costHeight (computedBytecodeValue w p v) 0 fun _ ↦ True :=
  (VerifierProgram.Costs.require (n := 0) _).mono le_rfl fun _ _ ↦ trivial

/-- The deferring check of the fixed polynomial's value costs nothing. -/
theorem costs_claimedBytecodeValue (claim : BytecodeClaim) (w : List K) (p : List E) (v : E) :
    VerifierProgram.Costs costHeight (claimedBytecodeValue claim w p v) 0 fun _ ↦ True :=
  (VerifierProgram.Costs.require (n := 0) _).mono le_rfl fun _ _ ↦ trivial

/-- **The cost of the leanVM verifier program**: every run of `leanVmVerifierProgram` costs at most
`leanVmCost` quarters, every commitment having height at most `costHeight`, for every bytecode
and public input. -/
theorem costLE_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    (leanVmVerifierProgram bytecode publicInput).CostLE costHeight leanVmCost := by
  rw [leanVmProgram_eq]
  exact VerifierProgram.Costs.seq
    (costs_verifyExecution _ costs_computedBytecodeValue bytecode publicInput) (fun _ _ ↦
      trivial) le_rfl

/-- **The cost of the deferring verifier program**, as the deployed one's. -/
theorem costLE_deferringProgram (claim : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    (deferringVerifierProgram claim bytecode publicInput).CostLE costHeight leanVmCost := by
  rw [deferredProgram_eq]
  exact VerifierProgram.Costs.seq
    (costs_verifyExecution _ (costs_claimedBytecodeValue claim) bytecode publicInput) (fun _ _ ↦
      trivial) le_rfl

/-! ## The seed and the query bound -/

/-- **The leanVM seeding**: the IV, the hash of the version tag and the bytecode, then the
permutation of the IV and the public input (`spongeSeedWith`). -/
def leanVmSeed (bytecode : List K) (publicInput : Digest) : Seed where
  hs := [fun _ ↦ versionTag ++ bytecode.flatMap K.toBytes]
  fin ds := seedInput (ds.getD 0 default) publicInput

/-- The seeding computes `spongeSeedWith`, with any hash and permutation in any lawful monad. -/
theorem seedRun_leanVmSeed {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) (bytecode : List K) (publicInput : Digest) :
    (leanVmSeed bytecode publicInput).run H F = seedWithHash H F bytecode publicInput := by
  simp [Seed.run, Seed.hsRun, leanVmSeed, seedWithHash, fiatShamirIvWithHash]

/-- The seeded verifier of the random-oracle theorem at the leanVM seed and program is the
compiled leanVM verifier with the hash and the permutation queries. -/
theorem verifierComp_leanVm (bytecode : List K) (publicInput : Digest) (π : Proof) :
    verifierComp (leanVmSeed bytecode publicInput) (leanVmVerifierProgram bytecode publicInput) π =
      verifyWithHash callKeccak256 callKeccakF1600 bytecode publicInput π := by
  simp only [verifierComp, Rom.verify, verifyWithHash, seedRun_leanVmSeed]

/-- **The query bound of the leanVM verifier**: the IV's hash, the seed's permutation, and the
program's cost in quarters. -/
def leanVmQueryBound : ℕ := 1 + 1 + leanVmCost / 4

/-- The bound, evaluated. -/
theorem leanVmQueryBound_eq : leanVmQueryBound = 13708 := by decide

/-- **The compiled leanVM verifier makes at most `leanVmQueryBound = 13708` queries** to the random
oracles on every proof, for every bytecode and public input: the hypothesis `hV` of `romSound`
at the leanVM program and seed. -/
theorem isTotalQueryBound_leanVm (bytecode : List K) (publicInput : Digest) (π : Proof) :
    IsTotalQueryBound
      (verifierComp (leanVmSeed bytecode publicInput) (leanVmVerifierProgram bytecode
          publicInput) π)
      leanVmQueryBound :=
  isTotalQueryBound_verifierComp (costLE_leanVmProgram bytecode publicInput) _ π

end
end LeanVM.Protocol.Verifier
