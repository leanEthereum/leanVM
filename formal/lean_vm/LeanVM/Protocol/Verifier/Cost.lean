/-
  LeanVM.Protocol.Verifier.Cost

  The query cost of leanVM's verifier program: per-phase cost bounds, an explicit bound over every
  announced size the verifier accepts, the Fiat-Shamir seed as a seeding, and the total query
  bound of the compiled verifier against the random oracles that `romSound` asks for.
-/

module

public import Statement.Verifier.Lib
public import LeanVM.Protocol.Compile.Cost
public import LeanVM.Protocol.WithHash

/-!
# The query cost of the leanVM verifier

`leanVmVerifierProgram bytecode publicInput` is costed in the calculus of
`LeanVM.Protocol.Compile.Cost`, phase by phase, in quarters of a query: a scalar read costs `1`
(the sponge permutes once per four absorptions), a challenge `4` (one permutation), a proof of
work `5` (charged even where it grinds nothing), a commitment `2`, an opening of `k` positions
`4 · k · (1 + height)` (one hash per leaf and per level), a packed message of `n` scalars
`readPackedCost n` and a packed draw of `n` challenges `samplePackedCost n`. A run that is not
rejected has sizes inside the window `buildLayout` and the program check: tables of at most
`2^30` rows (`maxTableLog`), a stack of `16 ≤ μ ≤ 30` variables, a rate exponent `1 ≤ R ≤ 4`,
the WHIR ladder `Whir.ladder μ R`, a pointer width of at most `24` (`Chunks.new`). The cost is
maximised over that window:

* the sizes (`readAnnouncedSizes`): `2 + nTables = 8` reads;
* the stack's root (`commitStack`): one commitment, `2`, and its out-of-domain sample
  (`readOod`): a proof of work, at most `30` challenges and a read;
* the link (`verifyLink`): a proof of work, `θ_0`, the packed draw of at most `151` challenges,
  the index sum-check over at most `24` coordinates, `m_1`, the five fresh coefficients, the row
  sum-check over at most `30` rows of at most `12` coefficients, the pointer columns' sum-check
  over `6` variables of at most `11`, and the packed message of the values and the `64`
  bit-slices (`linkCost`);
* the public input: one challenge (the prover sends nothing);
* `KECCAK`'s reduction (`keccakValidity`) at a point of at most `27` coordinates after the
  instances: `keccakCost 27`;
* ring switching: a proof of work and a packed draw of at most `18` challenges;
* the stacked opening: the WHIR levels (`whirCost`), at most `whirBound` over the `60`
  admissible ladders (`ladder_cost`, decided), every commitment of height at most
  `costHeight = 28`.

In total `leanVmCost` quarters (`costLE_leanVmProgram`). The seed is one hash and one permutation
(`leanVmSeed`, `seedRun_leanVmSeed`), so the compiled verifier makes at most
`leanVmQueryBound = 1 + 1 + leanVmCost / 4` queries on every proof (`isTotalQueryBound_leanVm`),
evaluated in `leanVmQueryBound_eq` (`12672`), and `leanVmQueryBound + 3 ≤ 2^14`
(`leanVmQueryBound_add_three_le`). The bound is crude where a tight one would cost proof without
changing the soundness bound, in which it enters linearly: the WHIR query positions are charged at
the largest height rather than at their level's, a sample right after a proof of work, which
permutes nothing, is charged a permutation, and the link's sizes are bounded by the window.
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

/-- The cost of ring switching: a proof of work and a packed draw of at most `2·8 + 1 + 1`. -/
def ringCost : ℕ := 5 + VerifierProgram.samplePackedCost (2 * ringMapWidth + 2)

/-- The values the link reads at its row point: every table's columns but its pointers. -/
def linkValues (tables : List Table) : ℕ :=
  (tables.zipIdx.map fun (table, t) ↦ ((List.range table.width).filter fun c ↦
    !((tables.map (·.links.pointers)).getD t []).contains c).length).sum

/-- The cost of the link at the window's largest sizes: a proof of work, `θ_0`, the packed draw
(`packedChallenges` at `30` rows, a width of `24` and `9` chunks), the index sum-check over `24`
coordinates, `m_1`, the five fresh coefficients, `30` row rounds of at most `12` coefficients, the
pointer columns' rounds of at most `11`, and the packed message of the values and the
bit-slices. -/
def linkCost : ℕ :=
  5 + 4 + VerifierProgram.samplePackedCost (packedChallenges tables 30 24 + 9) + 24 * roundCost 3 +
    1 + VerifierProgram.samplePackedCost 5 + 30 * roundCost 12 +
    6 * roundCost 11 +
    VerifierProgram.readPackedCost (linkValues tables + kBits)

/-- **The cost of the leanVM verifier program**, phase by phase, in quarters of a query. -/
def leanVmCost : ℕ :=
  (2 + nTables) + 2 + oodCost + linkCost + 4 + keccakCost 27 + ringCost + whirBound

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

/-- A sumcheck of at most `k` rounds of at most `c` coefficients costs at most
`k · roundCost c`. -/
theorem costs_sumcheck_le (count : ℕ) (claim : E) (eqs : List (Option E)) {k c : ℕ}
    (hk : eqs.length ≤ k) (hc : count ≤ c) :
    VerifierProgram.Costs height (sumcheck claim count eqs) (k * roundCost c)
      fun r ↦ r.1.length = eqs.length :=
  (costs_sumcheck count claim eqs).mono
    (Nat.mul_le_mul hk (by unfold roundCost; omega)) fun _ h ↦ h

theorem samplePackedCost_mono {a b : ℕ} (h : a ≤ b) :
    VerifierProgram.samplePackedCost a ≤ VerifierProgram.samplePackedCost b := by
  unfold VerifierProgram.samplePackedCost; omega

theorem readPackedCost_mono {a b : ℕ} (h : a ≤ b) :
    VerifierProgram.readPackedCost a ≤ VerifierProgram.readPackedCost b := by
  unfold VerifierProgram.readPackedCost; omega

/-- A packed draw of at most `b` challenges. -/
theorem costs_samplePacked_le (n : ℕ) {b : ℕ} (h : n ≤ b) :
    VerifierProgram.Costs height (VerifierProgram.sampleChallengesPacked n)
      (VerifierProgram.samplePackedCost b) fun _ ↦ True :=
  (VerifierProgram.Costs.samplePackedE n).mono (samplePackedCost_mono h) fun _ h ↦ h

/-- A packed message of at most `b` scalars. -/
theorem costs_readPacked_le (n : ℕ) {b : ℕ} (h : n ≤ b) :
    VerifierProgram.Costs height (VerifierProgram.readScalarsPacked n)
      (VerifierProgram.readPackedCost b) fun _ ↦ True :=
  (VerifierProgram.Costs.readPackedE n).mono (readPackedCost_mono h) fun _ h ↦ h

end Phases

/-! ## The announced sizes -/

/-- What `buildLayout` guarantees of a layout it returns. -/
structure LayoutBounds (layout : Layout) : Prop where
  /-- The deployed tables. -/
  tables_eq : layout.tables = tables
  /-- Every table has at most `2^30` rows. -/
  heights_le : ∀ h ∈ layout.tableLogHeights, h ≤ 30

/-- `log2Ceil v ≤ k` when `v ≤ 2^k`. -/
theorem log2Ceil_le {v k : ℕ} (h : v ≤ 2 ^ k) : log2Ceil v ≤ k := by
  unfold log2Ceil bitLength
  split
  · exact Nat.zero_le _
  · rename_i hv
    have := (Nat.log2_lt hv).mpr (by omega : v - 1 < 2 ^ k)
    omega

/-- A layout `buildLayout` returns is within its bounds. -/
theorem layoutBounds_of_buildLayout {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    LayoutBounds layout := by
  unfold buildLayout at h
  split at h
  · simp at h
  · split_ifs at h with hc
    obtain ⟨-, -, hall, -, -, -⟩ := hc
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_⟩
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    intro x hx
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hx
    simp only [List.getElem_zipWith] at hx
    rw [← hx]
    have hi1 : i < tableRows.length := by simp at hi; omega
    have hi2 : i < tableLogFloors.length := by simp at hi; omega
    refine max_le (log2Ceil_le (hall _ (List.getElem_mem hi1))) ?_
    have : ∀ f ∈ tableLogFloors, f ≤ 30 := by decide
    exact this _ (List.getElem_mem hi2)

/-- The sizes a run of `readAnnouncedSizes` returns: a layout `buildLayout` built, the stack in the
window, the rate exponent in `1..4`. -/
def SizesOK (p : Layout × ℕ) : Prop :=
  LayoutBounds p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 4 ∧ Whir.minLogStack ≤ p.1.stackLog ∧
    p.1.stackLog ≤ Whir.maxLogStack

/-- The announced sizes: `2 + nTables` reads, and sizes in the window the program checks. -/
theorem costs_readSizes {height : ℕ} (bytecode : List K) :
    VerifierProgram.Costs height (readAnnouncedSizes bytecode) (2 + nTables) SizesOK := by
  unfold readAnnouncedSizes
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun _ _ ↦ ?_) le_rfl
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ ?_)
    (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ hr ↦ ?_)
    (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun layout hl ↦ ?_) (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ hs ↦ ?_)
    (Nat.zero_le _)
  exact (show SizesOK _ from ⟨layoutBounds_of_buildLayout hl, hr.1, hr.2, hs.1, hs.2⟩)

/-! ## The phases -/

section Phases2

variable {height : ℕ}

/-- **The stack's out-of-domain sample**, on a stack of at most `30` variables. -/
theorem costs_readOod (stackLog : ℕ) (h : stackLog ≤ Whir.maxLogStack) :
    VerifierProgram.Costs height (readOod stackLog) oodCost fun _ ↦ True := by
  unfold readOod
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun _ _ ↦
      VerifierProgram.Costs.seq VerifierProgram.Costs.readE
        (fun _ _ ↦ trivial) (by unfold oodCost; omega)) (by unfold oodCost; omega))
    (by unfold oodCost; omega)

/-- **The public input**: one challenge. -/
theorem costs_bindPublicInput (layout : Layout) (publicInput : Digest) :
    VerifierProgram.Costs height (bindPublicInput layout publicInput) 4 fun _ ↦ True := by
  unfold bindPublicInput
  exact VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦
    VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun _ _ ↦ trivial) (Nat.zero_le _)) le_rfl

/-- **Ring switching**: a proof of work and a packed draw of at most `18` challenges. -/
theorem costs_ringSwitch (claims : List RingClaim) :
    VerifierProgram.Costs height (ringSwitch claims) ringCost fun _ ↦ True := by
  unfold ringSwitch
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦
    VerifierProgram.Costs.seq (costs_samplePacked_le _ (b := 2 * ringMapWidth + 2)
      (by split <;> omega)) (fun _ _ ↦ trivial) (by unfold ringCost; omega))
    (by unfold ringCost; omega)

/-- The memory term costs nothing. -/
theorem costs_memoryTermClaim (layout : Layout) (link : LinkEnd) :
    VerifierProgram.Costs height (memoryTermClaim layout link) 0 fun _ ↦ True := by
  unfold memoryTermClaim
  exact VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun _ _ ↦
    VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun _ _ ↦ trivial) le_rfl) le_rfl

end Phases2

/-! ## The link -/

/-- The chunks of a width `Chunks.new` accepts: at most `24` bits in at most `9` chunks. -/
theorem chunks_bounds {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : c.width ≤ 24 ∧ c.d ≤ 9 := by
  have key : ∀ w < 25, ∀ c, Chunks.new w = some c → c.width ≤ 24 ∧ c.d ≤ 9 := by decide +kernel
  by_cases hw : w < 25
  · exact key w hw c h
  · unfold Chunks.new at h
    split_ifs at h with hc
    · exact absurd hc.2 (by simp [maxPointerWidth]; omega)

theorem chunks_width {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : c.width = w := by
  unfold Chunks.new at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  rw [← h]

theorem foldl_max_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) : l.foldl max 0 ≤ b := by
  suffices ∀ a ≤ b, l.foldl max a ≤ b from this 0 (Nat.zero_le _)
  induction l with
  | nil => intro a ha; exact ha
  | cons x xs ih =>
    intro a ha
    exact ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) _
      (max_le ha (h x List.mem_cons_self))

/-- The link's packed draw at a built layout's sizes is at most the window's. -/
theorem packedChallenges_le {w nRows : ℕ} {c : Chunks} (h : Chunks.new w = some c)
    (hrows : nRows ≤ 30) : packedChallenges tables nRows c.width ≤ packedChallenges tables 30 24 + 9 := by
  have hw := chunks_width h
  obtain ⟨hw24, hd⟩ := chunks_bounds h
  have hc : Chunks.new c.width = some c := by rw [hw]; exact h
  unfold packedChallenges
  simp only [hc, Option.map_some, Option.getD_some]
  omega

/-- **The link** on a built layout, for a split that costs nothing. -/
theorem costs_verifyLink {height : ℕ}
    {bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split}
    (hsplit : ∀ b p pc, VerifierProgram.Costs height (bytecodeSplit b p pc) 0 fun _ ↦ True)
    {layout : Layout} (hl : LayoutBounds layout) :
    VerifierProgram.Costs height (verifyLink bytecodeSplit layout) linkCost fun _ ↦ True := by
  unfold verifyLink
  rw [hl.tables_eq]
  refine VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun chunks hch ↦ ?_) (Nat.zero_le _)
  obtain ⟨hw, hd⟩ := chunks_bounds hch
  have hrows : layout.tableLogHeights.foldl max 0 ≤ 30 := foldl_max_le hl.heights_le
  have hN : packedChallenges tables (layout.tableLogHeights.foldl max 0) chunks.width ≤
      packedChallenges tables 30 24 + 9 := packedChallenges_le hch hrows
  dsimp only
  have hr3 : roundCost 3 = 11 := rfl
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦ ?_)
    (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦ ?_)
    (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq (costs_samplePacked_le _ hN) (fun drawn _ ↦ ?_)
    (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq (costs_sumcheck_le 3 _ _ (k := 24) (c := 3)
    (by simp only [List.length_replicate]; omega) le_rfl) (fun r _ ↦ ?_) (by unfold linkCost; omega)
  obtain ⟨r, claim⟩ := r
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun m1 _ ↦ ?_)
    (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.samplePackedE 5) (fun fresh _ ↦ ?_)
    (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq (hsplit _ _ _) (fun split _ ↦ ?_) (Nat.zero_le _)
  have hrc : (roundCoefficients chunks.d).1 ≤ 12 := by simp only [roundCoefficients]; omega
  have hcc : (roundCoefficients chunks.d).2 ≤ 11 := by simp only [roundCoefficients]; omega
  refine VerifierProgram.Costs.seq (costs_sumcheck_le _ _ _ (k := 30) (c := 12)
    (by simp only [List.length_replicate]; omega) hrc) (fun r2 _ ↦ ?_) (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq (costs_sumcheck_le _ _ _ (k := 6) (c := 11)
    (by simp only [List.length_replicate]; decide) hcc) (fun r3 _ ↦ ?_) (by unfold linkCost; omega)
  refine VerifierProgram.Costs.seq (costs_readPacked_le _ (b := linkValues tables + kBits)
    (by decide)) (fun message _ ↦ ?_) (by unfold linkCost; omega)
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ trivial)
    (Nat.zero_le _)

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
      all_goals simp only [hm, hP, hr3, List.length_replicate]
      all_goals omega
    all_goals simp only [hm, hP, hr3]
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
      all_goals simp only [hm]
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
  unfold commitStack
  refine VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun config hc ↦ ?_) (Nat.zero_le _)
  have h := hH _ hc
  rcases config with _ | ⟨level, rest⟩
  · trivial
  · simp only [stackHeightLE, decide_eq_true_eq] at h
    exact VerifierProgram.Costs.commitP _ (by simpa [levelShape] using h)

/-- **The stacked opening**: WHIR on the batched claims. -/
theorem costs_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (batching : E) (W : ℕ) (hW : ∀ levels, Whir.ladder stackLog logInvRate = some levels →
      whirHeightsLE height stackLog levels = true ∧ queryDepthsLE stackLog levels = true ∧
        whirCost height stackLog levels ≤ W) :
    VerifierProgram.Costs height (verifyStackedOpening stackLog logInvRate claims batching) W
      fun _ ↦ True := by
  unfold verifyStackedOpening
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦
    (costs_verifyWhir _ _ _ _ W hW).mono (by omega) fun _ h ↦ h) (Nat.zero_le _)

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

/-! ## The Keccak reduction -/

section Keccak

variable {height : ℕ}

/-- One layer of the Keccak reduction keeps the claim's point length. -/
theorem costs_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    VerifierProgram.Costs height (verifyKeccakLayer logSteps step claim)
      (keccakLayerCost claim.point.length) fun c ↦ c.point.length = claim.point.length := by
  have hr4 : roundCost 4 = 12 := rfl
  have hr3 : roundCost 3 = 11 := rfl
  unfold verifyKeccakLayer
  dsimp only
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN _) (fun _ _ ↦ ?_)
    (by unfold keccakLayerCost; omega)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ ?_)
    (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦ ?_)
    (by unfold keccakLayerCost; omega)
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦ ?_)
    (by unfold keccakLayerCost; omega)
  refine VerifierProgram.Costs.seq (costs_sumcheck 3 _ _) (fun r hr ↦ ?_)
    (by simp only [keccakLayerCost, List.length_map, hr3]; omega)
  obtain ⟨point, value⟩ := r
  refine VerifierProgram.Costs.seq (costs_sumcheck 4 _ _) (fun r' _ ↦ ?_)
    (by simp only [keccakLayerCost, List.length_replicate, List.length_map, hr3, hr4]; omega)
  obtain ⟨localPoint, value'⟩ := r'
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN 3) (fun _ _ ↦ ?_)
    (by simp only [keccakLayerCost, List.length_replicate, List.length_map, hr3, hr4]; omega)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ ?_)
    (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦ ?_)
    (by simp only [keccakLayerCost, List.length_replicate, List.length_map, hr3, hr4]; omega)
  refine VerifierProgram.Costs.seq VerifierProgram.Costs.sampleE (fun _ _ ↦ ?_)
    (by simp only [keccakLayerCost, List.length_replicate, List.length_map, hr3, hr4]; omega)
  show point.length = claim.point.length
  simpa using hr

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

/-- **The Keccak reduction** at most `30` instance coordinates. -/
theorem costs_verifyKeccak (logSteps : ℕ) (inst output : List E) (hl : logSteps ≤ 30) :
    VerifierProgram.Costs height (verifyKeccak logSteps inst output) (keccakCost 27) fun _ ↦
        True := by
  have h1 : 1 < keccakSegments := by decide
  have hseg : keccakSegmentBits = 1 := by decide
  have hr3 : roundCost 3 = 11 := rfl
  unfold verifyKeccak
  dsimp only
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ hsh ↦ ?_)
    (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.grindP _) (fun _ _ ↦ ?_)
    (by unfold keccakCost; omega)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun segment hs ↦ ?_)
    (by unfold keccakCost; omega)
  refine VerifierProgram.Costs.seq (VerifierProgram.Costs.sampleN _) (fun _ _ ↦ ?_)
    (by unfold keccakCost; omega)
  split
  · have hL : (inst.drop 4 ++ segment).length ≤ 27 := by
      simp only [List.length_append, List.length_drop, hs, hsh.1, hseg]; omega
    have hlay : keccakDepth * keccakLayerCost (inst.drop 4 ++ segment).length ≤
        keccakDepth * keccakLayerCost 27 := by
      refine Nat.mul_le_mul_left _ ?_
      unfold keccakLayerCost
      have := Nat.mul_le_mul_right (roundCost 3) hL
      omega
    refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun committed _ ↦ ?_)
      (by unfold keccakCost; omega)
    refine VerifierProgram.Costs.seq (costs_keccakLayers logSteps (List.range keccakDepth) _)
      (fun claim _ ↦ ?_) (by simp only [keccakCost, keccakFirstClaim, List.length_range] at hlay ⊢; omega)
    refine VerifierProgram.Costs.seq (costs_keccakOpen logSteps _ 1 _ _) (fun _ _ ↦ ?_)
      (by simp only [keccakCost, keccakFirstClaim, List.length_range] at hlay ⊢; omega)
    refine VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦ ?_)
      (by simp only [keccakCost, keccakFirstClaim, List.length_range] at hlay ⊢; omega)
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ ?_)
      (Nat.zero_le _)
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.pure0 _) (fun _ _ ↦ ?_)
      (Nat.zero_le _)
    refine VerifierProgram.Costs.seq (costs_sumcheck 3 _ _) (fun _ _ ↦ ?_)
      (by simp only [keccakCost, keccakFirstClaim, List.length_range, List.length_replicate,
        hr3] at hlay ⊢; omega)
    refine VerifierProgram.Costs.seq (costs_keccakOpen logSteps _ 0 _ _) (fun _ _ ↦ ?_)
      (by simp only [keccakCost, keccakFirstClaim, List.length_range, List.length_replicate,
        hr3] at hlay ⊢; omega)
    refine VerifierProgram.Costs.seq (VerifierProgram.Costs.readN kBits) (fun _ _ ↦ ?_)
      (by simp only [keccakCost, keccakFirstClaim, List.length_range, List.length_replicate,
        hr3] at hlay ⊢; omega)
    exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ trivial)
      (Nat.zero_le _)
  · exact absurd h1 ‹_›

/-- **`KECCAK`'s validity** on a built layout. -/
theorem costs_keccakValidity {layout : Layout} (hl : LayoutBounds layout) (link : LinkEnd) :
    VerifierProgram.Costs height (keccakValidity layout link) (keccakCost 27) fun _ ↦ True := by
  have hsteps : layout.tableLogHeights.getD opKeccak 0 ≤ 30 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : layout.tableLogHeights[opKeccak]? with
    | none => simp
    | some x => exact hl.heights_le x (List.mem_of_getElem? h)
  unfold keccakValidity
  split
  exact VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun _ _ ↦
    costs_verifyKeccak _ _ _ hsteps) (Nat.zero_le _)

end Keccak

/-! ## The whole program -/

/-- **The cost of `verify_execution`**, for a split that costs nothing. -/
theorem costs_verifyExecution
    {bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split}
    (hsplit : ∀ b p pc, VerifierProgram.Costs costHeight (bytecodeSplit b p pc) 0 fun _ ↦ True)
    (bytecode : List K) (publicInput : Digest) :
    VerifierProgram.Costs costHeight (verifyExecution bytecodeSplit bytecode publicInput)
      leanVmCost fun _ ↦ True := by
  unfold verifyExecution
  refine VerifierProgram.Costs.seq (costs_readSizes bytecode) (fun p hp ↦ ?_)
    (by unfold leanVmCost; omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, hmax⟩ := hp
  refine VerifierProgram.Costs.seq (costs_commitStack _ _ fun levels h ↦
    (ladder_cost _ _ levels h).2.1) (fun _ _ ↦ ?_) (by unfold leanVmCost; omega)
  refine VerifierProgram.Costs.seq (costs_readOod _ hmax) (fun ood _ ↦ ?_)
    (by unfold leanVmCost; omega)
  refine VerifierProgram.Costs.seq (costs_verifyLink hsplit hl) (fun link _ ↦ ?_)
    (by unfold leanVmCost; omega)
  refine VerifierProgram.Costs.seq (costs_bindPublicInput _ _) (fun _ _ ↦ ?_)
    (by unfold leanVmCost; omega)
  refine VerifierProgram.Costs.seq (costs_keccakValidity hl link) (fun r _ ↦ ?_)
    (by unfold leanVmCost; omega)
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := r
  refine VerifierProgram.Costs.seq (costs_liftOption _ 0) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine VerifierProgram.Costs.seq (costs_ringSwitch _) (fun r _ ↦ ?_)
    (by unfold leanVmCost; omega)
  obtain ⟨ring, batching⟩ := r
  refine VerifierProgram.Costs.seq (costs_memoryTermClaim _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  exact (costs_verifyStackedOpening _ _ _ _ whirBound fun levels h ↦
    ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
      (ladder_cost _ _ levels h).2.2.2⟩).mono (by unfold leanVmCost; omega) fun _ h ↦ h

theorem costs_computedSplit (b : List K) (p : List E) (pc : List (ℕ × ℕ)) :
    VerifierProgram.Costs costHeight (computedSplit b p pc) 0 fun _ ↦ True := by
  unfold computedSplit
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ trivial)
    le_rfl

theorem costs_freshSplit (fresh : FreshClaim) (b : List K) (p : List E) (pc : List (ℕ × ℕ)) :
    VerifierProgram.Costs costHeight (freshSplit fresh b p pc) 0 fun _ ↦ True := by
  unfold freshSplit
  exact VerifierProgram.Costs.seq (VerifierProgram.Costs.require (n := 0) _) (fun _ _ ↦ trivial)
    le_rfl

/-- **The cost of the leanVM verifier program**: every run of `leanVmVerifierProgram` costs at most
`leanVmCost` quarters, every commitment having height at most `costHeight`, for every bytecode
and public input. -/
theorem costLE_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    (leanVmVerifierProgram bytecode publicInput).CostLE costHeight leanVmCost := by
  unfold leanVmVerifierProgram
  exact VerifierProgram.Costs.seq (costs_verifyExecution costs_computedSplit bytecode publicInput)
    (fun _ _ ↦ trivial) le_rfl

/-- **The cost of the deferring verifier program**, as the deployed one's. -/
theorem costLE_deferringProgram (fresh : FreshClaim) (bytecode : List K) (publicInput : Digest) :
    (deferringVerifierProgram fresh bytecode publicInput).CostLE costHeight leanVmCost := by
  unfold deferringVerifierProgram
  exact VerifierProgram.Costs.seq
    (costs_verifyExecution (costs_freshSplit fresh) bytecode publicInput) (fun _ _ ↦ trivial)
    le_rfl

/-! ## The seed and the query bound -/

/-- **The leanVM seeding**: the IV, the hash of the version tag and the bytecode, then the
permutation of the IV and the public input (`seedWithHash`). -/
def leanVmSeed (bytecode : List K) (publicInput : Digest) : Seed where
  hs := [fun _ ↦ versionTag ++ bytecode.flatMap K.toBytes]
  fin ds := seedInput (ds.getD 0 default) publicInput

/-- The seeding computes `seedWithHash`, with any hash and permutation in any lawful monad. -/
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
theorem leanVmQueryBound_eq : leanVmQueryBound = 12672 := by decide

/-- The bound with the end statement's margin: `leanVmQueryBound + 3 ≤ 2^14`. -/
theorem leanVmQueryBound_add_three_le : leanVmQueryBound + 3 ≤ 2 ^ 14 := by
  rw [leanVmQueryBound_eq]; norm_num

/-- **The compiled leanVM verifier makes at most `leanVmQueryBound` queries** to the random
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
