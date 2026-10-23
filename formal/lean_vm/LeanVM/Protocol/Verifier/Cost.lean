/-
  LeanVM.Protocol.Verifier.Cost

  The query cost of leanVM's verifier program: per-phase cost bounds, an explicit bound over every
  announced size the verifier accepts, the Fiat-Shamir seed as a seeding chain, and the total
  query bound of the compiled verifier against the random oracle that `romSound` asks for.
-/

module

public import LeanVM.Protocol.Compile.Cost
public import LeanVM.Protocol.Verifier

/-!
# The query cost of the leanVM verifier

`leanVmProgram bytecode publicInput` (`LeanVM.Protocol.Verifier`) is costed in the
calculus of `LeanVM.Protocol.Compile.Cost`, phase by phase. A run's shape depends on the sizes
the proof announces, but a run that is not rejected has sizes inside the window the program
checks: memory and table log-heights at most `32`, a bytecode of at most `2^36` words, a stack
of `15 ≤ μ ≤ 28` variables, a rate exponent `1 ≤ R ≤ 4`, and the WHIR ladder
`Parameters.Whir.ladder μ R`. The cost is maximised over that window:

* the sizes (`readSizes`): `8` reads;
* the stack's root (`commitStack`): one commitment, `2`;
* the bus (`verifyBusBalance`): `12` plus the GKR walk over the push side's depth, which is at
  most `38` (`3 + 34` blocks of at most `2^32` rows), `gkrCost 38 0 = 1995`;
* the table sumcheck (`tablePhase`): `1 + 4 · 32 + 6 · 37` (every table at most `37` wide);
* the public input: `1`, its challenge (the prover sends nothing);
* Flock at `14 + h` variables, `h ≤ 32` the `BLAKE2S` table's log-height: `4 · 33 + 177`;
* ring switching: `6` samples;
* the stacked opening: `3` plus the WHIR levels (`whirCost`), at most `whirBound = 10523` over
  the 56 admissible ladders (`ladder_cost`, decided; the query counts of `verifier.py:912` at
  leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`), every commitment of height at most
  `costHeight = 26`. Both are attained, at `μ = 28` and rates `1` and `4`.

In total `leanVmCost = 13210` (`costLE_leanVmProgram`). The seed of `seedWith` is three hashes
(`leanVmSeed`, `seedRun_leanVmSeed`), so the compiled verifier makes at most
`leanVmQueryBound = 13213` queries on every proof (`isTotalQueryBound_leanVm`). The bound is
crude where a tight one would cost proof without changing the soundness bound, in which it
enters linearly: the table widths, the depth of the bus, the Flock size, and the WHIR query
positions, charged at the largest height rather than at their level's.

## Deployed behaviour

The bound is a statement on the program `leanVmProgram` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, as transcribed in `LeanVM.Protocol.Verifier`;
it covers every proof, accepted or not.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Blake2sHash
open OracleComp OracleSpec

@[expose] public section

/-! ## Cost functions -/

/-- The cost of one GKR step of `step` levels at a point of `L` coordinates: the combiner, the
sumcheck's `L` rounds, the three trees' children and the new coordinates. -/
def gkrStepCost (step L : ℕ) : ℕ := L * max (2 ^ step + 1) 2 + 3 * 2 ^ step + step + 1

/-- The cost of the GKR walk over `n` remaining levels from a point of `L` coordinates, following
`gkrLayers`. -/
def gkrCost : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, L => gkrStepCost 1 L + gkrCost 0 (1 + L)
  | n + 2, L =>
    if n % 2 = 1 then gkrStepCost 1 L + gkrCost (n + 1) (1 + L)
    else gkrStepCost 2 L + gkrCost n (2 + L)

/-- The cost of the WHIR levels from a message of `μ` variables, following `whirLevels`: per
level its folds, the residual or the next commitment with its out-of-domain claim, the proof of
work, the query positions and their openings at `height`, the batching challenge and the
enforced claim, and on the final level the tail rounds. -/
def whirCost (height : ℕ) : ℕ → List Whir.Level → ℕ
  | _, [] => 0
  | μ, [level] =>
    3 * level.fold + 2 ^ (μ - level.fold) + level.queries * (2 + height) + 6 +
      3 * (μ - level.fold)
  | μ, level :: next :: rest =>
    3 * level.fold + (5 + (μ - level.fold)) + level.queries * (2 + height) + 6 +
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

/-- The bound on every commitment's height. -/
def costHeight : ℕ := 26

/-- The bound on the WHIR levels' cost over every admissible ladder, attained at `μ = 28`,
rate `1` (queries `(225, 56, 32, 23, 18, 14)`). -/
def whirBound : ℕ := 10523

/-- The bound on the GKR walk: the push side's depth is at most `38`. -/
def gkrBound : ℕ := 1995

/-- The bound on the Flock reduction: at most `33` sampled coordinates. -/
def flockBound : ℕ := 4 * 33 + 177

/-- **The cost of the leanVM verifier program**, phase by phase. -/
def leanVmCost : ℕ :=
  8 + 2 + (busBits + 1 + (2 + gkrBound) + 5) + (1 + 32 * 4 + 6 * 37) + 1 + flockBound + 6 +
    (1 + 2 + whirBound)

/-! ## Sumcheck rounds -/

section Phases

variable {height : ℕ}

/-- A pure step that may fail costs nothing, and returns what the option holds. -/
theorem costs_liftOption {α : Type} (o : Option α) (n : ℕ) :
    Prog.Costs height (liftOption o) n fun a ↦ o = some a := by
  cases o
  · trivial
  · rfl

/-- A round polynomial of `count` coefficients reads `count - 1` of them (at least one). -/
theorem costs_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    Prog.Costs height (sumcheckRoundPoly count claim eq) (max count 2 - 1) fun _ ↦ True := by
  cases eq with
  | none =>
    refine Prog.Costs.seq Prog.Costs.readE (fun _ _ ↦ Prog.Costs.seq (Prog.Costs.readN _)
      (fun _ _ ↦ trivial) ?_) ?_ <;> omega
  | some r =>
    exact Prog.Costs.seq (Prog.Costs.readN _) (fun _ _ ↦ trivial) (by omega)

/-- A sumcheck of `k` rounds costs `k · max count 2`, and returns `k` challenges. -/
theorem costs_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    Prog.Costs height (sumcheck claim count eqs) (eqs.length * max count 2)
      fun r ↦ r.1.length = eqs.length
  | _, [] => rfl
  | claim, e :: es => by
    refine Prog.Costs.seq (costs_sumcheckRoundPoly count claim e) (fun msg _ ↦
      Prog.Costs.seq Prog.Costs.sampleE (fun c _ ↦
        Prog.Costs.seq (costs_sumcheck count _ es) (fun r hr ↦ ?_) ?_) ?_) ?_
    · obtain ⟨point, final⟩ := r
      show (c :: point).length = (e :: es).length
      simpa using hr
    all_goals simp only [List.length_cons, Nat.succ_mul]; omega

/-! ## The bus -/

theorem costs_gkrStep (step : ℕ) (s : GkrState) :
    Prog.Costs height (gkrStep step s) (gkrStepCost step s.point.length)
      fun t ↦ t.point.length = step + s.point.length := by
  refine Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦
    Prog.Costs.seq (costs_sumcheck _ _ (s.point.map some)) (fun r hr ↦ ?_) ?_) ?_
  · obtain ⟨x, claim⟩ := r
    refine Prog.Costs.seq (Prog.Costs.readN _) (fun c0 _ ↦ Prog.Costs.seq (Prog.Costs.readN _)
      (fun c1 _ ↦ Prog.Costs.seq (Prog.Costs.readN _) (fun c2 _ ↦
        Prog.Costs.seq (Prog.Costs.require (n := 0) _) (fun _ _ ↦
          Prog.Costs.seq (Prog.Costs.sampleN step) (fun y hy ↦ ?_) ?_) ?_) ?_) ?_) ?_
    · show (y ++ x).length = step + s.point.length
      simp only [List.length_map] at hr
      simp [hy, hr]
    all_goals simp only [gkrStepCost, List.length_map]; omega
  all_goals simp only [gkrStepCost, List.length_map]; omega

/-- The GKR walk costs `gkrCost`. -/
theorem costs_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    Prog.Costs height (gkrLayers n s) (gkrCost n s.point.length) fun _ ↦ True
  | 0, _ => trivial
  | 1, s => by
    refine Prog.Costs.seq (costs_gkrStep 1 s) (fun t ht ↦
      (costs_gkrLayers 0 t).mono (by simp [gkrCost]) fun _ h ↦ h) ?_
    simp only [gkrCost]; omega
  | n + 2, s => by
    simp only [gkrLayers, gkrCost]
    split
    · refine Prog.Costs.seq (costs_gkrStep 1 s) (fun t ht ↦
        (costs_gkrLayers (n + 1) t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)
    · refine Prog.Costs.seq (costs_gkrStep 2 s) (fun t ht ↦
        (costs_gkrLayers n t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)

/-- The GKR grand products: the two roots and the walk. -/
theorem costs_verifyGkrGrandProducts (depth : ℕ) :
    Prog.Costs height (verifyGkrGrandProducts depth) (2 + gkrCost depth 0) fun _ ↦ True := by
  refine Prog.Costs.seq Prog.Costs.readE (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE
    (fun _ _ ↦ Prog.Costs.seq (costs_gkrLayers depth _) (fun _ _ ↦ trivial) ?_) ?_) ?_ <;>
    (try simp only [List.length_nil]) <;> omega

/-- The bus phase, at the push side's depth. -/
theorem costs_verifyBusBalance (layout : Layout) :
    Prog.Costs height (verifyBusBalance .computed layout)
      (busBits + 1 + (2 + gkrCost (busLayout [0, layout.logMemory, layout.logBytecode]
        layout.push).depth 0) + 5) fun _ ↦ True := by
  refine Prog.Costs.seq (Prog.Costs.sampleN _) (fun _ _ ↦ Prog.Costs.seq Prog.Costs.sampleE
    (fun _ _ ↦ Prog.Costs.seq (costs_verifyGkrGrandProducts _) (fun r _ ↦ ?_) ?_) ?_) ?_
  · obtain ⟨countRoot, point, treeValues⟩ := r
    refine Prog.Costs.seq (Prog.Costs.require (n := 0) _) (fun _ _ ↦ Prog.Costs.seq
      (Prog.Costs.readN 3)
      (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE
        (fun _ _ ↦ trivial) ?_) ?_) ?_) ?_ <;> omega
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

/-- The tables flush `34` pushes. -/
theorem busBlocks_push_length (hs rows : List ℕ) (h : hs.length = 6) (hr : rows.length = 6) :
    (busBlocks hs rows).1.length = 34 := by
  match hs, rows, h, hr with
  | [_, _, _, _, _, _], [_, _, _, _, _, _], _, _ => rfl

/-! ## The announced sizes -/

/-- What `buildLayout` guarantees of a layout it returns. -/
structure LayoutBounds (layout : Layout) : Prop where
  /-- The memory has at most `2^32` cells. -/
  logMemory_le : layout.logMemory ≤ 32
  /-- The bytecode has at most `2^32` tuples. -/
  logBytecode_le : layout.logBytecode ≤ 32
  /-- One height per table. -/
  heights_length : layout.tableLogHeights.length = 6
  /-- Every table has at most `2^32` rows. -/
  heights_le : ∀ h ∈ layout.tableLogHeights, h ≤ 32
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
    rcases hbb : busBlocks (tableRows.map log2Ceil) tableRows with ⟨push, pull, count⟩
    rcases hpl : placementsOf (columnKappas logMemory (logLength - busBits)
      (tableRows.map log2Ceil)) with ⟨pl, sl⟩
    simp only [hbb, hpl, Option.some.injEq] at h
    subst h
    refine ⟨hm, hb, ?_, ?_, ⟨tableRows, by simpa [tables] using hlen, by simp [hbb]⟩⟩
    · simpa [tables] using hlen
    · simp only [List.all_eq_true, decide_eq_true_eq] at hall
      simp only [List.mem_map]
      rintro _ ⟨r, hr, rfl⟩
      exact log2Ceil_le (hall r hr)

/-- The sizes a run of `readSizes` returns: a layout `buildLayout` built, the stack in the
window, the rate exponent in `1..4`. -/
def SizesOK (p : Layout × ℕ) : Prop :=
  LayoutBounds p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 4 ∧ minStackedLog ≤ p.1.stackLog ∧
    p.1.stackLog ≤ maxStackedLog

/-- The announced sizes: eight reads, and sizes in the window the program checks. -/
theorem costs_readSizes {height : ℕ} (bytecode : List K) :
    Prog.Costs height (readSizes bytecode) 8 SizesOK := by
  refine Prog.Costs.seq (Prog.Costs.readN _) (fun announced _ ↦ Prog.Costs.seq
    (Prog.Costs.require (n := 0) _) (fun _ _ ↦ Prog.Costs.seq (Prog.Costs.require (n := 0) _)
      (fun _ hr ↦ Prog.Costs.seq (costs_liftOption _ 0) (fun layout hl ↦ Prog.Costs.seq
        (Prog.Costs.require (n := 0) _) (fun _ hs ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · exact ⟨layoutBounds_of_buildLayout hl, hr.1, hr.2, hs.1, hs.2⟩
  all_goals simp [tables]

/-- The push side of a built layout has depth at most `38`. -/
theorem pushDepth_le {layout : Layout} (h : LayoutBounds layout) :
    (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth ≤ 38 := by
  refine stackOffsets_snd_le _ 32 6 ?_ ?_
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

/-- The GKR walk over at most `38` levels costs at most `gkrBound`. -/
theorem gkrCost_le : ∀ D ≤ 38, gkrCost D 0 ≤ gkrBound := by decide

/-- **The bus phase** costs at most `12 + gkrBound` on a built layout. -/
theorem costs_verifyBusBalance_le {height : ℕ} {layout : Layout} (h : LayoutBounds layout) :
    Prog.Costs height (verifyBusBalance .computed layout) (busBits + 1 + (2 + gkrBound) + 5)
      fun _ ↦ True :=
  (costs_verifyBusBalance layout).mono
    (by have := gkrCost_le _ (pushDepth_le h); omega) fun _ h ↦ h

/-! ## The table sumcheck and the public input -/

section Phases2

variable {height : ℕ}

/-- The tables' row evaluations: at most `w` reads per table. -/
theorem costs_tableTerms (constraintPowers formPowers point : List E) (w : ℕ) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), (∀ r ∈ rows, r.1.width ≤ w) →
      Prog.Costs height (tableTerms constraintPowers formPowers point rows cursor final claims)
        (rows.length * w) fun _ ↦ True
  | [], _, _, _, _ => trivial
  | (table, h, forms, weight) :: rest, cursor, final, claims, hw => by
    have h0 := hw _ List.mem_cons_self
    refine Prog.Costs.seq (Prog.Costs.readN _) (fun _ _ ↦
      (costs_tableTerms constraintPowers formPowers point w rest _ _ _
        fun r hr ↦ hw r (List.mem_cons_of_mem _ hr)).mono ?_ fun _ h ↦ h) ?_
    all_goals simp only [List.length_cons, Nat.succ_mul] at h0 ⊢; omega

private theorem foldl_max_le (M : ℕ) : ∀ (l : List ℕ) (acc : ℕ), acc ≤ M → (∀ x ∈ l, x ≤ M) →
    l.foldl max acc ≤ M
  | [], _, h, _ => h
  | x :: xs, acc, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le M xs _ (max_le h (hl x List.mem_cons_self))
      fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)

/-- Every table is at most `37` columns wide. -/
theorem tables_width_le : ∀ t ∈ tables, t.width ≤ 37 := by decide

/-- The table sumcheck over tables of at most `2^32` rows. -/
theorem costs_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E)
    (hh : ∀ h ∈ heights, h ≤ 32) :
    Prog.Costs height
      (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target)
      (32 * 4 + 6 * 37) fun _ ↦ True := by
  have hmax := foldl_max_le 32 heights 0 (Nat.zero_le _) hh
  refine Prog.Costs.seq (costs_sumcheck _ _ _) (fun r _ ↦ ?_) ?_
  · obtain ⟨challenges, claim⟩ := r
    have hrows : ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse))), r.1.width ≤ 37 :=
      fun r hr ↦ tables_width_le _ (List.of_mem_zip hr).1
    have hlen : (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse)))).length ≤ 6 := by
      simp only [List.length_zip]
      exact (min_le_left _ _).trans (by simp [tables])
    refine Prog.Costs.seq (costs_tableTerms _ _ _ 37 _ 0 0 [] hrows) (fun r _ ↦ ?_) ?_
    · obtain ⟨final, claims⟩ := r
      exact Prog.Costs.seq (Prog.Costs.require (n := 0) _) (fun _ _ ↦ trivial) (Nat.zero_le _)
    · simp only [List.length_replicate, show max 4 2 = 4 from rfl]
      have := Nat.mul_le_mul_right 37 hlen
      omega
  · simp only [List.length_replicate, show max 4 2 = 4 from rfl]
    omega

/-- **The table phase** on a built layout. -/
theorem costs_tablePhase {layout : Layout} (hl : LayoutBounds layout) (bus : BusResult) :
    Prog.Costs height (tablePhase layout bus) (1 + (32 * 4 + 6 * 37)) fun _ ↦ True :=
  Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦ Prog.Costs.seq
    (costs_tableSumcheck _ _ _ _ _ _ hl.heights_le) (fun _ _ ↦ trivial) (by omega)) (by omega)

/-- **The public-input phase**: one challenge. -/
theorem costs_publicInputPhase (layout : Layout) (publicInput : Digest) :
    Prog.Costs height (publicInputPhase layout publicInput) 1 fun _ ↦ True :=
  Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦ trivial) (by omega)

/-! ## Flock and ring switching -/

theorem fixedChallenges_length : fixedChallenges.length = 7 := by simp [fixedChallenges]

theorem flockKSkip_eq : flockKSkip = 6 := by decide

theorem flockNumLincheckRounds_eq : flockNumLincheckRounds = 8 := by decide

/-- The Flock zerocheck at `logN` variables. -/
theorem costs_verifyFlockZerocheck (logN : ℕ) :
    Prog.Costs height (verifyFlockZerocheck logN) (4 * (logN - 13) + 88) fun _ ↦ True := by
  refine Prog.Costs.seq (Prog.Costs.sampleN _) (fun sampled hs ↦ ?_)
    (by rw [flockKSkip_eq, fixedChallenges_length]; omega)
  have hr : ((fixedChallenges ++ sampled).map some).length = 7 + (logN - 13) := by
    simp only [List.length_map, List.length_append, fixedChallenges_length, hs, flockKSkip_eq]
    omega
  refine Prog.Costs.seq (Prog.Costs.readN kBits) (fun _ _ ↦ Prog.Costs.seq Prog.Costs.sampleE
    (fun _ _ ↦ Prog.Costs.seq (costs_sumcheck _ _ _) (fun r _ ↦ ?_) ?_) ?_) ?_
  · obtain ⟨chi, running⟩ := r
    refine Prog.Costs.seq Prog.Costs.readE (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE
      (fun _ _ ↦ trivial) ?_) ?_
    all_goals (try simp only [hr, flockKSkip_eq, fixedChallenges_length, kBits,
      show max 3 2 = 3 from rfl])
    all_goals omega
  all_goals (try simp only [hr, flockKSkip_eq, fixedChallenges_length, kBits,
    show max 3 2 = 3 from rfl])
  all_goals omega

/-- The Flock lincheck: eight rounds and the `64` slices. -/
theorem costs_verifyFlockLincheck (zc : ZerocheckResult) :
    Prog.Costs height (verifyFlockLincheck .computed zc) 89 fun _ ↦ True := by
  refine Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦ Prog.Costs.seq (costs_sumcheck _ _ _)
    (fun r _ ↦ ?_) ?_) ?_
  · obtain ⟨roundChallenges, rLc⟩ := r
    exact Prog.Costs.seq (Prog.Costs.readN kBits) (fun _ _ ↦ Prog.Costs.seq
      (Prog.Costs.pure0 _) (fun _ _ ↦ Prog.Costs.seq
        (Prog.Costs.require (n := 0) _) (fun _ _ ↦ trivial) (Nat.zero_le _)) (Nat.zero_le _))
      (by simp only [List.length_replicate, flockNumLincheckRounds_eq, kBits,
        show max 3 2 = 3 from rfl]; omega)
  all_goals (try simp only [List.length_replicate, flockNumLincheckRounds_eq,
    show max 3 2 = 3 from rfl])
  all_goals omega

/-- **Flock** at `logN` variables. -/
theorem costs_verifyFlock (logN : ℕ) :
    Prog.Costs height (verifyFlock .computed logN) (4 * (logN - 13) + 177) fun _ ↦ True :=
  Prog.Costs.seq (costs_verifyFlockZerocheck logN) (fun zc _ ↦
    (costs_verifyFlockLincheck zc).mono (by omega) fun _ h ↦ h) (by omega)

/-- **Ring switching**: six challenges. -/
theorem costs_ringSwitch (point s : List E) :
    Prog.Costs height (ringSwitch point s) 6 fun _ ↦ True :=
  Prog.Costs.seq (Prog.Costs.sampleN _) (fun _ _ ↦ trivial) (by simp [ringMapShifts])

end Phases2

/-! ## WHIR -/

section Whir

variable {height : ℕ}

/-- A level's fold rounds, three each; they append one fold challenge each. -/
theorem costs_foldRounds : ∀ (n : ℕ) (s : WhirState) (levelFolds : List E),
    Prog.Costs height (foldRounds n s levelFolds) (3 * n)
      fun r ↦ r.1.folds.length = s.folds.length + n
  | 0, _, _ => rfl
  | n + 1, s, levelFolds => by
    refine Prog.Costs.seq Prog.Costs.sampleE (fun c _ ↦ Prog.Costs.seq
      (costs_sumcheckRoundPoly 3 _ none) (fun _ _ ↦
        (costs_foldRounds n _ _).mono ?_ fun r hr ↦ ?_) ?_) ?_
    · simp only [show max 3 2 = 3 from rfl]; omega
    · rw [hr, List.length_append, List.length_singleton]; omega
    · simp only [show max 3 2 = 3 from rfl]; omega
    · omega

/-- The final level's tail rounds, at most three each. -/
theorem costs_tailRounds : ∀ (n : ℕ) (target : E) (quad : List E),
    Prog.Costs height (tailRounds n target quad) (3 * n) fun _ ↦ True
  | 0, _, _ => trivial
  | n + 1, _, quad => by
    refine Prog.Costs.seq Prog.Costs.sampleE (fun c _ ↦ Prog.Costs.ite (fun _ ↦ trivial)
      fun _ ↦ Prog.Costs.seq (costs_sumcheckRoundPoly 3 _ none) (fun _ _ ↦
        Prog.Costs.seq (costs_tailRounds n _ _) (fun r _ ↦ ?_) ?_) ?_) ?_
    · obtain ⟨rest, target⟩ := r
      trivial
    all_goals (try simp only [show max 3 2 = 3 from rfl])
    all_goals omega

/-- The query sampling loop: at most one challenge per round of fuel, and at most `remaining`
positions. -/
theorem costs_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    Prog.Costs height (sampleQueriesAux depth fuel remaining) fuel
      fun qs ↦ qs.length ≤ remaining
  | 0, _ => Nat.zero_le _
  | fuel + 1, remaining => by
    refine Prog.Costs.ite (fun _ ↦ Nat.zero_le _) fun hr ↦ Prog.Costs.seq Prog.Costs.sampleE
      (fun c _ ↦ Prog.Costs.seq (costs_sampleQueriesAux depth fuel _) (fun qs hqs ↦ ?_) ?_) ?_
    · show (List.map _ (List.range (min (192 / depth) remaining)) ++ qs).length ≤ remaining
      simp only [List.length_append, List.length_map, List.length_range]
      omega
    all_goals omega

theorem costs_sampleQueries (depth count : ℕ) :
    Prog.Costs height (sampleQueries depth count) count fun qs ↦ qs.length ≤ count :=
  costs_sampleQueriesAux depth count count

/-- Gluing claims keeps the fold challenges. -/
theorem glue_folds (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) :
    (glue lam s pending).folds = s.folds := by
  unfold glue
  generalize (1 : E) = c
  induction pending generalizing s c with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨value, intro, weightAt⟩ := p
    simp only [List.foldl_cons]
    exact ih _ _

/-- **The WHIR levels** from a message of `μ` variables cost `whirCost`, when their commitments
have height at most `height`. -/
theorem costs_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (μ : ℕ),
      logN - s.folds.length = μ → whirHeightsLE height μ levels = true →
      Prog.Costs height (whirLevels logN laneFolds evaluateBasis index levels s)
        (whirCost height μ levels) fun _ ↦ True
  | [], _, _, _, _, _ => trivial
  | [level], index, s, μ, hμ, _ => by
    have hq2 : level.queries * (2 + height) = level.queries + level.queries * (1 + height) := by
      ring
    simp only [whirCost]
    generalize hP : 2 ^ (μ - level.fold) = P
    refine Prog.Costs.seq (costs_foldRounds level.fold s []) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', levelFolds⟩ := r
    simp only at hr
    have hm : logN - s'.folds.length = μ - level.fold := by rw [hr]; omega
    refine Prog.Costs.seq (Prog.Costs.readN _) (fun _ _ ↦ Prog.Costs.seq (Prog.Costs.pure0 _)
      (fun _ _ ↦ Prog.Costs.seq (Prog.Costs.grindP _) (fun _ _ ↦ Prog.Costs.seq
        (costs_sampleQueries _ level.queries) (fun queries hq ↦ ?_) ?_) ?_) ?_) ?_
    · have hqm := Nat.mul_le_mul_right (1 + height) hq
      refine Prog.Costs.seq Prog.Costs.sampleE (fun lam _ ↦ Prog.Costs.seq
        (Prog.Costs.queryP index queries) (fun words _ ↦ Prog.Costs.seq
          (costs_sumcheckRoundPoly 3 _ none) (fun intro _ ↦ Prog.Costs.seq
            (costs_tailRounds _ _ _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_
      · obtain ⟨tailFolds, target⟩ := r
        exact (Prog.Costs.require (n := 0) _).mono (Nat.zero_le _) fun _ _ ↦ trivial
      all_goals (try simp only [hm, hP, show max 3 2 = 3 from rfl])
      all_goals omega
    all_goals (try simp only [hm, hP])
    all_goals omega
  | level :: next :: rest, index, s, μ, hμ, hH => by
    have hq2 : level.queries * (2 + height) = level.queries + level.queries * (1 + height) := by
      ring
    simp only [whirHeightsLE, Bool.and_eq_true, decide_eq_true_eq] at hH
    simp only [whirCost]
    refine Prog.Costs.seq (costs_foldRounds level.fold s []) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', levelFolds⟩ := r
    simp only at hr
    have hm : logN - s'.folds.length = μ - level.fold := by rw [hr]; omega
    refine Prog.Costs.seq (Prog.Costs.commitP _ (by rw [hm]; exact hH.1)) (fun _ _ ↦
      Prog.Costs.seq (Prog.Costs.sampleN _) (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE
        (fun _ _ ↦ Prog.Costs.seq (costs_sumcheckRoundPoly 3 _ none) (fun _ _ ↦
          Prog.Costs.seq (Prog.Costs.pure0 _) (fun _ _ ↦
          Prog.Costs.seq (Prog.Costs.grindP _) (fun _ _ ↦ Prog.Costs.seq
            (costs_sampleQueries _ level.queries) (fun queries hq ↦ ?_) ?_) ?_) ?_) ?_) ?_) ?_)
            ?_
    · have hqm := Nat.mul_le_mul_right (1 + height) hq
      refine Prog.Costs.seq Prog.Costs.sampleE (fun lam _ ↦ Prog.Costs.seq
        (Prog.Costs.queryP index queries) (fun words _ ↦ Prog.Costs.seq
          (costs_sumcheckRoundPoly 3 _ none) (fun intro _ ↦
            (costs_whirLevels logN laneFolds evaluateBasis (next :: rest) (index + 1) _
              (μ - level.fold) (by rw [glue_folds]; exact hm) hH.2).mono ?_
              fun _ h ↦ h) ?_) ?_) ?_
      all_goals (try simp only [hm, show max 3 2 = 3 from rfl])
      all_goals omega
    all_goals (try simp only [hm, show max 3 2 = 3 from rfl])
    all_goals omega

/-- **WHIR** on a stack whose every ladder costs at most `W`. -/
theorem costs_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E)
    (W : ℕ) (hW : ∀ levels, deriveConfig logN logInvRate = some levels →
      whirHeightsLE height logN levels = true ∧ whirCost height logN levels ≤ W) :
    Prog.Costs height (verifyWhir logN logInvRate target evaluateBasis) (2 + W)
      fun _ ↦ True := by
  refine Prog.Costs.seq (costs_liftOption _ 0) (fun config hc ↦ Prog.Costs.seq
    (costs_sumcheckRoundPoly 3 _ none) (fun quad _ ↦
      ((costs_whirLevels logN _ evaluateBasis config 0 _ logN rfl (hW config hc).1).mono
        ((hW config hc).2.trans (by omega)) fun _ h ↦ h)) ?_) (Nat.zero_le _)
  simp only [show max 3 2 = 3 from rfl]; omega

/-- **The stack's commitment**, at a height the ladder bounds. -/
theorem costs_commitStack (logN logInvRate : ℕ)
    (hH : ∀ levels, deriveConfig logN logInvRate = some levels →
      stackHeightLE height logN levels = true) :
    Prog.Costs height (commitStack logN logInvRate) 2 fun _ ↦ True := by
  refine Prog.Costs.seq (costs_liftOption _ 0) (fun config hc ↦ ?_) (Nat.zero_le _)
  have h := hH config hc
  cases config with
  | nil => trivial
  | cons level rest =>
    simp only [stackHeightLE, decide_eq_true_eq] at h
    exact Prog.Costs.commitP _ h

/-- **The stacked opening**: the batching challenge and WHIR. -/
theorem costs_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (W : ℕ) (hW : ∀ levels, deriveConfig stackLog logInvRate = some levels →
      whirHeightsLE height stackLog levels = true ∧ whirCost height stackLog levels ≤ W) :
    Prog.Costs height (verifyStackedOpening stackLog logInvRate claims) (1 + (2 + W))
      fun _ ↦ True :=
  Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦
    (costs_verifyWhir _ _ _ _ W hW).mono (by omega) fun _ h ↦ h) (by omega)

end Whir

/-! ## Every admissible ladder -/

/-- Over every ladder `Parameters.Whir.ladder` returns, the commitments have height at most
`costHeight` and the WHIR levels cost at most `whirBound`; decided over the 56 admissible
pairs. -/
theorem ladder_cost (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) :
    whirHeightsLE costHeight μ levels = true ∧ stackHeightLE costHeight μ levels = true ∧
      whirCost costHeight μ levels ≤ whirBound := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < Whir.maxLogInvRate + 1, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (whirHeightsLE costHeight μ levels && stackHeightLE costHeight μ levels &&
            decide (whirCost costHeight μ levels ≤ whirBound)) = true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  · simp [Whir.ladder, hadm] at h

/-! ## The whole program -/

private theorem getD_le_of_forall {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) (i : ℕ) :
    l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hi)

/-- **The cost of `verify_execution`.** -/
theorem costs_verifyExecution (bytecode : List K) (publicInput : Digest) :
    Prog.Costs costHeight (verifyExecution .computed bytecode publicInput) leanVmCost fun _ ↦ True := by
  unfold leanVmCost
  refine Prog.Costs.seq (costs_readSizes bytecode) (fun p hp ↦ ?_) (by omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, -⟩ := hp
  have hblake : layout.tableLogHeights.getD opBlake2s 0 ≤ 32 :=
    getD_le_of_forall hl.heights_le opBlake2s
  refine Prog.Costs.seq (costs_commitStack _ _ fun levels h ↦ (ladder_cost _ _ levels h).2.1)
    (fun _ _ ↦ Prog.Costs.seq (costs_verifyBusBalance_le hl) (fun bus _ ↦ Prog.Costs.seq
      (costs_tablePhase hl bus) (fun claims _ ↦ Prog.Costs.seq
        (costs_publicInputPhase layout publicInput) (fun publicClaims _ ↦ Prog.Costs.seq
          (costs_verifyFlock _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨flockPoint, flockS⟩ := r
    refine Prog.Costs.seq (costs_ringSwitch flockPoint flockS) (fun r _ ↦ ?_) ?_
    · obtain ⟨ringTarget, ringWeight⟩ := r
      refine (costs_verifyStackedOpening _ _ _ whirBound fun levels h ↦
        ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2⟩).mono ?_
          fun _ h ↦ h
      simp only [flockBound, blake2sR1csLogSize] at *
      omega
    · simp only [flockBound, blake2sR1csLogSize] at *
      omega
  all_goals simp only [flockBound, blake2sR1csLogSize] at *
  all_goals omega

/-- **The cost of the leanVM verifier program**: every run of `leanVmProgram` costs at most
`leanVmCost`, every commitment having height at most `costHeight`, for every bytecode and public
input. -/
theorem costLE_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    (leanVmProgram bytecode publicInput).CostLE costHeight leanVmCost :=
  Prog.Costs.seq (costs_verifyExecution bytecode publicInput) (fun _ _ ↦ trivial) le_rfl

/-! ## The seed and the query bound -/

/-- The IV's preimage before the bytecode's hash: `"leanvm" ‖ u64le(32) ‖ R1CS_DIGEST`. -/
def ivPrefix : Bytes :=
  [0x6c, 0x65, 0x61, 0x6e, 0x76, 0x6d] ++ [32, 0, 0, 0, 0, 0, 0, 0] ++ r1csDigest

/-- The IV's preimage is the prefix and the bytecode's hash. -/
theorem ivPreimage_eq (d : Digest) : ivPreimage d = ivPrefix ++ digestBytes d := rfl

/-- **The leanVM seed as a seeding chain**: the bytecode's hash, the IV around it, and the
public input after it (`seedWith`). -/
def leanVmSeed (bytecode : List K) (publicInput : Digest) : Seed where
  first := bytecode.flatMap kBytes
  steps := [(ivPrefix, []), ([], digestBytes publicInput)]

/-- The seeding chain computes `seedWith`, with any hash in any lawful monad. -/
theorem seedRun_leanVmSeed {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (bytecode : List K) (publicInput : Digest) :
    (leanVmSeed bytecode publicInput).run H = seedWith H bytecode publicInput := by
  simp [Seed.run, leanVmSeed, seedWith, Seed.input, ivPreimage_eq]

/-- The seeded verifier of the random-oracle theorem at the leanVM seed and program is the
compiled leanVM verifier with the hash a query. -/
theorem verifierComp_leanVm (bytecode : List K) (publicInput : Digest) (π : Proof) :
    verifierComp (leanVmSeed bytecode publicInput) (leanVmProgram bytecode publicInput) π =
      verifyWith queryH bytecode publicInput π := by
  simp only [verifierComp, Rom.verify, verifyWith, seedRun_leanVmSeed]

/-- **The query bound of the leanVM verifier**: three seeding hashes and the program's cost. -/
def leanVmQueryBound : ℕ := 1 + 2 + leanVmCost

/-- The bound, evaluated. -/
theorem leanVmQueryBound_eq : leanVmQueryBound = 13213 := by decide

/-- **The compiled leanVM verifier makes at most `leanVmQueryBound = 13213` queries** to the
random oracle on every proof, for every bytecode and public input: the hypothesis `hV` of
`romSound` at the leanVM program and seed. -/
theorem isTotalQueryBound_leanVm (bytecode : List K) (publicInput : Digest) (π : Proof) :
    IsTotalQueryBound
      (verifierComp (leanVmSeed bytecode publicInput) (leanVmProgram bytecode publicInput) π)
      leanVmQueryBound :=
  isTotalQueryBound_verifierComp (costLE_leanVmProgram bytecode publicInput) _ π

end
end LeanVM.Protocol.Verifier
