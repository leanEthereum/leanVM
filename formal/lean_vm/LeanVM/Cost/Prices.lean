module

public import Statement.CostMachine

/-!
# The budgets' exact prices

The closed-form prices `lean_vm` proves of the compiled extractor's parts and of the compiled
guest decoder (`Cost/Bounds/`, `Cost/AS/Bounds/`), natural-number formulas only. The statement's
budgets are short upper bounds on them: `leanVmKnowledgeExtractorBudget`
(`Statement/CostMachine.lean`) above the agreement-set extractor's price wherever it extracts, at
the stack size the proof announces (`asPrice_within`, `Cost/AS/End.lean`), and
`guestWitnessDecoderBudget` (`Statement/LeanVmGuest.lean`) above `guestDecoderPrice` on every valid
execution (`guestDecoderPrice_le_budget`, `Cost/Bounds/Guest/Budget.lean`).
-/

/-! ## The extractor's parts

The transcript's index and the committed leaves (`Cost/Bounds/Leaves.lean`), the runner's step and
the bytecode's words; the agreement-set extractor's price is assembled from them in
`Cost/AS/Bounds/Top.lean` and bounded by the budget in `Cost/AS/Within.lean`. -/

namespace LeanVM.Cost

@[expose] public section

/-- The limbs of a natural below `2^E`, at most. -/
def limbsBelowTwoPow (E : ℕ) : ℕ := E / 64 + 1

/-- One step of a leanISA run replayed (the extractor's candidate runs, the guest decoder's
replay), its memory of `2^κ` words and its program of `2^ℓ` instructions indexed in sorted
tables. -/
def runnerStepPrice (κ ℓ : ℕ) : ℕ := 366000 + 36 * ℓ + 936 * κ

/-- One step of the transcript's replay, amortized: two lookups among `25`-word keys, one among
`8`-word keys, three insertions into sorted maps below `2^D` entries, a block's `B` bytes; `W` the
limbs of positions and weights. -/
def replayStepPrice (B D W : ℕ) : ℕ :=
  2 * (D * (20 + (40 + 26 * 25 + 9 * W) * (D + 2))) + D * (20 + (40 + 26 * 8 + 9 * W) * (D + 2)) +
    2 * ((26 * 25 + 37) * D) + (26 * 8 + 37) * D + 3 * ((32 + 2 * W) * D) + 6 * W + 19 * B + 10342

/-- One step of the first answers, amortized: a lookup and an insertion of a key of at most `L`
bytes. -/
def firstAnswersStepPrice (L D W : ℕ) : ℕ :=
  D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + (26 * L + 37) * D + (32 + 2 * W) * D + 78 + 2 * W

/-- One step of the preimage index, amortized: a key of at most `L` bytes, a lookup, an
insertion. -/
def preimageStepPrice (L D W : ℕ) : ℕ :=
  31 * L + 162 * (D * D) + 537 * D + 145 + W * (9 * (D * (D + 2)) + 2 * (D + 1))

/-- The transcript's index: `N` permutation queries, `N + 2 ≤ 2^D`, evaluations of at most `L`
bytes kept. -/
def transcriptIndexPrice (D L N W : ℕ) : ℕ :=
  (26 * 8 + 37) * D + (replayStepPrice (L + 136) D W + 16) * N +
    (120 * (L + 136) + 9363) * (N + 1) + 442 +
    (N + 1) * ((firstAnswersStepPrice L D W + 11) + (preimageStepPrice L D W + 11) +
      D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + 67) + 44

/-- The bytecode's words: `16·2^ℓ` words. -/
def bytecodeWordsPrice (ℓ : ℕ) : ℕ := 5712 * 2 ^ ℓ + 947

/-- The levels of the extractor's sorted maps for `N` permutation queries: `log₂(N + 2) + 1`. -/
def extractorSortedMapLevels (N : ℕ) : ℕ := Nat.log2 (N + 2) + 1

end

end LeanVM.Cost

namespace LeanVM.Node

@[expose] public section

/-! ### The guest decoder's price

A closed-form upper bound that `lean_vm` proves on the compiled decoder's price
(`Cost/Bounds/Guest/Budget.lean`): a price per step of the
run, the address tables at the run's `κ` and `ℓ`, and a constant. Per step, the decoder replays the
step (`runnerStepPrice`) and files the state in its table of function entries
(`guestDecoderStateFilingPrice`: the precondition test of each function entered there, at most two,
and its share of one stable sort of at most `2·(steps + 1)` pairs, whose price grows as
`log(steps)`). The constant is the price of reading the witness at the counts and the cursors a
valid execution bounds: the decoder reads its counts off the memory, and the guest program's own
asserts bound them on every valid execution (`lean_vm`'s `valid_counts`: at most `16` children,
`65535` declared claims and raw signatures of each scheme and `65535` coverage slots in the two
regions together); each
child's cursor, the words of the child proof's stream before its opening, is at most `8192` on every
valid execution (`valid_cursor`: the decoded witness explains the input, so the deferring verifier
accepts the child's proof, whose stream has at most `8192` scalars, `stream_le_of_verifyDeferred`);
and the decoder clamps `da_verify`'s row count at `1024` (`LeanDa.maxRows`; `da_verify` asserts it,
so the clamp changes nothing on a valid execution) on every input.
`guestDecoderWitnessPriceAtValidCounts ≈ 2^38.63` is mostly the raw signatures (`65535` of each
scheme, about `2^38.35`, the leanSPHINCS ones `2^38.14`: each reads about `1500` words of its four
frames, `verify_sig_lean_sphincs`' and its three `sp_wots`', each frame looked up once; a leanXMSS
one `184` words of its `main_loop2` iteration's frame, looked up once on its `56` arguments), the
children's claims (each of the `16` children's priced at `65535` claims of each scheme, about
`2^35.45`) and the two regions' tables (about `2^34.01`); the children's cursors are `16·8192`
words at `1338` each, about `2^27.39`. The address tables of the memory and the program
are priced at the execution's `κ` and the program's `ℓ`
(`guestDecoderAddressTablesPrice κ ℓ = (74κ + 121)·2^κ + (74ℓ + 121)·2^ℓ + 42`: at the guest's
`ℓ = 19`, `2^31.21` at `κ = 20`, `2^41.19` at `κ = 30`). A frame lookup (`guestDecoderFramePrice`,
one binary search, growing as `log(steps)`) is paid about `2^25.19` times
(`guestDecoderFrameLookupCountAtValidCounts`; a search on `main_loop2`'s `56` arguments counts as
four), `2^40.06` in all at `2^20` steps and `2^41.16` at `2^51`.

So the bound is `O(steps·log steps)` below `2^61` steps (`O(steps·log² steps)` as `steps` grows,
through the positions' limbs), plus the address tables, `O(κ·2^κ + ℓ·2^ℓ)` in the memory's size
`2^κ` and the program's `2^ℓ`: per step about `2^20.5` to `2^21` (`2^20.55` at `κ = 16` and no
step, `2^20.98` at `κ = 30` and `2^60` steps; `κ` and `ℓ` enter the step's price,
`runnerStepPrice`). At the guest's `ℓ = 19` it is `2^41.62` at `κ = 20` and `2^20` steps, `2^44.83`
at `κ = 24` and `2^24`, `2^48.78` at `κ = 28` and `2^28`, `2^50.79` at `κ = 30` and `2^30`,
`2^71.93` at `κ = 30` and `2^51`, and `2^80.98` at `κ = 30` and `2^60`: the terms besides the steps'
(the address tables included: `2^40.52` at `κ = 20` and `2^20` steps to `2^42.39` at `κ = 30` and
`2^60`) dominate up to about `2^20` steps at `κ ≤ 24`, `2^21` at `κ = 28` and `2^22` at `κ = 30`, the per-step price
beyond; the log factor enters through the entry table's key exponent,
`Nat.log2 (2·(steps + 1)) + 1`. A valid execution of the guest program has fewer than `2^51`
steps: the memory is fixed and every instruction reads a cell at `fp·o` for an offset `o` fixed by
`pc`, so at each `pc` at most `2^κ` values of `fp` let a step succeed; the run is determined by
`(pc, fp)`, and a repeated state would loop without halting (`2^ℓ·2^κ` states, `ℓ = 19`, `κ ≤ 30`;
argued, not a Lean theorem; `lean_vm` proves fewer than `2^128`, `steps_lt_replayFuel`). The
per-step price and the frame lookup's are `lean_vm`'s bounds on the compiled decoder's own work,
stated exactly (`entryArrayStatePrice_eq`; `frameAtAPrice_le`, equal at `16` words), at small maxima
only (a memory read at `1271`, its price at `κ = 32`, above the deployed `κ ≤ 30`; two functions entered at a pc;
`16` words a frame). The constant prices the witness at the bounds above, not at the run's: `16`
children, each with `65535` claims of each scheme (the two regions together hold at most `65535`)
and a cursor of `8192` words, `65535` declared claims and raw signatures of each scheme, `32` rows of the DA matrix,
and the frame lookups these take. So on an execution with fewer children and claims, at `κ ≤ 28` and
well below `2^22` steps, the budget is several times what the compiled decoder spends (at `κ = 30`
the address tables, priced at the run's `κ`, are most of it); that looseness is an accepted
trade-off.

The literals (`8313`, `41252`, `18158`, `22021176`, `4343`, `4373`, `1584`, the `+ 39`, `+ 36`,
and the other constants below) are the bounds `lean_vm` proves of the compiled decoder's parts
(`topConst_le`, `addressTablesPrice_eq`, `entryArrayStatePrice_eq`, `frameAtAPrice_le`,
`Cost/Bounds/`); a reviewer checks only their size. They are the deployed guest program's (its
tables of preconditions and entries, its frames), not those of any program of `2^ℓ` instructions:
the budget's constants are `LeanVM.Guest.guestProgram`'s, and `GuestKnowledgeSoundness`'s `guest` is only ever that
program. -/

/-- The entry table's key exponent: `2·(steps + 1) < 2^exponent` bounds the number of the table's
keys. -/
def guestDecoderEntryTableKeyExponent (steps : ℕ) : ℕ := Nat.log2 (2 * (steps + 1)) + 1

/-- The limbs of the entry table's positions and weights (below `2^(exponent + 1)`). -/
def guestDecoderEntryTablePositionLimbs (exponent : ℕ) : ℕ :=
  LeanVM.Cost.limbsBelowTwoPow (exponent + 1)

/-- A function's precondition test at a state: `269` memory reads (`1271` each), `99` bounds of
logarithms (`706` each: a scan of the lanes of the generator's powers, no discrete logarithm),
and `24834 + 11` for the rest of the test (its checks over the deployed table of preconditions,
the powers of the generator read off a table, `preTestAt_cost_deployed`, and the call). -/
def guestDecoderPreconditionPrice : ℕ := 269 * 1271 + 99 * 706 + 24834 + 11

/-- Filing one state of the run in the entry table, a sorted array: a lookup of its pc (`8313`),
and for each of the at most two functions entered there the precondition test, the call's key
(`66` reads: at most `56` arguments, `main_loop2`'s, and `10` returns; and `41252` for the rest of the
key and the pair), then its share of the one stable sort and the deduplication of the pairs
(`(4343 + 5·limbs)·exponent + 7·limbs + 4373` a pair). -/
def guestDecoderStateFilingPrice (exponent : ℕ) : ℕ :=
  8313 + (guestDecoderPreconditionPrice + 66 * 1271 + 41252) * 2 + 36 +
    2 * ((4343 + 5 * guestDecoderEntryTablePositionLimbs exponent) * exponent +
      7 * guestDecoderEntryTablePositionLimbs exponent + 4373)

/-- A lookup of a call's frame in the entry table, one binary search (at most `16` words of
arguments and returns), and a word of the frame. -/
def guestDecoderFramePrice (exponent : ℕ) : ℕ :=
  (64 * 16 + 78 + 9 * guestDecoderEntryTablePositionLimbs exponent) * (exponent + 2) +
    27 * 16 + 1271 + 1584

/-- The sorted tables of the addresses of a memory of `2^κ` words and of a program of `2^ℓ`
instructions, built once. -/
def guestDecoderAddressTablesPrice (κ ℓ : ℕ) : ℕ :=
  (74 * κ + 121) * 2 ^ κ + (74 * ℓ + 121) * 2 ^ ℓ + 42

/-- The witness's and the decoding's price, its counts at most `M` (the declared claims and the raw
signatures of each scheme, the coverage slots of the two regions), the frame lookups and the address
tables apart: `16` children, each child's cursor at most `8192` words, the DA matrix of up to `1024`
rows, the children's proofs, the tables built once (the discrete logarithm's, the generator's
powers', the readers'). Affine in `M`. -/
def guestDecoderWitnessPriceAt (M : ℕ) : ℕ := 2986079128 + 6414234 * M

/-- How many frame lookups the witness pays for, its counts at most `M`. -/
def guestDecoderFrameLookupCountAt (M : ℕ) : ℕ := 3611473 + 8 * M

/-- The bound on the counts the decoder reads that a valid execution's asserts give
(`valid_counts`). -/
def guestDecoderCountBound : ℕ := 65535

/-- The witness's price at a valid execution's counts. -/
def guestDecoderWitnessPriceAtValidCounts : ℕ := guestDecoderWitnessPriceAt guestDecoderCountBound

/-- The frame lookups at a valid execution's counts. -/
def guestDecoderFrameLookupCountAtValidCounts : ℕ :=
  guestDecoderFrameLookupCountAt guestDecoderCountBound

/-- **An upper bound on the guest decoder's price, its counts at most `M`** (`guestDecoderPrice`
at a valid execution's `M = guestDecoderCountBound`): per step the replay and the filing of the
state, the tables of preconditions and of entries, the address tables, the witness and its frame
lookups at counts at most `M`. -/
def guestDecoderPriceAt (M κ ℓ steps : ℕ) : ℕ :=
  (LeanVM.Cost.runnerStepPrice κ ℓ + 46 +
      guestDecoderStateFilingPrice (guestDecoderEntryTableKeyExponent steps)) * (steps + 1) +
    17940 + 23146593 + guestDecoderAddressTablesPrice κ ℓ + guestDecoderWitnessPriceAt M +
    guestDecoderFrameLookupCountAt M *
      guestDecoderFramePrice (guestDecoderEntryTableKeyExponent steps) + 39

/-- **An upper bound on the guest decoder's price** on a memory of `2^κ` words, the deployed guest
program (`2^ℓ` instructions, `ℓ = 19`) and a run of `steps` steps: per step the replay and the
filing of the state, then the guest's tables of preconditions (`18158`) and of entries
(`22021176`), the address tables, the witness at a valid execution's counts and cursors, and its
frame lookups. -/
def guestDecoderPrice (κ ℓ steps : ℕ) : ℕ :=
  (LeanVM.Cost.runnerStepPrice κ ℓ + 46 +
      guestDecoderStateFilingPrice (guestDecoderEntryTableKeyExponent steps)) * (steps + 1) +
    18158 + 22021176 + guestDecoderAddressTablesPrice κ ℓ + guestDecoderWitnessPriceAtValidCounts +
    guestDecoderFrameLookupCountAtValidCounts *
      guestDecoderFramePrice (guestDecoderEntryTableKeyExponent steps) + 39

end

end LeanVM.Node
