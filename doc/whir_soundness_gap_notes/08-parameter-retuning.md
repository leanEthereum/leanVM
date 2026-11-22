# 08. Parameter retuning inside the proven analysis

Researcher 08. Question: with the soundness analysis exactly as proven today (Annex B, `thm:rbr`, the search of `whir_config.rs` and `affine_mca.rs`), how much proof size and verifier work do the protocol's knobs leave on the table? Nothing here goes beyond the Johnson radius.

Status tags used below. **Exact**: an output of the model of section 1, which reproduces the Rust search bit for bit wherever the two were compared; proof bytes and Keccak counts are exact expectations over the i.i.d. query positions. **Measured**: read off a run on this machine (Apple M4 Max, the release binary, `--threads 4`). **Estimate**: a fit or an extrapolation, with its basis stated. **Conjectured**: not checked.

## 0. Summary

1. **The model is validated.** It reproduces `WHIR_QUERIES` at all 60 admitted shapes (rates 1/2 to 1/16, $\mu = 16..30$), the internals (thresholds, lists, multiplicities) the Rust prints, and the Rust search recompiled with 12 other sets of constants (720 derivations, queries and lists, no mismatch).
2. **The deployed counts are already at the floor of this analysis.** Summed over the levels of an opening they sit 1 to 7 queries above the Johnson limit ($\eta \to 0$, unlimited lists), out of 130 to 362. No retuning of list budgets, OOD or fold grinds, degree slack or per-round loss is worth more than 1% of the proof at rate 1/2 (3% at rate 1/16). What is left is in four places: the query grind, the lane count of level 0, the stopping rule of the ladder, and (outside the PCS) the guest's Merkle cap rule.
3. **Three recommended configurations** (WHIR opening, full stack, rate 1/2; exact unless marked; section 6 has every rate):

| | $\mu = 24$ | $\mu = 28$ | $\mu = 30$ | prover cost |
| --- | --- | --- | --- | --- |
| today | 260.4 KiB, 5748 Keccak | 313.7 KiB, 7883 Keccak | 335.9 KiB, 8173 Keccak | |
| **A, constants only**: `RESIDUAL_MAX_LOG = 6`, level-0 query grind $\max(17, \mu - 6)$ bits, batch grind 14, OOD grind 16 | 247.4 KiB (-5.0%), 5408 Keccak (-5.9%) | 293.0 KiB (-6.6%), 7354 (-6.7%) | 320.6 KiB (-4.6%), 7820 (-4.3%) | encoding unchanged; grind $2^{19.8}$, $2^{22.3}$, $2^{24.1}$ permutations instead of $2^{19.7}$ to $2^{19.9}$ |
| **B, 32 lanes**: `INITIAL_FOLDING_FACTOR = 5`, grinds as today | 226.6 KiB (-13.0%), 5778 (+0.5%), guest query cycles -17% (est.) | 283.7 KiB (-9.6%), 8005 (+1.5%), -13% (est.) | 308.3 KiB (-8.2%), 8409 (+2.9%), -12% (est.) | NTT work x1.03 to x1.05, Merkle permutations x1.13, grind unchanged |
| **C, B with A's grinds** | 224.9 KiB (-13.6%), 5734 (-0.2%), -17% (est.) | 276.1 KiB (-12.0%), 7783 (-1.3%), -16% (est.) | 297.1 KiB (-11.6%), 8101 (-0.9%), -16% (est.) | as B, with A's grind |

4. **Caveats that change the ranking.** B's byte saving shrinks when the stack is not full, because level 0 leaves carry only data rows: at 62% fill it is -6.1%, -4.6%, -3.5%, -2.4% at $\mu = 24, 26, 28, 30$ (exact). Its cycle saving does not depend on the fill. B raises the Keccak count: by 0 to 5% for the guest once the cap rule's noise is removed (section 8.1), by 3 to 6% for the native verifier. A improves bytes and Keccak at every size and rate and leaves query cycles within 0.4%; its only cost is grinding time.
5. **Keccak is not the recursive verifier's dominant cost on the one profile measured.** In a 2-to-1 recursion over $\mu = 23$ children, level-0 queries take 47% of the guest's cycles (478 cycles a query, measured) while all KECCAK steps weigh about 18% of proving cost (estimate, a KECCAK step at about 8 ordinary cycles). The lane count is therefore worth more to recursion than the hash count suggests.
6. **Prover time is better spent on the level-0 rate than on any ladder knob.** Rate 1/4 buys -34% bytes for about 2.1x encoding work; lowering the domain reductions buys 3 to 13% for 1.34x to 1.36x. A useful intermediate point exists: rate 1/4 with `RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 4` gives -31% bytes at 1.75x encoding work.

## 1. The model and its validation

`scripts/08_retuning/whir_model.py` is a line-by-line port of `whir_config.rs` and `whir_config/affine_mca.rs`: the ladder, the Johnson list, the interpolation inequality (4.5) of [CWYZ26] with its `(m, D)` search (float steering in the Rust's operation order, integer decisions), the choice of $B = A - 2^i$, the exact 256-bit comparison of the fold round against its budget, the list terms (batching over 514 claims, `MAX_LIST_0 = 166`, OOD pairs), the bisection over $t_{\mathrm{end}}$, and the exact big-integer query count with the next level's batching row. Where the Rust counts a `u128` overflow as a failed hypothesis, so does the port. Every constant is a field of `Knobs`.

Validation, all **exact** comparisons:

- `validate.py`: the 60 shapes of `WHIR_QUERIES`, twice (the Rust's bisection, and a faster search used nowhere in this note's numbers): 120 derivations, 0 mismatches.
- Against `cargo test --release -p experimental_pcs print_whir_query_counts -- --ignored --nocapture` at (rate, $\mu$) = (1/2, 30), (1/2, 20), (1/4, 24), (1/16, 16): every level's queries, $\eta$, list and the multiplicities $m$ of every fold round are identical.
- `crosscheck.sh`: the Rust search cannot be run at other constants in place, so the script copies the two Rust files, unmodified but for their imports, into a scratch crate outside the repository with a stub `verifier` module carrying one variant's constants. 12 variants (lanes 4 to 7, later folds 3 to 5, reductions 0 to 4, residual caps 4 to 6, query grinds 17 to 28, fold grinds 5 to 12, batch grinds 12 to 16, OOD grinds 15 to 27), 60 shapes each: 720 derivations, 0 mismatches in query counts or level-start lists.

Not cross-checked against Rust, because the Rust has no such knob: a query grind that differs by level (thresholds do not depend on it, and `query_count` is the cross-checked function with another grind argument), ladders with per-level folds, the analysis variants of section 7, and a `MAX_LIST_0` other than 166.

## 2. The cost model and its checks

`costs.py` follows `crates/verifier/src/{whir,transcript,wire,merkle,hash}.rs` and, for the guest, `crates/aggregation/src/child.rs` and `guests/lean_ethereum.py`.

- **Proof bytes** (`wire.rs`): per level, a 16-byte header, 4 bytes a query position, each distinct leaf (8 bytes a word: $2^{k_0}$ words at level 0 or only the data rows of a partly filled stack, $2 \cdot 2^{k}$ later), and the pruned siblings, whose expected count at a tree level of $N$ nodes is $N[(1 - 1/N)^t - (1 - 2/N)^t]$. The stream: 16 bytes a scalar, 4 scalars and a nonce a fold round, root, high part, OOD nonce and value and query nonce a level, the final lane, 2 scalars a tail round.
- **Keccak, native**: `MerklePath::root` on every path, $t(\text{leaf} + \text{depth})$ permutations a level, a leaf being $\lfloor 8w/136 \rfloor + 1$ (4 at level 0, 2 later). **Keccak, guest**: paths stop at a cap of depth `merkle_cap_depth(t, depth)`, whose internal nodes are hashed once when a query reaches them (expected count computed), plus the duplex sponge's permutations (simulated from `transcript.rs`).
- **Grinding**: one permutation a nonce, $2^g$ expected. An opening grinds once a fold round, once a commitment (OOD), once for the batching and once a query message.
- **Encoding**: K words of every codeword, the same weighted by $\log_2$ of the block length (NTT work), and the Merkle trees' permutations.
- **Guest cycles of the queries** (**estimate**): a per-query formula fitted to one `DBG_PROF` profile (below).

Checks. The model covers only the WHIR part, so each is indirect.

| run (**measured**) | whole proof | model, WHIR part (**exact**) | remainder |
| --- | --- | --- | --- |
| aggregate 100 XMSS, $\mu = 23$, 44 of 64 rows, rate 1/2, 1/4, 1/8, 1/16 | 238.0, 170.1, 144.4, 131.4 KiB | 204.9, 135.9, 109.9, 96.3 KiB | 33.1, 34.2, 34.5, 35.1 KiB |
| aggregate 900 XMSS, $\mu = 26$, 40 of 64 rows, rate 1/2, 1/4 | 277.5, 200.0 KiB | 240.4, 162.9 KiB | 37.1, 37.1 KiB |
| recursion 2 to 1, $\mu = 24$, 56 of 64 rows, rate 1/2 | 271.2 KiB | 246.8 KiB | 24.4 KiB |

The remainder (everything but the opening) is constant across rates to within 2 KiB while the WHIR part moves by 108 KiB, which is what a correct byte model predicts. The WHIR opening is 86 to 91% of a rate-1/2 proof. The recursion run executed 12,373 KECCAK steps for its two $\mu = 23$ children (**measured**); the model gives $2 \times 5328 = 10{,}656$ for their openings (**exact**), 86% of the total, the rest being the transcript outside the PCS.

Calibrations (**measured**, one run each, 4 threads):

- Grind kernel (`keccak256::first_nonce`, one thread): 15.0 M permutations a second. Times below quote one thread; the prover's pool divides them.
- Aggregate 900 XMSS ($\mu = 26$, rate 1/2): proving 1.19 s, of which level 0's commitment 253 ms, the later levels' commitments 143 ms, the Keccak reduction 469 ms, the bus grind (21 bits) 52 ms. Rate 1/4: 1.64 s. At $\mu = 23$: 0.181, 0.227, 0.332, 0.528 s at rates 1/2 to 1/16. So encoding is a third of proving in that run (43% in the recursion proof below), and across the rates proving time grows by 0.24 (at $\mu = 23$) to 0.33 (at $\mu = 26$) of the rate-1/2 time per unit of encoding multiple (**estimate**, a fit to these six runs).
- Per committed K word the commitments cost 3.0, 2.4, 2.2, 2.0, 1.9 ns at levels 0 to 4, so the word count is a fair proxy of encoding time across levels, within 20%.
- Recursion 2 to 1 (445,632 cycles): the level-0 query loop 131,456 cycles, its path walks 20,040, window decoding 16,640, residual chain 40,340, for 436 queries: 478 cycles a level-0 query, 47% of all cycles. A level-1 query costs about 237. One KECCAK step costs about as much proving time as 8 ordinary cycles (**estimate**: 42 ms of Keccak reduction plus its share of the commitment for 12,373 steps, against the rest of the 275 ms for 445,632 cycles).

## 3. Where today's queries come from

Level by level at $\mu = 30$, rate 1/2 (**exact**):

| level | rate | $n$ | list $L_i$ | binding term | queries | Johnson limit | proof (KiB) | guest Keccak |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | $2^{-1}$ | $2^{25}$ | 127 | batching, $513 L \le 2^{16}$ | 218 | 217 | 221.2 | 4921 |
| 1 | $2^{-4}$ | $2^{24}$ | 148 | OOD, $\binom{L}{2} \nu \le 2^{18}$ | 55 | 55 | 43.8 | 1157 |
| 2 | $2^{-7}$ | $2^{23}$ | 162 | OOD | 32 | 31 | 25.3 | 669 |
| 3 | $2^{-10}$ | $2^{22}$ | 181 | OOD | 23 | 22 | 17.8 | 475 |
| 4 | $2^{-13}$ | $2^{21}$ | 209 | OOD | 18 | 17 | 13.6 | 367 |
| 5 | $2^{-16}$ | $2^{20}$ | 256 | OOD | 15 | 14 | 11.0 | 303 |

The Johnson limit is $\lceil (125 - g) / (\log_2 n - \tfrac12 \log_2 (n d)) \rceil$: the count at $\eta = 0$ with no list term at all, the floor of this analysis at the given grind. Level 0 is 66% of the bytes and 60% of the guest's Keccak, and a query costs about the same at every level (1.0 KiB at level 0, 0.73 to 0.80 KiB later), so what matters is the number of queries, 218 of 361 at level 0.

At small sizes another term binds: the interpolation inequality (4.5) has no solution close to the Johnson radius (section 7.3). This is why the lists of $\mu \le 22$ are below their budgets (60 instead of 127 at $\mu = 20$) and why the last levels of $\mu \le 24$ have 2 to 3 queries more than their Johnson limit.

## 4. Knob by knob

All numbers **exact**, WHIR opening with a full stack, changes relative to the deployed configuration at the same size and rate. "Guest cycles" columns are the **estimate** of section 2.

### 4.1 Query grinding

Each bit of query grind removes $1/\log_2(n/(A-1))$ queries on its level: 2.0 at rate 1/2, 1.0 at 1/4, 0.67 at 1/8, 0.5 at 1/16, and 0.5 or less on every later level. So the grind belongs on level 0's message only: grinding every level costs as many permutations again per level for a quarter of the effect or less.

| $\mu = 30$ | queries, rate 1/2 | bytes | grind (perms) | one thread | queries, rate 1/4 | bytes |
| --- | --- | --- | --- | --- | --- | --- |
| today, 17 bits everywhere | 218 55 32 23 18 15 | 335.9 KiB | $2^{19.92}$ | 0.07 s | 109 44 28 21 17 15 | 222.6 KiB |
| every level 20 | 211 53 31 22 17 15 | -3.1% | $2^{22.63}$ | 0.43 s | 106 43 27 20 16 15 | -2.8% |
| every level 24 | 203 51 30 21 17 14 | -6.5% | $2^{26.59}$ | 6.7 s | 102 41 26 19 16 14 | -6.4% |
| every level 28 | 195 49 29 20 16 14 | -9.9% | $2^{30.59}$ | 108 s | 98 40 25 19 15 13 | -9.6% |
| level 0 only, 20 | 211 55 32 23 18 15 | -2.0% | $2^{20.87}$ | 0.13 s | 106 ... | -1.4% |
| level 0 only, 22 | 207 ... | -3.2% | $2^{22.27}$ | 0.34 s | 104 ... | -2.3% |
| level 0 only, 24 | 203 ... | -4.3% | $2^{24.07}$ | 1.2 s | 102 ... | -3.3% |
| level 0 only, 26 | 199 ... | -5.5% | $2^{26.02}$ | 4.5 s | 100 ... | -4.2% |
| level 0 only, 28 | 195 ... | -6.7% | $2^{28.00}$ | 18 s | 98 ... | -5.1% |

Keccak and cycles move with the bytes (within 0.5 points). The cost is fixed while proving time grows with the stack, so the right grind depends on the size, as the bus grind already does (`bus_grinding_bits`, $\mu_{\mathrm{bus}} - 3$ bits: 21 bits in the 900-XMSS proof whose stack is $\mu = 26$, 20 bits in the recursion proof at $\mu = 24$). A level-0 query grind of $\max(17, \mu - 6)$ bits costs half of that existing grind or less in those two proofs: $2^{20}$ permutations at $\mu = 26$, 0.07 s on one thread against a 1.19 s proof on four (about 1.5% if the pool's search scales, **estimate**), and $2^{24}$ at $\mu = 30$. It saves about $2(\mu - 23)$ queries at rate 1/2. Two more bits ($\mu - 4$) save 4 more queries for four times the work.

### 4.2 List budgets: batching, OOD and fold grinds

| $\mu = 30$, rate 1/2 | lists | queries | bytes | grind |
| --- | --- | --- | --- | --- |
| today (fold 7, batch 13, OOD 15) | 127 148 162 181 209 256 | 218 55 32 23 18 15 | | $2^{19.92}$ |
| batch 12 | 63 ... | 219 ... | +0.3% | |
| fold 6 | 127 148 162 170 170 169 | 218 55 32 23 18 16 | +0.2% | |
| fold 5 | 81 85 85 85 85 85 | 218 55 32 23 19 18 | +0.8% | |
| batch 14, OOD 16 | 166 209 229 256 296 335 | 217 55 32 22 18 15 | -0.5% | $2^{20.19}$ |
| OOD 19, fold 9 | 127 580 648 724 836 609 | 218 55 31 22 17 15 | -0.6% | $2^{21.91}$ |
| batch 16, OOD 19, fold 9, `MAX_LIST_0` 512 | 237 580 648 724 836 609 | 217 55 31 22 17 15 | -0.9% | $2^{21.94}$ |
| OOD 35, fold 17 | 127 1173 1536 1219 875 609 | 218 55 31 22 17 15 | -0.6% | $2^{37.58}$ |

The deployed fold grind is the least that costs nothing, as the Rust test asserts. Batch 14 with OOD 16 takes level 0's list to the `MAX_LIST_0` cap and is the only cheap step: one query at level 0, sometimes one later. A larger OOD grind lets the later lists grow, and those lists are charged to the previous level's query message through its batching row $(t + 1) L_{i+1}/|E|$: with OOD 19 level 1's list of 580 takes 12% of level 0's query budget, which is why the row with OOD 19 has 218 at level 0 where OOD 16 has 217. Past OOD 19 nothing moves at any grind, because the fold round's own terms take over on the last levels. At rate 1/2 the whole list side is worth at most 0.9%, and at $\mu = 24$ only the level-0 query (the later levels sit on the interpolation floor). It is worth more at low rates, where the later levels are a larger share: at $\mu = 30$, batch 14, OOD 19 and fold 9 give -1.0%, -1.3% and -3.1% at rates 1/4, 1/8 and 1/16 (55 31 22 17 14 13 at 1/16) for $2^{21.9}$ permutations, a better deal there than the level-0 query grind. Raising `MAX_LIST_0` buys nothing.

### 4.3 Lanes at level 0 and the domain reduction after it

Level 0's codeword has $2^{\mu + R}$ words whatever $k_0$ is, and level 1's has $2 \cdot 2^{\mu + R - r_0}$, so $r_0$ alone sets the later levels' encoding cost and $k_0$ trades leaf width (8 bytes a lane) against tree depth (32 bytes a level) and against level 1's rate, $2^{-(R + k_0 - r_0)}$.

| $\mu = 30$, rate 1/2 | queries | bytes | guest Keccak | guest cycles | NTT work | Merkle perms |
| --- | --- | --- | --- | --- | --- | --- |
| $k_0 = 4$, $r_0 = 2$ | 218 73 37 25 19 16 15 | -9.5% | +18.5% | -15.9% | x1.40 | x1.76 |
| $k_0 = 4$, $r_0 = 3$ | 218 109 44 28 21 17 15 | -0.6% | +29.0% | -6.5% | x1.06 | x1.39 |
| $k_0 = 5$, $r_0 = 2$ | 218 55 32 23 18 15 | -12.8% | -2.8% | -17.5% | x1.36 | x1.49 |
| $k_0 = 5$, $r_0 = 3$ | 218 73 37 25 19 16 | **-8.2%** | +2.9% | **-12.3%** | x1.03 | x1.13 |
| $k_0 = 5$, $r_0 = 4$ | 218 109 44 28 21 17 | +0.3% | +13.7% | -3.1% | x0.87 | x0.94 |
| $k_0 = 6$, $r_0 = 2$ | 218 44 28 21 17 15 | -2.8% | -3.6% | -3.3% | x1.34 | x1.37 |
| $k_0 = 6$, $r_0 = 3$ (today) | 218 55 32 23 18 15 | | | | | |
| $k_0 = 6$, $r_0 = 4$ | 218 73 37 25 19 16 | +4.3% | +5.5% | +4.8% | x0.84 | x0.82 |
| $k_0 = 7$, $r_0 = 3$ | 218 44 28 21 17 15 | +26.4% | +5.4% | +33.9% | x0.97 | x0.94 |

Halving the lanes at the same $r_0$ keeps every codeword's size: level 0 has 32 lanes over twice the domain, level 1 the same block length at rate $2^{-3}$ instead of $2^{-4}$. A level-0 query shrinks by 224 bytes (256 fewer of leaf, one more sibling) and by about 140 guest cycles (**estimate**), and the later levels take 27 more queries. The saving grows as the tree gets shallower: -8.2% at $\mu = 30$, -9.6% at 28, -13.0% at 24, -17.8% at 20. It shrinks with the fill of the stack, since a partly filled stack already sends only its data rows: at 40 of 64 rows, -4.6% at $\mu = 26$ and -2.4% at $\mu = 30$. `RESIDUAL_MAX_LOG = 5 <= INITIAL_FOLDING_FACTOR` still holds. Going to 16 lanes does not pay at equal encoding cost, and 128 lanes loses on bytes and cycles.

### 4.4 Later folds and reductions

| $\mu = 30$, rate 1/2 | queries | bytes | guest Keccak | NTT work |
| --- | --- | --- | --- | --- |
| $k = 3$, $r = 1$ | 218 55 37 28 23 19 17 15 | +5.1% | +11.2% | x1.02 |
| $k = 4$, $r = 0$ | 218 55 28 19 16 14 | -0.8% | -1.4% | x1.52 |
| $k = 4$, $r = 1$ (today) | 218 55 32 23 18 15 | | | |
| $k = 4$, $r = 2$ | 218 55 37 28 23 20 | +2.0% | +2.0% | x0.90 |
| $k = 5$, $r = 1$ | 218 55 28 19 16 | +2.2% | -4.2% | x0.98 |
| $k = 5$, $r = 2$ | 218 55 32 23 18 | +3.8% | -3.6% | x0.90 |

The deployed pair is the byte optimum at its encoding cost. `SUBSEQUENT_FOLDING_FACTOR = 5` is the Keccak optimum: one level fewer, 4 to 7% fewer permutations for 2 to 3% more bytes at every size tried, and its 64-word leaves are exactly `MAX_LEAF_WORDS`. Ladders with a different fold or reduction at level 1 than later (54 combinations around each of $k_0 = 5$ and $k_0 = 6$, kept when within 1.06x encoding) found nothing better than the uniform ones.

### 4.5 Where the ladder stops

With `RESIDUAL_MAX_LOG = 5` and folds of 4, a stack with $\mu \equiv 0 \pmod 4$ ends on a level with $\kappa = 2$: four coefficients a lane, analysed at degree 7, 14 to 27 queries into a tree of $2^{12}$ to $2^{21}$ leaves, to avoid sending 64 coefficients. `RESIDUAL_MAX_LOG = 6`, which the existing assertion `RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR` admits, stops one level earlier at exactly those sizes and changes nothing at the others:

| | rate 1/2 | 1/4 | 1/8 | 1/16 |
| --- | --- | --- | --- | --- |
| $\mu = 20$: bytes, guest Keccak | -5.5%, -5.3% | -8.3%, -8.2% | -10.2%, -12.4% | -11.4%, -13.4% |
| $\mu = 24$ | -4.1%, -5.1% | -6.0%, -6.3% | -7.4%, -7.6% | -8.4%, -8.6% |
| $\mu = 28$ | -3.2%, -3.4% | -4.8%, -5.1% | -6.1%, -7.2% | -6.8%, -7.3% |

The prover commits one level less and skips its OOD and query grinds; guest cycles are unchanged within 1.5% (**estimate**: the final queries evaluate 68 coefficients instead of 8). A residual of 8 would save about 2% of bytes and 3% of Keccak at $\mu = 30$ too, but it breaks the guest's point rotation (`residual > k_0`) and costs about 4% of query cycles (**estimate**).

### 4.6 The level-0 rate

| $\mu = 30$ | queries | bytes | guest Keccak | NTT work | words |
| --- | --- | --- | --- | --- | --- |
| rate 1/2 | 218 55 32 23 18 15 | 335.9 KiB | 8173 | x1.00 | x1.00 |
| rate 1/4, $r_0 = 5$ | 109 73 37 25 19 16 | 246.8 KiB (-26.5%) | 6738 | x1.58 | |
| rate 1/4, $r_0 = 4$ | 109 55 32 23 18 15 | 232.1 KiB (-30.9%) | 6291 | x1.75 | x1.67 |
| rate 1/4 | 109 44 28 21 17 15 | 222.6 KiB (-33.7%) | 6000 | x2.08 | x2.00 |
| rate 1/8 | 73 37 25 19 16 15 | 180.7 KiB (-46.2%) | 4914 | x4.33 | x4.00 |
| rate 1/16 | 55 32 23 18 16 14 | 158.7 KiB (-52.8%) | 4318 | x8.98 | x8.00 |

Across all rates the deployed ladders sit 0 to 8% above the lower envelope of bytes against encoding work, most at rate 1/2, and the gap is the 32-lane point of section 4.3. Extra encoding spent on the ladder (lower reductions) is dominated by the next rate. The row $r_0 = 4$ is rate 1/4 at level 0 over the later levels of rate 1/2: it gives 92% of rate 1/4's saving for 70% of its extra encoding.

## 5. Pareto fronts

`explore.py pareto` evaluates, for $\mu \in \{20, 24, 28, 30\}$ and each rate, 171 ladders ($k_0 \in 4..7$, $r_0 \in 1..5$, later folds 3 to 5, later reductions 0 to 2) under 17 grind profiles (level-0 query grind 17 to 28, four of them also with batch 14 and OOD 16, two with level 1 raised, two with every level raised): 46,512 configurations, 44,897 feasible. `fronts.py` extracts the front in (bytes, guest Keccak, expected grind permutations, NTT work); it has 371 to 777 points per (size, rate), because grind and encoding are near-continuous axes. Its shape is simple and the same everywhere:

- Along the grind axis every front point puts the query grind on level 0 alone, sometimes with batch 14 and OOD 16.
- Along the encoding axis, at today's encoding (x1.05 or less) the byte-optimal ladder is $k_0 = 5$, $r_0 = 3$ with the deployed later levels, at every size and rate; the Keccak-optimal one has later folds of 5 (with $k_0 = 6$ in 15 of the 16 cases); the best for recursion cost (cycles plus 8 a KECCAK step, **estimate**) is $k_0 = 5$ with later folds of 4 or 5, in 15 of the 16 cases.
- With 1.4x encoding the byte optimum moves to $r_0 = 2$ with $k_0 = 5$ or 4 (-16.4% at $\mu = 30$, -17.8% at $\mu = 24$, rate 1/2, with the level-0 grind), which the next rate beats.

Best points under a few prover budgets, rate 1/2 (bytes, guest Keccak; today's encoding means NTT work at most x1.05; the grind budget of the third and later rows is today's plus $2^{\max(17, \mu - 6)} + 2^{18}$ permutations):

| | $\mu = 20$ | $\mu = 24$ | $\mu = 28$ | $\mu = 30$ |
| --- | --- | --- | --- | --- |
| today | 210.1 KiB, 5044 | 260.4 KiB, 5748 | 313.7 KiB, 7883 | 335.9 KiB, 8173 |
| today's encoding and grind, least bytes | 172.7 (-17.8%), 4924 | 226.0 (-13.2%), 5763 | 283.0 (-9.8%), 7985 | 307.6 (-8.4%), 8388 |
| today's encoding, the grind budget, least bytes | 171.0 (-18.6%), 4867 | 224.3 (-13.9%), 5720 | 275.4 (-12.2%), 7763 | 297.1 (-11.6%), 8101 |
| same budget, least Keccak | 180.3 (-14.2%), 4394 (-12.9%) | 265.4 (+1.9%), 5456 (-5.1%) | 311.2 (-0.8%), 7294 (-7.5%) | 327.9 (-2.4%), 7478 (-8.5%) |
| encoding x1.4, same budget, least bytes | 157.5 (-25.0%), 4768 | 214.0 (-17.8%), 5428 | 261.3 (-16.7%), 7726 | 280.8 (-16.4%), 7613 |

The grid kept `RESIDUAL_MAX_LOG` at $\min(5, k_0)$; section 4.5's change composes with any $k_0 = 6$ point.

## 6. Recommended configurations

- **A, constants only.** The deployed ladder with `RESIDUAL_MAX_LOG = 6`, a level-0 query grind of $\max(17, \mu - 6)$ bits (every other query message stays at 17), `BATCH_GRINDING_BITS = 14` and `OOD_GRINDING_BITS = 16`. It changes three constants, makes a fourth (the query grind) depend on the level and the stacked size, and regenerates `WHIR_QUERIES`; no shape changes except that sizes $\mu \equiv 0 \pmod 4$ lose their last level.
- **B, 32 lanes.** `INITIAL_FOLDING_FACTOR = 5` with `RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3` and every grind as deployed. A shape change in both provers, the three verifiers and `formal/`.
- **C.** B with A's grinds (the residual cap stays 5, as $k_0 = 5$ requires).

Encoding relative to today: A x1.00 (x0.96 to x0.99 where a level is dropped); B and C x1.02 to x1.05 NTT work and x1.13 Merkle permutations, both from level 0 alone (one more NTT layer over the same words; 3 permutations per 256 committed bytes instead of 5 per 512). Grind time on one thread at 15 M permutations a second is $2^{x}/15\mathrm{M}$: 0.04 to 0.07 s today, and with A 0.04 s at $\mu = 20$, 0.06 s at 24, 0.34 s at 28, 1.19 s at 30.

| $\mu$ | rate | config | queries per level | WHIR bytes (KiB) | guest Keccak | native Keccak | guest query cycles (est.) | grind ($\log_2$ perms) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 20 | 1/2 | today | 219 55 33 27 | 210.1 | 5044 | 6072 | 123.0k | 19.34 |
| 20 | 1/2 | A | 219 55 33 | 198.5 (-5.5%) | 4778 (-5.3%) | 5690 (-6.3%) | 123.4k (+0.3%) | 19.21 |
| 20 | 1/2 | B | 218 74 38 28 | 172.7 (-17.8%) | 4924 (-2.4%) | 6232 (+2.6%) | 99.0k (-19.5%) | 19.34 |
| 20 | 1/2 | C | 218 74 38 28 | 172.7 (-17.8%) | 4924 (-2.4%) | 6232 (+2.6%) | 99.0k (-19.5%) | 19.62 |
| 20 | 1/4 | today | 109 44 29 24 | 135.2 | 3190 | 3895 | 69.9k | 19.34 |
| 20 | 1/4 | A | 109 44 29 | 124.1 (-8.3%) | 2930 (-8.2%) | 3531 (-9.3%) | 70.2k (+0.4%) | 19.21 |
| 20 | 1/4 | B | 109 55 32 25 | 118.5 (-12.4%) | 3198 (+0.2%) | 4040 (+3.7%) | 59.1k (-15.5%) | 19.34 |
| 20 | 1/4 | C | 109 55 32 25 | 118.5 (-12.4%) | 3198 (+0.2%) | 4040 (+3.7%) | 59.1k (-15.5%) | 19.62 |
| 20 | 1/8 | today | 73 37 25 22 | 107.8 | 2539 | 3115 | 51.4k | 19.34 |
| 20 | 1/8 | A | 73 37 25 | 96.9 (-10.2%) | 2224 (-12.4%) | 2759 (-11.4%) | 50.8k (-1.1%) | 19.21 |
| 20 | 1/8 | B | 73 44 28 23 | 97.4 (-9.6%) | 2578 (+1.5%) | 3237 (+3.9%) | 44.5k (-13.4%) | 19.34 |
| 20 | 1/8 | C | 73 44 28 23 | 97.4 (-9.6%) | 2578 (+1.5%) | 3237 (+3.9%) | 44.5k (-13.4%) | 19.62 |
| 20 | 1/16 | today | 55 32 23 20 | 93.4 | 2172 | 2707 | 41.2k | 19.34 |
| 20 | 1/16 | A | 55 32 23 | 82.7 (-11.4%) | 1881 (-13.4%) | 2363 (-12.7%) | 40.8k (-1.1%) | 19.21 |
| 20 | 1/16 | B | 55 37 25 20 | 85.2 (-8.8%) | 2203 (+1.4%) | 2788 (+3.0%) | 35.8k (-13.1%) | 19.34 |
| 20 | 1/16 | C | 55 37 25 20 | 85.2 (-8.8%) | 2203 (+1.4%) | 2788 (+3.0%) | 35.8k (-13.1%) | 19.62 |
| 24 | 1/2 | today | 218 55 32 23 20 | 260.4 | 5748 | 7684 | 135.5k | 19.66 |
| 24 | 1/2 | A | 215 55 32 23 | 247.4 (-5.0%) | 5408 (-5.9%) | 7270 (-5.4%) | 133.5k (-1.4%) | 19.84 |
| 24 | 1/2 | B | 218 73 37 25 20 | 226.6 (-13.0%) | 5778 (+0.5%) | 7964 (+3.6%) | 112.8k (-16.7%) | 19.66 |
| 24 | 1/2 | C | 215 73 37 25 20 | 224.9 (-13.6%) | 5734 (-0.2%) | 7897 (+2.8%) | 111.7k (-17.5%) | 20.11 |
| 24 | 1/4 | today | 109 44 28 21 18 | 169.9 | 4318 | 5012 | 80.7k | 19.66 |
| 24 | 1/4 | A | 108 44 28 21 | 158.9 (-6.5%) | 4025 (-6.8%) | 4659 (-7.0%) | 79.8k (-1.1%) | 19.84 |
| 24 | 1/4 | B | 109 55 32 23 19 | 156.7 (-7.8%) | 4373 (+1.3%) | 5276 (+5.3%) | 71.0k (-12.0%) | 19.66 |
| 24 | 1/4 | C | 108 55 32 23 19 | 156.1 (-8.1%) | 4352 (+0.8%) | 5252 (+4.8%) | 70.6k (-12.5%) | 20.11 |
| 24 | 1/8 | today | 73 37 25 19 17 | 136.8 | 3524 | 4050 | 60.2k | 19.66 |
| 24 | 1/8 | A | 72 37 25 19 | 125.8 (-8.1%) | 3234 (-8.2%) | 3697 (-8.7%) | 59.2k (-1.7%) | 19.84 |
| 24 | 1/8 | B | 73 44 28 21 17 | 128.4 (-6.1%) | 3607 (+2.3%) | 4239 (+4.7%) | 54.0k (-10.3%) | 19.66 |
| 24 | 1/8 | C | 72 44 28 21 17 | 127.8 (-6.6%) | 3587 (+1.8%) | 4215 (+4.1%) | 53.7k (-10.9%) | 20.11 |
| 24 | 1/16 | today | 55 32 23 18 16 | 119.4 | 3082 | 3549 | 49.4k | 19.66 |
| 24 | 1/16 | A | 54 32 22 18 | 107.8 (-9.8%) | 2775 (-10.0%) | 3177 (-10.5%) | 48.2k (-2.4%) | 19.84 |
| 24 | 1/16 | B | 55 37 25 19 16 | 112.8 (-5.6%) | 3148 (+2.2%) | 3679 (+3.7%) | 44.7k (-9.6%) | 19.66 |
| 24 | 1/16 | C | 54 37 25 19 16 | 112.0 (-6.2%) | 3128 (+1.5%) | 3654 (+3.0%) | 44.3k (-10.3%) | 20.11 |
| 28 | 1/2 | today | 218 55 32 23 18 16 | 313.7 | 7883 | 9409 | 155.3k | 19.92 |
| 28 | 1/2 | A | 207 55 32 22 18 | 293.0 (-6.6%) | 7354 (-6.7%) | 8764 (-6.9%) | 148.7k (-4.3%) | 22.27 |
| 28 | 1/2 | B | 218 73 37 25 19 16 | 283.7 (-9.6%) | 8005 (+1.5%) | 9813 (+4.3%) | 134.3k (-13.5%) | 19.92 |
| 28 | 1/2 | C | 207 73 37 25 19 16 | 276.1 (-12.0%) | 7783 (-1.3%) | 9525 (+1.2%) | 129.9k (-16.4%) | 22.33 |
| 28 | 1/4 | today | 109 44 28 21 17 15 | 207.7 | 5213 | 6235 | 91.7k | 19.92 |
| 28 | 1/4 | A | 104 44 28 21 17 | 193.0 (-7.1%) | 4839 (-7.2%) | 5775 (-7.4%) | 88.6k (-3.4%) | 22.27 |
| 28 | 1/4 | B | 109 55 32 23 18 15 | 196.8 (-5.3%) | 5414 (+3.9%) | 6571 (+5.4%) | 83.0k (-9.5%) | 19.92 |
| 28 | 1/4 | C | 104 55 32 22 18 15 | 192.3 (-7.4%) | 5292 (+1.5%) | 6412 (+2.8%) | 80.8k (-12.0%) | 22.33 |
| 28 | 1/8 | today | 73 37 25 19 16 15 | 168.9 | 4283 | 5088 | 69.1k | 19.92 |
| 28 | 1/8 | A | 70 37 25 19 16 | 155.5 (-7.9%) | 3908 (-8.8%) | 4666 (-8.3%) | 66.5k (-3.7%) | 22.27 |
| 28 | 1/8 | B | 73 44 28 21 17 15 | 162.7 (-3.7%) | 4748 (+10.9%) | 5353 (+5.2%) | 65.4k (-5.4%) | 19.92 |
| 28 | 1/8 | C | 70 44 28 21 17 15 | 160.3 (-5.1%) | 4669 (+9.0%) | 5268 (+3.5%) | 64.1k (-7.2%) | 22.33 |
| 28 | 1/16 | today | 55 32 23 18 15 14 | 147.9 | 3975 | 4472 | 57.9k | 19.92 |
| 28 | 1/16 | A | 52 32 23 18 15 | 134.6 (-9.0%) | 3599 (-9.5%) | 4055 (-9.3%) | 55.4k (-4.4%) | 22.27 |
| 28 | 1/16 | B | 55 37 25 19 16 14 | 142.9 (-3.3%) | 4062 (+2.2%) | 4658 (+4.2%) | 53.8k (-7.2%) | 19.92 |
| 28 | 1/16 | C | 52 37 25 19 16 14 | 140.4 (-5.0%) | 3983 (+0.2%) | 4570 (+2.2%) | 52.5k (-9.4%) | 22.33 |
| 30 | 1/2 | today | 218 55 32 23 18 15 | 335.9 | 8173 | 10130 | 161.5k | 19.92 |
| 30 | 1/2 | A | 203 55 32 22 18 15 | 320.6 (-4.6%) | 7820 (-4.3%) | 9668 (-4.6%) | 152.9k (-5.3%) | 24.09 |
| 30 | 1/2 | B | 218 73 37 25 19 16 | 308.3 (-8.2%) | 8409 (+2.9%) | 10621 (+4.8%) | 141.6k (-12.3%) | 19.92 |
| 30 | 1/2 | C | 203 73 37 25 19 16 | 297.1 (-11.6%) | 8101 (-0.9%) | 10197 (+0.7%) | 135.3k (-16.2%) | 24.09 |
| 30 | 1/4 | today | 109 44 28 21 17 15 | 222.6 | 6000 | 6728 | 98.3k | 19.92 |
| 30 | 1/4 | A | 102 44 28 21 17 15 | 215.4 (-3.3%) | 5802 (-3.3%) | 6516 (-3.2%) | 94.3k (-4.1%) | 24.09 |
| 30 | 1/4 | B | 109 55 32 23 18 15 | 213.0 (-4.3%) | 6166 (+2.8%) | 7103 (+5.6%) | 90.3k (-8.2%) | 19.92 |
| 30 | 1/4 | C | 102 55 32 22 18 15 | 206.5 (-7.2%) | 5961 (-0.6%) | 6873 (+2.2%) | 86.9k (-11.6%) | 24.09 |
| 30 | 1/8 | today | 73 37 25 19 16 15 | 180.7 | 4914 | 5482 | 74.6k | 19.92 |
| 30 | 1/8 | A | 68 37 25 19 16 14 | 174.6 (-3.4%) | 4752 (-3.3%) | 5301 (-3.3%) | 71.4k (-4.3%) | 24.09 |
| 30 | 1/8 | B | 73 44 28 21 17 15 | 175.5 (-2.9%) | 5093 (+3.6%) | 5772 (+5.3%) | 70.0k (-6.2%) | 19.92 |
| 30 | 1/8 | C | 68 44 28 21 17 14 | 170.5 (-5.7%) | 4941 (+0.6%) | 5596 (+2.1%) | 67.4k (-9.6%) | 24.09 |
| 30 | 1/16 | today | 55 32 23 18 16 14 | 158.7 | 4318 | 4832 | 62.0k | 19.92 |
| 30 | 1/16 | A | 51 32 23 18 15 14 | 153.4 (-3.3%) | 4183 (-3.1%) | 4676 (-3.2%) | 59.4k (-4.1%) | 24.09 |
| 30 | 1/16 | B | 55 37 25 19 16 15 | 154.5 (-2.7%) | 4457 (+3.2%) | 5039 (+4.3%) | 58.6k (-5.5%) | 19.92 |
| 30 | 1/16 | C | 51 37 25 19 16 14 | 150.1 (-5.4%) | 4331 (+0.3%) | 4889 (+1.2%) | 56.5k (-8.8%) | 24.09 |

At 40 of 64 data rows (the fill of the 900-XMSS proof), rate 1/2, bytes only: A -5.7%, -2.2%, -6.8%, -4.2% and B -6.1%, -4.6%, -3.5%, -2.4% and C -6.7%, -6.2%, -5.9%, -5.8% at $\mu = 24, 26, 28, 30$ (**exact**). Keccak and cycles do not depend on the fill: the guest hashes and folds whole leaves.

How to choose. A is free of trade-offs and should be taken first; its grind schedule is the only part that costs anything, and it can be made gentler ($\mu - 7$) or steeper ($\mu - 4$) at 2 queries a bit. B is worth its shape change if recursion cycles or full-stack proof size matter more than the Keccak count, and not otherwise: with A's residual change on the deployed ladder, A beats B on bytes at 62% fill for $\mu = 28$ and ties it at $\mu = 24$. If the Keccak count is the objective, `SUBSEQUENT_FOLDING_FACTOR = 5` (section 4.4) and the cap rule (section 8.1) are the levers, not the lanes.

## 7. Slack in the proven bound

### 7.1 Against the Johnson limit

Total queries of an opening, deployed against the Johnson limit of section 3 (**exact**):

| | $\mu = 20$ | $\mu = 24$ | $\mu = 28$ | $\mu = 30$ |
| --- | --- | --- | --- | --- |
| rate 1/2 | 334 / 328 | 348 / 343 | 362 / 357 | 361 / 356 |
| rate 1/4 | 206 / 203 | 220 / 218 | 234 / 231 | 234 / 230 |
| rate 1/8 | 157 / 155 | 171 / 170 | 185 / 182 | 185 / 182 |
| rate 1/16 | 130 / 126 | 144 / 140 | 157 / 151 | 158 / 151 |

So every refinement of the list side together (tighter batching than $(J_0 - 1) L$ with $J_0 = 514$, a second OOD point, a larger `MAX_LIST_0`, exact rather than floored Johnson counts) is worth at most 1 to 7 queries, almost all of them on the cheap last levels. At level 0 the gap is one query at rate 1/2 (two at $\mu = 20$) and zero at the other rates.

### 7.2 The terms the brief names

Each variant is the model with one hypothesis relaxed, to price it; none is a proof.

- **Degree slack $d = 2^\kappa - 1 + \ell$ and the loss of one point a round.** Analysing every round at $d = 2^\kappa - 1$ and at the level's final threshold changes the query counts at 23 of 32 shapes tried (rates 1/2 to 1/16, $\mu = 16, 18, \dots, 30$). Above $\mu = 20$ it is at most one query in total, on the last level, where $2^\kappa$ is 4 to 16 and $\ell = 4$. At $\mu = 20$ it is 1 to 3 queries on the last two levels, and at $\mu = 16$, rate 1/2, it is 5, 2 and 5 queries on the three levels. **Conjectured**: the degree slack cannot be removed by an elementary argument, since the folded word really is close to polynomials of degree $2^\kappa - 1 + \ell$ and the query phase compares against one. Stopping the ladder before the degenerate level (section 4.5) recovers more than this slack would.
- **Sampling with replacement.** The protocol samples i.i.d., so $((A-1)/n)^t$ is exact for it. Sampling distinct positions instead (a protocol change; **exact** with $\prod_{i<t} (A - 1 - i)/(n - i)$ in place of the power) saves 24 queries at $\mu = 16$, rate 1/2, at most 2 at $\mu = 20$, and one query at 2 of the 40 shapes above $\mu = 20$.
- **The batching row inside a query message**, $(t + 1) L_{i+1} / |E|$: at the deployed constants it uses at most 3.7% of the message's budget, and removing it changes no count at any level of the 60 shapes (**exact**). It becomes material only when the later lists are allowed to grow (section 4.2).
- **Implementation conservatism.** Dropping the `u128` overflow-as-failure rule, raising `MAX_MULTIPLICITY` from $2^{16}$ to $2^{22}$, or giving the fold round an unlimited budget changes no query count at any of the 32 shapes (and no list for the first two).

### 7.3 A finite-size floor in the interpolation inequality

**Checked numerically** (`interp_floor.py`, 16 level shapes from $n = 2^{11}$ to $2^{28}$): inequality (4.5) of [CWYZ26, Lemma 4.2] has no solution $(m, D)$ with $m \le 2^{16}$ unless $A \ge \sqrt{n d} + c \sqrt{n}$, with $c$ between 0.45 and 0.47 at rate 1/2 (seven sizes from $2^{11}$ to $2^{25}$), 0.60 at rate 1/4, 0.71 to 0.74 at 1/16, and rising to about 1.0 at the lowest rates. Raising the multiplicity cap to $2^{22}$ moves no threshold at the 32 shapes of section 7.2. A heuristic reason (not proved) is the shape of the monomial set: the $X$-degree budget is $mA - D$, which costs $D/m$ points of agreement, while the $(Y, Z)$ simplex of side $D$ loses a fraction of order $m/D$ of its monomials, and balancing the two leaves a relative loss of order $1/\sqrt{A}$. Relative to $n$ this floor is $\eta \ge c/\sqrt{n}$, against the list-budget $\eta \approx (1 - \sqrt\rho)/(2L)$: it binds once $n \lesssim 2^{17}$, which is level 0 for $\mu \le 22$ and the last one or two levels for $\mu \le 24$. At $\mu = 16$, rate 1/2, level 0 is 12 queries above its Johnson limit, of which the variants of section 7.2 explain 5 and this floor the rest; at $\mu = 20$ it costs level 0 one or two queries, and the last levels of $\mu \le 24$ two or three. **Conjectured**: a different monomial support in Lemma 4.2 (a box rather than a simplex in $(Y, Z)$) would lower $c$; this is a change to the cited lemma, not an elementary tightening, and at the sizes real proofs use it is worth at most the 2 to 3 last-level queries.

## 8. Side findings

### 8.1 The guest's Merkle cap rule costs up to a fifth of its Merkle hashes

`merkle_cap_depth` keeps the walked part of a path a whole number of 6-bit windows, so the cap depth is the tree depth modulo 6, between 2 and 8 whatever the query count. When it comes out at 2 to 4 on level 0 (218 queries), about four levels of every path are hashed query by query that a deeper cap would hash once. Expected Merkle permutations of the guest with the deployed rule against a cap of 8 levels at every level (**exact** expectations; the cap's extra cycles are not counted):

| rate 1/2, $\mu$ | 20 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| deployed rule | 4886 | 5098 | 5143 | 5540 | 5708 | 7071 | 7237 | 7620 | 7734 | 7891 |
| level-0 cap depth | 3 | 5 | 6 | 7 | 8 | 3 | 4 | 5 | 6 | 7 |
| cap 8 everywhere | 3809 | 4422 | 4740 | 5325 | 5660 | 5994 | 6340 | 6944 | 7290 | 7651 |
| change | -22.0% | -13.3% | -7.8% | -3.9% | -0.8% | -15.2% | -12.4% | -8.9% | -5.7% | -3.0% |

`walk_path` already has arms for a partial last window (widths 1 to 5). **Conjectured**: `decode_query_windows` and the hint layout can follow, which someone who knows the guest should confirm. This also means that Keccak counts compared across shapes carry a lottery of several percent; section 6's table quotes the native count next to the guest's for that reason.

### 8.2 The Rust bisection assumes a monotone predicate that is not always monotone

In 16 of the 720 cross-check derivations, all with an OOD grind of 17 or more, the Rust's bisection over the full predicate and a search that starts from the least threshold clearing the list terms end on different thresholds, in either direction. In the one case examined (rate 1/16, $\mu = 28$, level 1, lanes 5, $r_0 = 2$, fold grind 6, OOD grind 17; **checked numerically**, every threshold between the two answers) the Rust's answer is followed by 1556 feasible thresholds, then 402 infeasible ones, then feasible ones again: the fold round's check is made against the witness with the least $m$ and its least $D$, which jumps as the threshold moves, so feasibility is not monotone in $t_{\mathrm{end}}$ and a bisection returns a feasible threshold that need not be the least. The two answers are $3 \cdot 10^{-5}\,n$ apart there and no query count differs in any of the 16 cases; `validate` rechecks the returned threshold; and it does not happen at the deployed constants (the two searches agree at all 60 shapes). Worth knowing before raising the OOD grind.

### 8.3 Smaller items

- Query positions travel in the proof, 4 bytes each: 1.4 KiB of 336 at $\mu = 30$. The verifier derives them from the transcript and only compares.
- A later-level grind change is not worth a constant: 28 bits on levels 1 to 5 save 15 queries for $5 \cdot 2^{28}$ permutations.

## 9. Reproducing

Everything is under `doc/whir_soundness_gap_notes/scripts/08_retuning/`, standard library only, seconds each on four cores.

| script | what it does |
| --- | --- |
| `whir_model.py` | the port: `derive(mu, rate, Knobs(...))` |
| `validate.py` | against `WHIR_QUERIES`, read from `crates/verifier/src/whir.rs` |
| `crosscheck.sh [DIR]`, `crosscheck.py` | the Rust search recompiled at other constants in a scratch crate outside the repository, against the model |
| `costs.py` | bytes, Keccak, grinding, encoding, the guest-cycle estimate |
| `explore.py sweeps`, `pareto OUT.json`, `slack` | section 4, the grid of section 5, section 7.2 |
| `fronts.py OUT.json` | the fronts and the budget tables of section 5 |
| `recommend.py [--fill F] [--extra]` | section 6 |
| `interp_floor.py` | section 7.3 |

The measured inputs came from `./target/release/leanvm-bench --prover experimental --threads 4 [--log-inv-rate R] [--tracing] aggregate --xmss 100|900`, the same with `recursion --n 2 --xmss-per-leaf 100` and `DBG_PROF=1`, and a single-threaded loop over `keccak256::first_nonce` in a scratch crate.
