# 71. Tree codes at level 0: protocol changes, guest and prover cost, payoff

Researcher 71, round 15, 2026-11-21. Status tags used throughout: **checked** (read off the code, file and line given), **exact** (exact in the stated model), **measured** (a number measured by an earlier note or by a script here), **estimate**. Scripts: `scripts/71_*`.

## Summary

**Section 1 of note 68 is half right, a tree code is cheap for the prover and costs the guest 5 to 10 percent a level-0 query, and it becomes a clear win over configuration C from $L = 3$ with $\varepsilon \le 2/64$ at rate 1/2 and from $L = 8$ at rate 1/4; but it forces a scalar fold at level 0, and that breaks the efficient extractor `formal/` proves today.** In detail. (1) Level 0's evaluation set is free for ring switching, the stacked opening, the rotation of the terminal point, the batching of query claims and the final check (**checked**), but note 68's claim that level 0's fold is a linear combination of lanes is wrong: level 0 folds with the affine combiner $G + (\alpha + \beta X) F$ like every level, reads the column's point, sends a high part, and its soundness is a correlated agreement theorem for Reed-Solomon codes (**checked**: `crates/verifier/src/whir.rs:173-183`, `:244-251`, `:304-319`). A tree code is not closed under multiplication by a column label, so level 0 must fold with a scalar; that has no proof in today's analysis and works only inside the DEEP fold, with a class lemma of its own (sketched in section 4.2, not refereed), 8 or 9 points instead of 10 to 12, and a loss of $n_0/2^{13}$ columns a round paid by a 12-bit fold grind. (2) Prover (**estimate**, not implemented): the network is today's in variant T1, the twiddles are a table of one sixty-fourth of the codeword or $n_0/15$ permutations, and proving time moves by less than one percent either way, plus about 1.5 percent for the DEEP fold's points; T2 doubles the butterflies' products. (3) Guest (**estimate**): 3 to 5 more permutations and 30 to 60 more cycle-equivalents a level-0 query (5 to 10 percent) if the derivation rides the path windows and the top layers come from a table built once per opening; note 68's version is 13 to 17 percent, mostly because exposing a lane of a permutation's output costs 1.5 cycles, which note 68 did not count. (4) Payoff (bytes and Keccak **exact in the model**, cycles estimated): with C's knobs the opening is 1.4 to 1.5 percent of C smaller per 0.01 of $\tau$ at rate 1/2; $L = 3$, $\varepsilon = 2/64$ ($\tau = 0.656$) is 10.6 to 13.2 percent below C with the guest 1 to 5 percent faster, $L = 16$, $\varepsilon = 1/64$ is 24 to 27 percent below C (164.0, 206.8, 226.2 KiB at $\mu = 24, 28, 30$ against C's 224.9, 276.1, 297.1 and today's 260.4, 313.7, 335.9); at rate 1/4 the win starts at $L = 8$ ($\tau \le 0.40$, 12 to 20 percent); $L = 2$ never pays; without C's knobs the tree code needs $L = 8$. (5) What the lead has not seen (section 6.1): the knowledge extractor descends from the final polynomial by interpolating with at most one error; a tree code has no fast erasure decoder and cannot be decoded with the wrong columns a scalar fold lets through with probability $n_0/q$, so knowledge soundness at 125 bits needs fold grinds of $\log_2 n_0 - 2$ bits (an estimated 4 to 11 percent of proving time) and a linear-algebra decoder proved for the cost machine, or it drops to about 122 bits. (6) If the theorem comes, build the hybrid of section 5.4: tree code and DEEP fold at level 0 only, today's protocol after it; it is 1.5 to 5.5 points larger than the DEEP fold everywhere and 2 to 7 points cheaper for the guest.

### The payoff at a glance

Opening in KiB, guest Keccak count and guest cycle-equivalents (thousands) of the WHIR opening, full stack. "DEEP at every level" is the tree code at level 0 with note 67's proven DEEP-fold levels after it; "hybrid" is section 5.4. A clear win is more than ten percent below C on bytes at all three sizes with the guest not slower at any. Sections 5.2 and 5.3 have the configuration without C's knobs and one table per size.

| rate | config | $\mu = 24$ | $\mu = 28$ | $\mu = 30$ |
| --- | --- | --- | --- | --- |
| 1/2 | today | 260.4 KiB, 5748 Keccak, 181.4k | 313.7 KiB, 7883 Keccak, 218.4k | 335.9 KiB, 8173 Keccak, 226.9k |
| 1/2 | C | 224.9 KiB, 5734 Keccak, 157.6k | 276.1 KiB, 7783 Keccak, 192.1k | 297.1 KiB, 8101 Keccak, 200.1k |
| 1/4 | today | 169.9 KiB, 4318 Keccak, 115.2k | 207.7 KiB, 5213 Keccak, 133.4k | 222.6 KiB, 6000 Keccak, 146.3k |
| 1/4 | C | 156.1 KiB, 4352 Keccak, 105.4k | 192.3 KiB, 5292 Keccak, 123.1k | 206.5 KiB, 5961 Keccak, 134.6k |

**Rate 1/2** (tree code with C's knobs; KiB, Keccak, cycle-eq in thousands at $\mu = 24, 28, 30$; percent against C)

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ | DEEP at every level: KiB | Keccak | cycle-eq | bytes % | guest % | hybrid: KiB | bytes % | guest % | clear win (DEEP / hybrid) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.682 | 195, 188, 184 | 205.6, 256.1, 278.4 | 5854, 8011, 8357 | 158.9, 199.2, 208.9 | -6 to -9 | +4 to +1 | 213.9, 263.3, 283.0 | -5 to -5 | +1 to -1 | no / no |
| 2 | 2/64 | 0.698 | 207, 199, 196 | 212.4, 263.7, 287.5 | 6063, 8277, 8651 | 164.8, 205.9, 216.5 | -3 to -6 | +8 to +5 | 220.7, 270.9, 292.1 | -2 to -2 | +4 to +3 | no / no |
| 2 | 4/64 | 0.729 | 236, 227, 223 | 228.7, 283.0, 307.8 | 6567, 8955, 9313 | 179.1, 222.9, 233.4 | +4 to +2 | +17 to +14 | 237.0, 290.2, 312.4 | +5 to +5 | +13 to +12 | no / no |
| 3 | 1/64 | 0.641 | 167, 161, 158 | 189.6, 237.2, 258.6 | 5364, 7358, 7812 | 145.1, 182.8, 192.4 | -13 to -16 | -4 to -8 | 197.9, 244.4, 263.2 | -11 to -12 | -8 to -10 | yes / yes |
| 3 | 2/64 | 0.656 | 177, 170, 167 | 195.3, 243.5, 265.5 | 5539, 7575, 8043 | 150.0, 188.2, 198.1 | -11 to -13 | -1 to -5 | 203.6, 250.7, 270.1 | -9 to -9 | -5 to -7 | yes / no |
| 3 | 4/64 | 0.688 | 199, 191, 188 | 207.8, 258.2, 281.5 | 5924, 8084, 8455 | 160.9, 201.0, 211.4 | -5 to -8 | +6 to +2 | 216.2, 265.3, 286.1 | -4 to -4 | +2 to +0 | no / no |
| 4 | 1/64 | 0.616 | 154, 148, 145 | 182.1, 228.1, 248.7 | 5136, 7043, 7479 | 138.7, 174.9, 184.0 | -16 to -19 | -8 to -12 | 190.4, 235.3, 253.3 | -15 to -15 | -12 to -14 | yes / yes |
| 4 | 2/64 | 0.631 | 162, 156, 153 | 186.7, 233.7, 254.8 | 5276, 7237, 7684 | 142.6, 179.7, 189.2 | -14 to -17 | -5 to -10 | 195.0, 240.9, 259.4 | -13 to -13 | -9 to -11 | yes / yes |
| 4 | 4/64 | 0.662 | 181, 174, 171 | 197.6, 246.3, 268.6 | 5610, 7672, 8145 | 152.0, 190.7, 200.7 | -10 to -12 | +0 to -4 | 205.9, 253.5, 273.2 | -8 to -8 | -4 to -6 | no / no |
| 8 | 1/64 | 0.571 | 133, 128, 126 | 169.8, 213.9, 234.0 | 4767, 6558, 7551 | 128.3, 162.7, 179.3 | -21 to -24 | -10 to -19 | 178.2, 221.1, 238.6 | -20 to -21 | -14 to -21 | yes / yes |
| 8 | 2/64 | 0.587 | 140, 135, 132 | 173.9, 218.9, 238.6 | 4890, 6727, 7144 | 131.7, 166.9, 175.7 | -20 to -23 | -12 to -16 | 182.3, 226.1, 243.2 | -18 to -19 | -16 to -18 | yes / yes |
| 8 | 4/64 | 0.618 | 155, 149, 146 | 182.6, 228.8, 249.4 | 5154, 7067, 7504 | 139.1, 175.5, 184.7 | -16 to -19 | -8 to -12 | 191.0, 236.0, 254.0 | -14 to -15 | -12 to -14 | yes / yes |
| 16 | 1/64 | 0.545 | 123, 118, 116 | 164.0, 206.8, 226.2 | 5134, 6316, 7238 | 130.5, 156.6, 172.2 | -24 to -27 | -14 to -18 | 172.3, 213.9, 230.8 | -22 to -23 | -18 to -22 | yes / yes |
| 16 | 2/64 | 0.561 | 129, 124, 122 | 167.5, 211.0, 230.9 | 4696, 6461, 7426 | 126.3, 160.3, 176.4 | -22 to -26 | -12 to -20 | 175.8, 218.2, 235.5 | -21 to -22 | -16 to -22 | yes / yes |
| 16 | 4/64 | 0.592 | 142, 137, 134 | 175.1, 220.3, 240.2 | 4925, 6776, 7196 | 132.7, 168.2, 177.0 | -19 to -22 | -12 to -16 | 183.4, 227.5, 244.8 | -18 to -18 | -15 to -18 | yes / yes |

**Rate 1/4** (tree code with C's knobs; KiB, Keccak, cycle-eq in thousands at $\mu = 24, 28, 30$; percent against C)

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ | DEEP at every level: KiB | Keccak | cycle-eq | bytes % | guest % | hybrid: KiB | bytes % | guest % | clear win (DEEP / hybrid) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.516 | 113, 108, 106 | 150.9, 189.4, 205.8 | 4643, 5690, 6466 | 117.7, 140.8, 153.2 | -0 to -3 | +14 to +12 | 159.6, 195.7, 210.1 | +2 to +2 | +8 to +8 | no / no |
| 2 | 2/64 | 0.531 | 118, 114, 111 | 154.0, 193.9, 209.9 | 4759, 5836, 6622 | 120.6, 144.5, 156.7 | +2 to -1 | +17 to +14 | 162.7, 200.2, 214.2 | +4 to +4 | +11 to +10 | no / no |
| 2 | 4/64 | 0.562 | 130, 125, 122 | 161.4, 202.1, 218.8 | 5037, 6104, 6966 | 127.3, 151.2, 164.5 | +6 to +3 | +23 to +21 | 170.1, 208.4, 223.1 | +9 to +8 | +17 to +16 | no / no |
| 3 | 1/64 | 0.453 | 94, 91, 89 | 138.9, 176.6, 191.9 | 4203, 5274, 5935 | 107.1, 130.5, 141.2 | -7 to -11 | +6 to +2 | 147.6, 182.8, 196.2 | -5 to -5 | -1 to -2 | no / no |
| 3 | 2/64 | 0.469 | 99, 95, 93 | 142.1, 179.6, 195.2 | 4319, 5372, 6060 | 109.9, 132.9, 144.0 | -5 to -9 | +8 to +4 | 150.8, 185.9, 199.5 | -3 to -3 | +1 to +0 | no / no |
| 3 | 4/64 | 0.500 | 108, 104, 102 | 147.7, 186.4, 202.6 | 4527, 5592, 6341 | 114.9, 138.4, 150.4 | -2 to -5 | +12 to +9 | 156.5, 192.7, 206.8 | +0 to +0 | +6 to +5 | no / no |
| 4 | 1/64 | 0.416 | 85, 82, 80 | 133.2, 169.7, 184.5 | 4048, 5104, 5653 | 101.9, 124.9, 134.8 | -11 to -15 | +1 to -3 | 141.9, 176.0, 188.8 | -8 to -9 | -5 to -7 | bytes / no |
| 4 | 2/64 | 0.431 | 89, 86, 84 | 135.7, 172.8, 187.8 | 4144, 5206, 5778 | 104.2, 127.4, 137.6 | -9 to -13 | +3 to -1 | 144.5, 179.0, 192.1 | -7 to -7 | -3 to -5 | no / no |
| 4 | 4/64 | 0.463 | 97, 93, 91 | 140.8, 178.1, 193.6 | 4273, 5323, 5997 | 108.7, 131.7, 142.6 | -6 to -10 | +7 to +3 | 149.5, 184.3, 197.8 | -4 to -4 | +0 to -1 | no / no |
| 8 | 1/64 | 0.349 | 71, 68, 67 | 124.2, 159.0, 173.7 | 3709, 4745, 5247 | 93.9, 116.2, 125.6 | -16 to -20 | -6 to -11 | 133.0, 165.2, 178.0 | -14 to -15 | -12 to -15 | yes / yes |
| 8 | 2/64 | 0.365 | 74, 71, 70 | 126.2, 161.3, 176.2 | 3782, 4822, 5341 | 95.6, 118.0, 127.7 | -15 to -19 | -4 to -9 | 134.9, 167.5, 180.5 | -13 to -14 | -11 to -13 | yes / yes |
| 8 | 4/64 | 0.396 | 81, 78, 76 | 130.7, 166.6, 181.2 | 3951, 5001, 5528 | 99.6, 122.4, 132.0 | -12 to -16 | -1 to -5 | 139.4, 172.9, 185.5 | -10 to -11 | -7 to -9 | yes / yes |
| 16 | 1/64 | 0.310 | 64, 62, 60 | 119.7, 154.3, 167.8 | 3540, 4591, 5028 | 89.9, 112.4, 120.7 | -19 to -23 | -9 to -15 | 128.4, 160.6, 172.1 | -16 to -18 | -15 to -19 | yes / yes |
| 16 | 2/64 | 0.325 | 67, 64, 63 | 121.6, 155.9, 170.4 | 3613, 4642, 5122 | 91.6, 113.7, 122.8 | -18 to -22 | -8 to -13 | 130.4, 162.1, 174.6 | -15 to -16 | -14 to -17 | yes / yes |
| 16 | 4/64 | 0.357 | 73, 70, 69 | 125.5, 160.5, 175.4 | 3758, 4796, 5310 | 95.1, 117.4, 127.0 | -15 to -20 | -5 to -10 | 134.2, 166.8, 179.6 | -13 to -14 | -11 to -14 | yes / yes |

## 1. Is Section 1 of note 68 right? Half of it

### 1.1 What is right (checked)

- Level 0's leaf is one point of the domain holding the 64 lane values, one word of $K$ a lane: `crates/verifier/src/whir.rs:14-15` (`INITIAL_FOLDING_FACTOR`), `:259-261` (`leaf_words = lanes` at level 0), `:263-269` (`lanes_of`: level 0's leaf reversed, each word embedded in $E$).
- No fibre of a subspace polynomial is used: level 1's domain is not a quotient of level 0's. Level 1 commits to a fresh encoding of the folded message (Annex B, step 2(a), `body/b-polynomial-commitment-scheme.tex:95`), and a level-0 query is turned into a weighted claim on that message (step 2(e), `:99-106`).
- The claim a query makes is a tensor weight on the folded table: `induced_weight`, `whir.rs:190-203`, evaluates $\prod_k (1 + p_k (1 + \widehat W_k(x_q)))$, the multilinear extension of $\bigotimes_k (1, \widehat W_k(x_q))$ (Annex D, `lem:colweight`).

### 1.2 What is wrong (checked): the fold reads the evaluation point

Note 68 says "Level 0's fold is the linear combination of the lanes with the six sumcheck challenges". It is not. Every level, level 0 included, folds with the affine combiner of [CWYZ26], $P = G + (\alpha + \beta X) F$, where $X$ is the column's evaluation point:

- `whir.rs:166-170` (`FoldRound { alpha, beta }`), `:173-183` (`fold_row(values, x, rounds)` uses `round.alpha + round.beta * x`), called with `x = K(query)` at `:278-279` (final level) and `:315-319` (level 0 and every other level).
- Each round the prover sends four scalars, two of them inner products with $XF$: `whir.rs:244-249` (`claim = u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1))`), Annex B step 1(a) (`body/b-polynomial-commitment-scheme.tex:81`).
- The folded lane has degree $2^{\kappa} - 1 + \ell$, so each level, level 0 included, sends a high part of $\ell$ scalars (`whir.rs:304`) which the verifier removes at each query: `correction = novel_eval(&high, &what) * what[mu]` (`whir.rs:317-319`), Annex B step 2(d).
- The soundness of a fold round is the affine mutual correlated agreement theorem, `thm:mca-affine` of Annex B (`:174`), which is a theorem about Reed-Solomon codes. Annex B's own intuition paragraph (`:121-125`) says why the affine form is there: a scalar fold has error $(n - A + 1)/|E|$ a round.

So level 0 uses three properties of its code, not one: (i) lanes are encoded independently, (ii) a column's row is a tensor $\bigotimes_k (1, x_k)$, and (iii) **the code is closed under multiplication by the column label $X$ up to $\ell$ extra dimensions** (degree $+1$ a round). A tree code has (i) and (ii) and not (iii): for a generic tree code $C$ and any injective label $X$, $C + X C + \dots + X^6 C$ has dimension up to $7k$, so the honest folded word is not a codeword plus a short high part. **A tree code at level 0 forces a scalar fold at level 0**, $P = G + \alpha F$, and with it a different soundness argument for level 0's fold rounds. Sections 4 and 6 give what that costs: it is workable inside the DEEP-fold analysis (a column loss of $n_0/2^{13}$ a round and a 12-bit fold grind in place of 7), and not available at all inside today's Annex B analysis, which needs a correlated agreement theorem for the code.

### 1.3 What does not depend on level 0's code (checked)

- **Ring switching** (`crates/verifier/src/ring_switch.rs`, whole file): acts on claims and weights over the committed table; it needs the table to be $K$-valued and the code to have a generator matrix over $K$ (twiddles in $K$), nothing of the domain. No reference to `Subspace` or to a domain point in the file.
- **The stacked opening's map** (`crates/verifier/src/lib.rs:161-166`, `evaluate_basis`): a weight on the table $f$, evaluated at the terminal point.
- **The rotation of the terminal point** (`whir.rs:292-294`, `point[lane_folds..] ++ point[..lane_folds]`): it says which variables of $f$ are lanes; unchanged.
- **The batching of level-0 query claims into level 1's sumcheck** (`whir.rs:306-335`): unchanged in shape. The weight of query $q$ is still $\lambda^q \bigotimes_k (1, x_k(j_q))$; only the source of the $x_k$ changes.
- **The final check** (`whir.rs:271-299`): it concerns the last level, which stays Reed-Solomon.
- **The commitment's leaf layout and the partly filled stack** (`crates/stable_prover/pcs/src/whir.rs:100-131`): absent lanes are zero codewords under any linear code.
- **The multilinear OOD claim of the commitment** (`crates/verifier/src/lib.rs:171`, `read_ood`): a claim on $f$.

### 1.4 Every place that changes

With a tree code and a scalar fold at level 0 (levels 1 and later untouched):

| where | file and lines | change |
| --- | --- | --- |
| native verifier | `crates/verifier/src/whir.rs:244-251` | level 0's round reads two scalars and one challenge: `claim = u0 + alpha * (u0 + claim + alpha * w)` |
| | `whir.rs:173-183`, `:315-319` | `fold_row` at level 0 without `beta * x`; no `correction` |
| | `whir.rs:304` | no high part after level 0 |
| | `whir.rs:102-137`, `:190-203`, `:256`, `:317` | at level 0, `Subspace::at(x)` is replaced by the leaf's twiddles $x_k(j)$, derived from the oracle (section 2) |
| | `whir.rs:35-48`, `:25-32` | `WHIR_QUERIES` and level 0's grinds |
| guest | `guests/lean_ethereum.py:1402-1403` | `t = coefs[2j] + coefs[2j+1] * x` becomes `t = coefs[j]` at level 0 |
| | `:1460-1477` (`residual_query`), `:1480-1515` | the recurrence on `VANISH_BY_COLS` is replaced by the twiddle derivation of section 2; no `h_high` chain at level 0 |
| | `:1209` (`opening_round`), `:1611-1623`, `:1672-1681` | level 0's round messages, no high part, no `hs` normalizers at level 0 |
| | `:1285-1336` (`walk_window`, `walk_path`), `:856` | the twiddle derivation rides the path windows (section 2) |
| guest constants and witness | `crates/aggregation/src/placeholders.rs:774-780`, `crates/aggregation/src/child.rs` | twiddle tags, top-layer table; the replay stores nothing new (twiddles are public) |
| stable prover | `crates/stable_prover/pcs/src/ntt.rs:94-131` | twiddles from a table or the oracle instead of `standard` and `twiddle` |
| | `pcs/src/whir.rs:105-131`, `:181-200`; `whir_lanes.rs` (all); `xmul.rs` | level 0's commit takes the tree twiddles; level 0's rounds drop the $XF$ projections |
| | `pcs/src/whir_induce.rs:17-43`, `:57` | `induce_basis` takes the queries' twiddles instead of `Subspace::at` |
| experimental prover | `pcs/src/ntt/twiddles.rs:51-132`, `ntt/kernels.rs:356-357`, `:636-680` | byte tables and `radix8` replaced by table reads; the zero-twiddle arm is no longer reached at level 0 |
| | `pcs/src/whir_induce.rs:171-327`, `whir.rs:522`, `whir_lanes.rs`, `xmul.rs` | the transposed NTT's twiddles; level 0's round |
| | `pcs/src/whir_config.rs`, `whir_config/affine_mca.rs` | level 0 leaves the affine MCA search |
| Lean statement | `formal/Statement/LeanVmVerifier.lean:1491-1553` (`subspaceAt`, `foldRow`, `inducedWeight`), `:1614`, `:1638-1665`, `:1671` (`verifyWhir`) | the same edits as the Rust verifier, and the oracle calls that derive twiddles |
| Lean proof | the level-0 fold round of the knowledge soundness proof | today Johnson plus the affine MCA theorem; replaced by section 4's argument and by the tree code's list theorem, which is a statement over the oracle |
| documents | Annex B (`fig:protocol`, `thm:rbr`, `lem:fold-list`), Annex D (`lem:colweight`) | a level-0 variant |

## 2. The level-0 query claim, and the twiddle derivation

### 2.1 The claim today (checked)

A query is a leaf index $j < n_0$, read as the point $x = $ `K(j)` of the domain (the integer's bits are the coordinates in the basis $1, x, x^2, \dots$). The verifier folds the leaf's 64 lanes with the affine combiner at $x$ (`fold_row`), removes the high part, and obtains $c_j = w^{(0)}(x) + \widehat W_\kappa(x) \sum_{s < 6} h_s X_s(x)$. The claim is $\langle W_x, f^{(1)} \rangle = c_j$ on the folded table $f^{(1)}: \{0,1\}^\kappa \to E$, held in **novel-basis coefficient order**, with $W_x(c) = \prod_{k: c_k = 1} \widehat W_k(x)$ (Annex D, `lem:colweight`). The verifier never builds $W_x$: at the terminal point $p$ it evaluates the multilinear extension $\prod_{k<\kappa} (1 + p_k (1 + \widehat W_k(x)))$ (`whir.rs:190-203`; the guest's `residual_query`, `guests/lean_ethereum.py:1460-1477`, computes the same product as $\prod_k (d_k + W_k(x))$ with the unnormalized $W_k$ and the normalizers folded into $d_k$).

The encoder is note 68's butterfly with variant T1, exactly: `forward(u, v, t) = (u + v t, v + u + v t)` (`crates/stable_prover/pcs/src/ntt.rs:33-38`), and the twiddle of a block is $s_i$ at the block's prefix (`ntt.rs:118-131`), so $\widehat W_i(x_j) = t_i(p_i(j)) + j_i$ with $t_i$ an $\mathbb F_2$-linear function of the prefix. The Reed-Solomon code is the tree code whose twiddles are linear in the prefix bits; a random tree code keeps the network and makes them independent.

### 2.2 The claim for a tree code (exact)

Same table, same order, same product: $\langle \bigotimes_k (1, x_k(j)), f^{(1)} \rangle = \mathrm{fold}(\text{leaf } j)$ with $x_k(j) = t_k(p_k(j)) + j_k$ (T1), the fold being scalar (section 1.2) and with no high part to remove. The verifier needs the $\kappa = \mu - 6$ twiddles on the path of $j$, one a layer, and nothing else about the code. The prover's batched weight (`induce_basis`, or the experimental tree's sparse transposed NTT) is the same computation with these twiddles.

### 2.3 Deriving twiddles: what a permutation gives the guest (checked)

- A `KECCAK` step writes the first 1, 2 or 13 cells of the output state, a cell holding two lanes (`crates/isa/src/lib.rs:97-108`, `zkDSL.md:454`). With the sponge's rate, 17 lanes are usable; in the random-permutation model of `formal/`, all 25 of a permutation applied to a tagged input are.
- A twiddle is one lane, in $K$, but the guest reads cells. Exposing a cell's two limbs costs three cycles (`split_limbs`, `guests/lean_ethereum.py:575-583`: a hint, one `XOR`, one `MUL`, and the untaken `JUMP` of `assert_in_k`, `zkDSL.md:401-412`). This is the main bookkeeping cost and note 68 did not count it: 1.5 cycles a lane exposed, and a path uses 4 of the 15 lanes of a four-level subtree, which lie in 3 or 4 different cells.
- The path bits are already available as compile-time constants inside the 64 arms of the Merkle walk's window dispatch (`walk_path`, `:1300-1321`), and the position's masked prefixes are sums of window patterns. So the selection of lanes can be free of runtime indexing if it rides a window dispatch.

### 2.4 Designs

**D1, note 68's (one permutation per four-level subtree, every layer, twiddles stored at query time and read back in the residual pass).** $\lceil \kappa/4 \rceil$ permutations a query: 5 at $\mu = 24$, 6 at $\mu = 28$ and 30.

**D2, recommended.** (a) The layers whose prefix lies inside the Merkle cap (the top `cap_depth` $- r$ layers, 1 to 6 of them), and up to two more so that the rest is a multiple of four, come from a table built once per opening: at most $2^9$ twiddles, 35 permutations, and the partial products $\prod (d_k + x_k)$ over those layers are memoized per table node. (b) The remaining 12 or 16 layers are hashed in four-level subtrees, **inside the residual pass**, in the arms of a dispatch on the path windows the guest already stores (`query_win_ptrs`): an arm knows its bits, so it reads fixed cells, splits them, and multiplies into the running product with no store and no runtime index. Twelve layers are two windows and three subtrees; the middle subtree straddles the windows, which works if its bottom level sits at lanes 8 to 15 so that the two candidates left open by the other window's bit share a cell. 3 permutations a query for 12 layers, 4 for 16.

**Top layers as bytecode constants.** Possible only if the family is nested: key a twiddle by (depth below the root, tree, prefix) in one forest of 16 trees, so that every size and rate shares its top layers. Then one table of at most $2^{c+4}$ words serves all shapes. It buys little: a constant reaching a runtime-indexed table is one `SET` cycle per execution, about what hashing and splitting it costs (35 permutations and 256 splits, about 1000 cycle-equivalents an opening, 5 to 8 a query). Without nesting the tables are 52 shapes times up to 512 words of bytecode, which is not acceptable. Recommendation: nest the family (it costs the theorem a union bound over 52 codes) and build the table at run time.

**T1 against T2.** T2 needs 30 lanes a four-level subtree: two permutations a subtree, or three-level subtrees, either way one third to one half more permutations a query, and it doubles the multiplications of the prover's butterflies. T1 is strictly cheaper everywhere; T2 is worth it only if the list theorem cannot be proved for T1.

**Other groupings considered.** Six-level subtrees aligned with the windows (63 lanes, 4 permutations, a path needs 2 or 3 of them): worse. Twiddles of 32 bits (31 a permutation, five-level subtrees): one fifth fewer permutations, but halves the entropy the list theorem's union bound spends; not assumed. Twiddles affine in the prefix bits within a subtree (10 words instead of 15): this is what makes Reed-Solomon cheap, and it removes the independence of sibling subtrees the proof idea uses; not assumed.

### 2.5 Cost of a level-0 query in the guest (estimate)

Baseline (**measured**, note 08): 478 cycles a level-0 query at $\mu = 23$, of which the residual chain is 92.5 at $\kappa = 17$, and a `KECCAK` step weighs about 8 cycles. Reading `residual_query` (`guests/lean_ethereum.py:1468-1476`) the chain is two `XOR` and two `MUL` a coordinate plus reads shared by the batch of eight, about 4.3 cycles a coordinate, which leaves about 19 for the high part and the two chains; consistent with the measured 92.5.

Instruction counts for design D2, a layer (**estimate**, read off the source, nothing compiled):

| item | cycles a hashed layer | note |
| --- | --- | --- |
| `KECCAK` step, one a four-level subtree | 2.0 (cycle-equivalents) | 8 a step |
| key (masked prefix) and operands | 0.9 | one or two `XOR` and the operand cells a subtree |
| exposing the lanes | 2.6 | 3.5 splits a subtree at 3 cycles |
| product into the running weight | 2.0 | as today; the T1 bit is absorbed by choosing $d_k$ or $d_k + 1$ at compile time |
| window dispatch | 0.5 | two dispatches for twelve layers |
| total | 8.0 | today: 4.3 |

So a hashed layer costs 3.7 cycle-equivalents more than today's recurrence, a table layer about 1 more (one `DEREF`), and the scalar fold gives back about 26 cycles a query (12 for the six $\alpha + \beta x$, 14 for the high part). The script's plan (`scripts/71_tree_level.py`, `twiddle_plan`) picks the number of hashed layers that minimizes the total with the table's cost shared by the queries:

| shape | hashed layers, table | Keccak a query, today to tree (guest) | cycle-equivalents a query, today to tree |
| --- | --- | --- | --- |
| $\mu = 24$, rate 1/2, 64 lanes | 12, $2^7$ | 16 to 19 | 613 to 641 (+4.6%) |
| $\mu = 30$, rate 1/2, 64 lanes | 16, $2^9$ | 22 to 26 | 730 to 780 (+6.8%) |
| $\mu = 24$, rate 1/2, 32 lanes | 12, $2^8$ | 14 to 17 | 461 to 493 (+7.1%) |
| $\mu = 30$, rate 1/2, 32 lanes | 20, $2^6$ | 20 to 25 | 577 to 635 (+10.0%) |
| $\mu = 30$, rate 1/4, 32 lanes | 20, $2^7$ | 26 to 31 | 648 to 709 (+9.3%) |

(The "today" column is note 08's fitted formula plus 8 a `KECCAK` step of the leaf and path, with the cap rule of section 5.) **A tree code costs the guest 3 to 5 more permutations and 30 to 60 more cycle-equivalents a level-0 query, 5 to 10 percent.** For design D1 the same accounting gives 5 or 6 permutations and 85 to 120 cycle-equivalents a query (10.0 a layer: a store and a read back on top of D2's items, and a second window decoding), 13 to 17 percent. For T2 add one permutation a subtree: 9 to 17 percent with D2's layout. The native verifier pays $\lceil \kappa/4 \rceil$ permutations a query on top of $4 + \mathrm{depth}$, about 20 percent more a query.

What is not in these numbers: the bytecode grows by the arms of the dispatch (two or three dispatches of 64 arms, about 30 instructions an arm, per opening shape that differs in path depth), which moves `BYTECODE_LOG` only if it crosses a power of two; not estimated.

## 3. Prover cost (not implemented; checked where a file is cited, otherwise estimate)

**The network is unchanged in T1 (checked).** Both trees run `u' = u + v t; v' = v + u'` on whole rows of 64 lanes under one twiddle a block and a layer (`crates/stable_prover/pcs/src/ntt.rs:33-38`, `:5-9`; `crates/experimental_prover/pcs/src/ntt/kernels.rs:348-352`), and a codeword is $2^r$ copies of the message transformed from layer $r$ on, which is note 68's "the top $r$ bits select a tree". The same `AdditiveNttF64` also encodes levels 1 and later and LeanDA, so the tree twiddles are a second twiddle source for level 0, not a replacement.

**Where twiddles come from today (checked).**

- Stable: `twiddle(layer, block)` is a subset sum of up to `layer` words, recomputed for every block of every pass (`ntt.rs:118-131`, called at `:197`, `:242`). A table read is cheaper than this.
- Experimental: three loads from L1-resident byte tables and two `XOR` (`ntt/twiddles.rs:102-115`); `radix8` gets the seven twiddles of a three-layer group from three lookups by $\mathbb F_2$-linearity in the block index (`:117-132`); and a zero twiddle skips the product (`ntt/kernels.rs:356-357`, `:636-680`). Block 0 of every layer has twiddle zero, so today $2^{1-r}$ layers' worth of butterflies out of $\kappa$ are product-free: 4.2 to 5.6 percent at rate 1/2, half of that at rate 1/4.

**What a tree code changes in the kernels.**

- A table of $n_0 - 2^r$ words, one sixty-fourth of the level-0 codeword: 16 MiB at $\mu = 26$ and rate 1/2, 256 MiB at $\mu = 30$ and rate 1/2, 512 MiB at $\mu = 30$ and rate 1/4. Alternative: store only the layers above the bottom four ($n_0/16$ words) and re-derive a sub-block's bottom twiddles when the deep pass reaches it, $n_0/16$ permutations an encode against the $5 n_0$ of level 0's Merkle tree (4 a leaf, 1 a node), 1.3 percent more hashing (2.1 percent at 32 lanes).
- The cache-tiled passes keep their geometry. A gathered pass reuses one set of $2^g - 1$ twiddles for every residue of a block (`ntt/gathered.rs:33-37`: the block index drops the residue), which holds for any per-block table, and the far layers' twiddles are at most $n_0/2^{11}$ words in all. In the deep pass a sub-block of `L2_WORDS` (`ntt/plan.rs:157-159`) reads its own twiddles, contiguous in a per-layer array, once: 1.6 percent more memory traffic and 1.6 percent less room in the tile. No kernel reads a twiddle per butterfly: one read serves a row pair of 64 lanes.
- `radix8` becomes seven loads. The zero-twiddle arm is never taken at level 0: 4 to 6 percent more products in the level-0 NTT at rate 1/2, 2 to 3 at rate 1/4. (Forcing zero twiddles on tree 0 would keep it and is not a random tree code.)
- The induced weight (`pcs/src/whir_induce.rs:171-327` in experimental, the dense tensors of `crates/stable_prover/pcs/src/whir_induce.rs:17-43` in stable) and the rows rebuilt for an opening (`ntt/openings.rs`) read the same table.
- Level 0's fold rounds lose the $XF$ projections (`whir_lanes.rs`, `xmul.rs`): two of four scalars a round.

**Deriving the table.** One permutation per 15 twiddles (T1): $n_0/15$ permutations, 0.14 M at $\mu = 26$ and 2.2 M at $\mu = 30$ (rate 1/2), which is 9 ms and 150 ms on one thread at the 15 M permutations a second **measured** in note 08 for the grind kernel, less with the multi-way permutation on the pool. Once per (size, rate) and process if the table is kept.

**Proving time (estimate).** Level 0's commitment is 21 percent of `Prove` at $\mu = 26$, rate 1/2 (253 ms of 1.19 s, **measured**, note 08), about half of it the NTT (my split, from $5 n_0$ Merkle permutations). So: lost product-free butterflies +0.4 to +0.6 percent of `Prove`, table traffic +0.2, derivation 0 to +0.3, the $XF$ projections saved (not broken out in any trace I have; under 1 percent). **The tree code itself moves proving time by less than one percent either way in T1.** T2 doubles the butterflies' products: +6 to +10 percent of `Prove`. The DEEP fold's points come on top and are not specific to the tree code: 9 multilinear points at level 0 are 1.6 percent of `Prove` by note 67's formula on note 24's measured kernels (the Reed-Solomon DEEP fold's 11 or 12 points: 2.0 to 2.3), and a multilinear point is exactly today's OOD evaluation, a kernel both trees already have. Grinding: six 12-bit fold grinds at level 0 in place of 7-bit ones, nothing.

## 4. Does the DEEP-fold theorem apply to an abstract level-0 code?

### 4.1 Not as stated, and not because of MDS

Theorem 5.2 of `doc/deep_fold` (`sections/05-soundness.tex:27-44`) asks of a level's code one hypothesis, the list bound $\mathrm{LB}_i(L_i)$ for interleaved words of every lane count. It never uses MDS: the distance enters only the interleaving reduction (Theorem 6.1, any code with an agreement bound) and the uniqueness of the near tuple in the extractor (S2), which need $\tau > \rho + \varepsilon_0$ and nothing more. But the *proof* is written for polynomials and for the affine fold, and uses them in four places that a tree code does not have (**checked** against the paper):

1. the fold $G + (\alpha + \beta X) F$ itself (Definition 2.2), section 1.2 above;
2. the class trichotomy (Lemma 4.5, `sections/04-deep-fold.tex:120-136`): poles, degrees, and "two columns $x \ne x'$ determine $c$";
3. the point functional $\sum_u \theta^{e(u)} U_u(\zeta)$ and its facts (E3), (E4) (Lemma 4.2), which evaluate a univariate polynomial outside the domain;
4. the high part at the level boundary (M3, assumption S1).

### 4.2 The scalar-fold version (proof sketch, not refereed)

Let $C \subseteq E^{n}$ be any $E$-linear code, $w$ an interleaved word, $w_\alpha = w_1 + \alpha w_0$, candidates $(\alpha, P)$ with $P$ in the list of $w_\alpha$ at agreement $t$, at most $Lq$ of them, and the class of a pair of codeword tuples $(F, G)$ the candidates with $P = G + \alpha F$.

- **Determinant lemma.** Unchanged with $a_k = \alpha_k$: two candidates with different challenges lie in exactly one class, and now $F = (P_1 + P_2)/(\alpha_1 + \alpha_2)$ is always a codeword tuple, so cases (a) and (b) of the trichotomy do not exist.
- **Class lemma.** Let $A_{F,G}$ be the columns where $(F, G)$ agrees with $(w_0, w_1)$. A column outside $A_{F,G}$ on which $G + \alpha F$ agrees with $w_\alpha$ determines $\alpha$, so the sets of such columns are disjoint for different members of the class. Hence for every $g \ge 0$ at most $\lfloor n/(g+1) \rfloor$ members have more than $g$ agreement columns outside $A_{F,G}$; for the others $(F, G)$ lies in the list of $w$ at agreement $t - g$ and is a near tuple up to $g$ columns. With $g = 0$ this is the classical $n/q$ of a scalar fold (Annex B's intuition paragraph); the loss $g$ is what buys a small error.
- **Fold round.** As Lemma 4.8 with $M = \max(2, \lfloor n/(g+1) \rfloor)$: condition (p) is one linear equation in $\alpha$ (one root) and condition (w) a quadratic (two roots). Fewer than $K_0$ challenges out of $q$ are bad for any $K_0 > M$ once the points are not exceptional. Thresholds $t^{(0,j)} = t_0 - (\ell_0 - j) g$: a level loses $\ell_0 g$ columns.
- **Points.** A point is a point $z \in E^{\mu}$ and the functional is the multilinear evaluation of the tuple's message table, lanes included; (E1), (E2) (the lane variable folded first splits off linearly), (E3) for scalars are immediate, and (E4) is Schwartz and Zippel with $\varepsilon_p = \mu/q$. Counting is Theorem 4.7 with $|{\rm cand}|^3 \le L^3 q^3$.
- **Rows.** Points: $\binom{L}{2} \varepsilon_p^{\bar s_1} + \frac{L^3 q^3}{\Theta} \sum_j \psi^{-(j-1)} \varepsilon_p^{\bar s_j}$, $\Theta = K_0 (K_0 - 1)(K_0 - M)$. Fold: $(K_0 - 1)/q + \psi$. Queries: $((t_0 + \ell_0 g - 1)/n)^{t} + (\bar s + t)/q$. No high part, so the carried value after the last round is already the weighted claim $\langle \bigotimes_k (1, \zeta_k), f^{(1)} \rangle$.

**Constants.** With a fold grind of $g_f$ bits take $K_0 = 2^{g_f + 2}$, $M = 2^{g_f + 1}$, $\psi = 2^{-(126 - g_f)}$, hence $g = \lceil n / 2^{g_f + 1} \rceil - 1$. At the deployed 7 bits a level of six rounds would lose $6/2^{8} = 2.3$ percent of agreement, more than the $\varepsilon = 1/64$ the list theorem is asked for. **At 12 bits the loss is $6/2^{13} = 0.07$ percent** (63 columns a round at $n_0 = 2^{19}$, 4095 at $2^{25}$) and the six grinds cost $6 \cdot 2^{12}$ permutations. The script uses 12. Without the loss the grind would have to be $\log_2 n_0 - 2$ bits a round, 23 at $\mu = 30$. This choice is for soundness only: section 6.1 shows that the extractor of `formal/` cannot use the loss, so knowledge soundness at 125 bits needs the large grind after all.

### 4.3 What the out-of-domain points become, and how many it saves (exact in the model)

`python3 scripts/71_payoff.py --points`, row M0 at a 15-bit point grind, one batch:

| $\mu$ | Reed-Solomon level 0 of the paper ($L = 2^7$, $2^{40}$) | tree level 0, multilinear points ($L = 2, 16, 2^{20}$) | tensor-power points |
| --- | --- | --- | --- |
| 24 | 10, 11 | 9, 9, 9 | 9, 9, 10 |
| 28 | 11, 12 | 9, 9, 9 | 9, 9, 10 |
| 30 | 11, 12 | 9, 9, 9 | 9, 9, 10 |

A point gives 123.1 bits ($\mu/q$) instead of 104 ($2^{\kappa}/q$), and the row needs $1023 + 3 \log_2 L$ bits at a 12-bit fold grind, 570 of them the discount for reusing points across six rounds. **So 9 points instead of 10 to 12: one to three saved**, and on the ladder schedule $(4,5,6,7,8,9)$ 48 scalars instead of 55 to 66; with the two scalars a round and the high part that go away, level 0's stream is 25 to 36 scalars (0.4 to 0.6 KiB) shorter than the Reed-Solomon DEEP fold's. One caveat the lead's question hides: a uniform point of $E^{\mu}$ is $\mu$ challenges, and the guest's sponge spends one permutation a challenge (`squeeze_point_from`, `guests/lean_ethereum.py:1256`), 270 permutations for nine points. A **tensor-power point** fixes it: split the coordinates into blocks of eight and set a block to $(\theta, \theta^2, \dots, \theta^{128})$; the error is $\lceil \mu/8 \rceil \cdot 255/q = 2^{-118}$, four challenges a point, and the count stays 9 for $L \le 16$. The tables of section 5 use it.

### 4.4 What would have to be re-proved

By hand (all easier than the polynomial versions, none written out in full here):

1. the class lemma and the fold round for a scalar fold with a loss of $g$ columns (replacing Lemmas 4.5 and 4.8), and the near-tuple notion "up to $g$ columns" through the extractor;
2. the point facts for multilinear or tensor-power points, with (E2) for the lane variables;
3. row M3 at the boundary from a level without a high part to a Reed-Solomon level, and the conversion of the carried claims;
4. the composition for a ladder whose levels are of two kinds (challenge space $E$ with thresholds stepping by $g$, then $E^2$ stepping by one);
5. nothing for the interleaving: Theorem 6.1 (any code with an agreement bound) and Proposition 6.2 (any code with a generator matrix over $K$) already give the interleaved, $E$-valued list from a single-lane list over $K$, with the same $L$ for $L < 2^{63}$;
6. the list theorem itself, which is another researcher's.

In Lean (`doc/deep_fold/lean`, 12.2k lines, **checked** by reading the file list and the structures):

- reusable as they are: `DeepFold/Counting.lean` (`exists_big_class`, stated for an abstract relation), `Protocol/Potential.lean`, `Interleave/Tree.lean`, `Interleave/Projection.lean`, `Soundness/RBR.lean`;
- to be redone for an abstract linear code and a scalar challenge: `DeepFold/Basic.lean`, `Class.lean`, `Lanes.lean`, `Claim.lean`, `Main.lean`, `Theorem.lean` (about 1.4k lines, all over `K[X]`; the new versions have no poles and no degrees and should be shorter);
- to be redone for the new functional and constants: `Protocol/Pinning.lean`, `Level.lean`, `Ladder.lean`, `Params.lean`;
- to be generalized: `Rounds/Fold.lean`, `Rounds/Query.lean` and `Soundness/ProtocolD.lean`, whose `structure Level` (`:58`) is a level of polynomial lanes with challenge pairs; the composed theorem `protocolD_rbr` needs a second kind of level.

That development is not connected to `formal/`, which proves today's Annex B. A deployment would need `formal/` to carry the whole new argument, and the list theorem for the code as a statement about the permutation.

### 4.5 What the oracle modelling requires

- The code is a function of the oracle on a fixed public set of inputs, $n_0/15$ of them per (size, rate), tagged apart from every transcript and Merkle input. "The code is good" is an event over those values alone, and the rest of the oracle stays uniform given them. So soundness is $\delta_{\mathrm{code}}$ plus the round-by-round sum, and $\delta_{\mathrm{code}}$ is paid once: it is not multiplied by the prover's queries or by the number of proofs. This is right in the random oracle model.
- `formal/` works in the random-permutation model. There the tagged inputs are permutation inputs the adversary may also query, which is harmless (the twiddles are public), but two things must be written: the existing bounds with the adversary's query count raised by the size of the table, and that no honest call (a first block has a zero capacity and a free rate, `zkDSL.md:454`) can equal a twiddle call. A nonzero constant in the capacity cells of the twiddle calls gives the second.
- The family: 13 sizes by 4 rates, or one nested forest (section 2.4); a union bound of 6 bits either way. The theorem must cover $n_0$ up to $2^{26}$ for rates 1/2 and 1/4 at $\mu = 30$ and $2^{28}$ if rate 1/16 keeps the same level 0.
- What the modelling cannot give: Keccak is one function, so the deployed code is one code, and "it is list decodable" becomes a statement nobody can check for that code, with no certificate. Every random oracle proof has this status, but here the unverifiable object is a combinatorial property of a public matrix, and `formal/statement.tex` would have to say so.

## 5. The payoff

### 5.1 The model

`scripts/71_tree_level.py`, `71_payoff.py`, `71_hybrid.py` (outputs in `scripts/71_*_output.txt`). Bytes and Keccak counts are **exact in the model** (note 08's validated byte and hash model, note 67's stream of the DEEP fold, both reused unedited; the self-test checks that this note's cost function equals `67_model.cost` on Reed-Solomon levels). Guest cycle-equivalents are **estimates**: note 08's fitted cycles a query, 8 a `KECCAK` step, note 67's count for points, and section 2.5 for the twiddles.

- **Level 0, tree code.** Agreement $\tau = (1 + L\rho)/(L+1) + \varepsilon$ for the list hypothesis, interleaved list $L$ (projection bound), scalar fold with a 12-bit grind and a loss of $n_0/2^{13}$ columns a round (section 4.2), tensor-power points on the ladder schedule (9 points at 64 lanes, 8 at 32), query row $((\tau n_0 + \ell_0 g - 1)/n_0)^t + (\bar s + t)/q$, twiddles by design D2. So the queries are $\lceil (125 - g_q) / \log_2 (1/(\tau + 0.0007)) \rceil$: the table is a function of $\tau$ alone, and $L$ enters only through $\tau$ (the points do not move for $L \le 16$).
- **Levels 1 and later.** In "DEEP" rows, note 67's best proven DEEP-fold levels (Johnson, counting at the last levels, ladder schedules). In "hybrid" rows (section 5.4), today's protocol.
- **Alone**: the deployed ladder (64 lanes) and grinds. **With C's knobs**: 32 lanes, C's ladder, level-0 query grind $\max(17, \mu - 6)$.
- **Cap rule.** The guest's Merkle cap depth (`merkle_cap_depth`) jumps from 8 to 2 when a level has 128 queries or fewer and a depth that is 2 modulo 6, which is noise for every configuration (note 08, section 8.1). Tables use the deployed rule; `--bestcap` reruns everything with the better of the two caps, today and C included, and no verdict below changes except where said.

### 5.2 Summary against C, DEEP fold at every level (percent; range over $\mu = 24, 28, 30$)

"Clear win": more than ten percent below C on bytes at every size, and the guest's cycle-equivalents not above C's at any size, both for the configuration with C's knobs.

**Rate 1/2** (Johnson is $\tau = 0.707$; C has 215, 207, 203 level-0 queries)

| $L$ | $\varepsilon$ | $\tau$ | alone: bytes | alone: guest | with C's knobs: level-0 queries | bytes | guest | clear win |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.682 | +4.8 to +3.8 | +13.8 to +11.6 | 195, 188, 184 | -6.3 to -8.6 | +4.4 to +0.8 | no |
| 2 | 2/64 | 0.698 | +8.7 to +7.7 | +18.4 to +16.5 | 207, 199, 196 | -3.2 to -5.6 | +8.2 to +4.6 | no |
| 2 | 4/64 | 0.729 | +18.7 to +17.2 | +29.6 to +28.3 | 236, 227, 223 | +3.6 to +1.7 | +16.6 to +13.6 | no |
| 3 | 1/64 | 0.641 | -4.4 to -5.5 | +2.9 to +0.2 | 167, 161, 158 | -12.9 to -15.7 | -3.9 to -8.0 | yes |
| 3 | 2/64 | 0.656 | -1.1 to -2.2 | +6.8 to +4.3 | 177, 170, 167 | -10.6 to -13.2 | -1.0 to -4.8 | yes |
| 3 | 4/64 | 0.688 | +6.1 to +5.1 | +15.3 to +13.2 | 199, 191, 188 | -5.3 to -7.6 | +5.6 to +2.1 | no |
| 4 | 1/64 | 0.616 | -9.0 to -10.3 | -2.5 to -5.5 | 154, 148, 145 | -16.3 to -19.0 | -8.0 to -12.0 | yes |
| 4 | 2/64 | 0.631 | -6.1 to -7.2 | +1.0 to -1.8 | 162, 156, 153 | -14.2 to -17.0 | -5.5 to -9.5 | yes |
| 4 | 4/64 | 0.662 | +0.2 to -0.9 | +8.4 to +5.9 | 181, 174, 171 | -9.6 to -12.1 | +0.3 to -3.6 | no |
| 8 | 1/64 | 0.571 | -16.0 to -17.8 | -10.6 to -14.1 | 133, 128, 126 | -21.2 to -24.5 | -10.4 to -18.6 | yes |
| 8 | 2/64 | 0.587 | -13.7 to -15.3 | -7.9 to -11.2 | 140, 135, 132 | -19.7 to -22.7 | -12.2 to -16.4 | yes |
| 8 | 4/64 | 0.618 | -8.7 to -9.9 | -2.1 to -5.1 | 155, 149, 146 | -16.0 to -18.8 | -7.7 to -11.7 | yes |
| 16 | 1/64 | 0.545 | -19.4 to -21.4 | -14.5 to -18.1 | 123, 118, 116 | -23.9 to -27.1 | -14.0 to -18.5 | yes |
| 16 | 2/64 | 0.561 | -17.4 to -19.2 | -12.2 to -15.7 | 129, 124, 122 | -22.3 to -25.5 | -11.8 to -19.9 | yes |
| 16 | 4/64 | 0.592 | -12.7 to -14.2 | -6.8 to -10.0 | 142, 137, 134 | -19.1 to -22.1 | -11.6 to -15.8 | yes |

**Rate 1/4** (Johnson is $\tau = 0.5$; C has 108, 104, 102 level-0 queries)

| $L$ | $\varepsilon$ | $\tau$ | alone: bytes | alone: guest | with C's knobs: level-0 queries | bytes | guest | clear win |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.516 | +8.1 to +6.5 | +21.2 to +18.8 | 113, 108, 106 | -0.3 to -3.4 | +14.4 to +11.7 | no |
| 2 | 2/64 | 0.531 | +10.6 to +9.2 | +24.4 to +22.1 | 118, 114, 111 | +1.7 to -1.4 | +17.4 to +14.3 | no |
| 2 | 4/64 | 0.562 | +16.6 to +15.3 | +31.0 to +22.9 | 130, 125, 122 | +6.0 to +3.4 | +22.8 to +20.8 | no |
| 3 | 1/64 | 0.453 | -1.4 to -3.8 | +9.1 to +5.9 | 94, 91, 89 | -7.1 to -11.0 | +6.0 to +1.5 | no |
| 3 | 2/64 | 0.469 | +1.1 to -1.1 | +12.3 to +9.3 | 99, 95, 93 | -5.5 to -9.0 | +8.0 to +4.2 | no |
| 3 | 4/64 | 0.500 | +5.6 to +3.8 | +18.0 to +15.4 | 108, 104, 102 | -1.9 to -5.4 | +12.4 to +9.0 | no |
| 4 | 1/64 | 0.416 | -5.9 to -8.7 | +3.4 to -0.1 | 85, 82, 80 | -10.7 to -14.7 | +1.4 to -3.3 | bytes only |
| 4 | 2/64 | 0.431 | -3.9 to -6.6 | +5.9 to +2.6 | 89, 86, 84 | -9.1 to -13.0 | +3.5 to -1.1 | no |
| 4 | 4/64 | 0.463 | +0.1 to -2.2 | +11.0 to +8.0 | 97, 93, 91 | -6.3 to -9.8 | +7.0 to +3.1 | no |
| 8 | 1/64 | 0.349 | -13.0 to -16.4 | -5.3 to -9.6 | 71, 68, 67 | -15.9 to -20.4 | -5.6 to -10.9 | yes |
| 8 | 2/64 | 0.365 | -11.5 to -14.8 | -3.4 to -7.6 | 74, 71, 70 | -14.7 to -19.2 | -4.1 to -9.3 | yes |
| 8 | 4/64 | 0.396 | -8.5 to -11.5 | +0.3 to -3.5 | 81, 78, 76 | -12.3 to -16.3 | -0.6 to -5.5 | yes (a tie with the retuned cap rule) |
| 16 | 1/64 | 0.310 | -16.6 to -20.3 | -9.6 to -14.3 | 64, 62, 60 | -18.7 to -23.3 | -8.7 to -14.7 | yes |
| 16 | 2/64 | 0.325 | -15.6 to -19.2 | -8.4 to -13.0 | 67, 64, 63 | -17.5 to -22.1 | -7.7 to -13.1 | yes |
| 16 | 4/64 | 0.357 | -12.5 to -15.9 | -4.7 to -8.9 | 73, 70, 69 | -15.1 to -19.6 | -4.6 to -9.8 | yes |

**Reading, as a function of $\tau$.** With C's knobs the opening shrinks by 1.4 to 1.5 percent of C for each 0.01 of $\tau$ at rate 1/2 and by 0.9 to 1.0 percent at rate 1/4. Ten percent below C on bytes needs $\tau \le 0.66$ at rate 1/2 and $\tau \le 0.42$ at rate 1/4. The guest breaks even with C at $\tau \approx 0.665$ (rate 1/2) and $\tau \approx 0.40$ (rate 1/4): at rate 1/4 the DEEP fold's points at the later levels, a fixed cost, are a larger share (note 67 found the same: the DEEP fold with C's knobs costs the guest 2 to 9 percent before any gain). **So the clear win starts at $L = 3$ with $\varepsilon \le 2/64$ at rate 1/2, and at $L = 8$ at rate 1/4** (any $\varepsilon \le 4/64$; $L = 4$ with $\varepsilon = 1/64$ wins on bytes and ties on the guest). $L = 2$ never pays: its radius $(1 + 2\rho)/3$ is 0.667 at rate 1/2 and exactly Johnson's 0.5 at rate 1/4, and the slack puts it back near or above Johnson. Alone (64 lanes, deployed grinds) the tree code needs one step more: $L = 8$ with $\varepsilon \le 2/64$, or $L = 16$, at either rate.

**Sensitivity.** The verdicts at the boundary rest on section 2.5's estimate. Level 0 is about 60 percent of the guest's cost of an opening, so if a tree query cost 15 percent more than a Reed-Solomon one instead of 5 to 10 (design D1, or T2), every guest column rises by about 4 points: the row $L = 3$, $\varepsilon = 2/64$ at rate 1/2 and the row $L = 8$, $\varepsilon = 4/64$ at rate 1/4 become "bytes only", and nothing else changes.

### 5.3 The payoff tables, DEEP fold at every level (deployed cap rule)

Bytes and Keccak **exact in the model**, cycle-equivalents **estimate**. $q_0$ is the level-0 query count; percentages are against C; "Keccak" is the guest's count of `KECCAK` steps for the opening, twiddles included.

**$\mu = 24$, rate 1/2.** Today: 218 level-0 queries, 260.4 KiB, 5748 Keccak, 181.4k cycle-eq. C: 215 queries, 224.9 KiB, 5734 Keccak, 157.6k cycle-eq. Percentages are against C.

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.682 | 197 | 235.0 (+4.5%) | 5775 | 175.9k (+11.6%) | 195 | 205.6 (-8.6%) | 5854 | 158.9k (+0.8%) |
| 2 | 2/64 | 0.698 | 209 | 244.4 (+8.7%) | 6005 | 183.6k (+16.5%) | 207 | 212.4 (-5.6%) | 6063 | 164.8k (+4.6%) |
| 2 | 4/64 | 0.729 | 238 | 267.0 (+18.7%) | 6562 | 202.1k (+28.3%) | 236 | 228.7 (+1.7%) | 6567 | 179.1k (+13.6%) |
| 3 | 1/64 | 0.641 | 169 | 212.8 (-5.3%) | 5237 | 157.9k (+0.2%) | 167 | 189.6 (-15.7%) | 5364 | 145.1k (-8.0%) |
| 3 | 2/64 | 0.656 | 179 | 220.8 (-1.8%) | 5429 | 164.3k (+4.3%) | 177 | 195.3 (-13.2%) | 5539 | 150.0k (-4.8%) |
| 3 | 4/64 | 0.688 | 201 | 238.1 (+5.9%) | 5852 | 178.4k (+13.2%) | 199 | 207.8 (-7.6%) | 5924 | 160.9k (+2.1%) |
| 4 | 1/64 | 0.616 | 155 | 201.7 (-10.3%) | 4967 | 148.9k (-5.5%) | 154 | 182.1 (-19.0%) | 5136 | 138.7k (-12.0%) |
| 4 | 2/64 | 0.631 | 164 | 208.9 (-7.1%) | 5141 | 154.7k (-1.8%) | 162 | 186.7 (-17.0%) | 5276 | 142.6k (-9.5%) |
| 4 | 4/64 | 0.662 | 183 | 223.9 (-0.4%) | 5506 | 166.9k (+5.9%) | 181 | 197.6 (-12.1%) | 5610 | 152.0k (-3.6%) |
| 8 | 1/64 | 0.571 | 134 | 184.9 (-17.8%) | 4563 | 135.5k (-14.1%) | 133 | 169.8 (-24.5%) | 4767 | 128.3k (-18.6%) |
| 8 | 2/64 | 0.587 | 141 | 190.5 (-15.3%) | 4697 | 140.0k (-11.2%) | 140 | 173.9 (-22.7%) | 4890 | 131.7k (-16.4%) |
| 8 | 4/64 | 0.618 | 156 | 202.5 (-9.9%) | 4986 | 149.6k (-5.1%) | 155 | 182.6 (-18.8%) | 5154 | 139.1k (-11.7%) |
| 16 | 1/64 | 0.545 | 124 | 176.8 (-21.4%) | 4369 | 129.0k (-18.1%) | 123 | 164.0 (-27.1%) | 5134 | 130.5k (-17.2%) |
| 16 | 2/64 | 0.561 | 130 | 181.7 (-19.2%) | 4485 | 132.9k (-15.7%) | 129 | 167.5 (-25.5%) | 4696 | 126.3k (-19.9%) |
| 16 | 4/64 | 0.592 | 144 | 192.9 (-14.2%) | 4755 | 141.9k (-10.0%) | 142 | 175.1 (-22.1%) | 4925 | 132.7k (-15.8%) |

**$\mu = 24$, rate 1/4.** Today: 109 level-0 queries, 169.9 KiB, 4318 Keccak, 115.2k cycle-eq. C: 108 queries, 156.1 KiB, 4352 Keccak, 105.4k cycle-eq. Percentages are against C.

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.516 | 114 | 166.2 (+6.5%) | 4598 | 125.2k (+18.8%) | 113 | 150.9 (-3.4%) | 4643 | 117.7k (+11.7%) |
| 2 | 2/64 | 0.531 | 119 | 170.4 (+9.2%) | 4724 | 128.8k (+22.1%) | 118 | 154.0 (-1.4%) | 4759 | 120.6k (+14.3%) |
| 2 | 4/64 | 0.562 | 131 | 180.5 (+15.6%) | 4438 | 129.6k (+22.9%) | 130 | 161.4 (+3.4%) | 5037 | 127.3k (+20.8%) |
| 3 | 1/64 | 0.453 | 95 | 150.1 (-3.8%) | 4120 | 111.7k (+5.9%) | 94 | 138.9 (-11.0%) | 4203 | 107.1k (+1.5%) |
| 3 | 2/64 | 0.469 | 100 | 154.4 (-1.1%) | 4246 | 115.2k (+9.3%) | 99 | 142.1 (-9.0%) | 4319 | 109.9k (+4.2%) |
| 3 | 4/64 | 0.500 | 109 | 162.0 (+3.8%) | 4473 | 121.7k (+15.4%) | 108 | 147.7 (-5.4%) | 4527 | 114.9k (+9.0%) |
| 4 | 1/64 | 0.416 | 86 | 142.5 (-8.7%) | 3894 | 105.3k (-0.1%) | 85 | 133.2 (-14.7%) | 4048 | 101.9k (-3.3%) |
| 4 | 2/64 | 0.431 | 90 | 145.9 (-6.6%) | 3994 | 108.1k (+2.6%) | 89 | 135.7 (-13.0%) | 4144 | 104.2k (-1.1%) |
| 4 | 4/64 | 0.463 | 98 | 152.7 (-2.2%) | 4196 | 113.8k (+8.0%) | 97 | 140.8 (-9.8%) | 4273 | 108.7k (+3.1%) |
| 8 | 1/64 | 0.349 | 72 | 130.4 (-16.4%) | 3541 | 95.3k (-9.6%) | 71 | 124.2 (-20.4%) | 3709 | 93.9k (-10.9%) |
| 8 | 2/64 | 0.365 | 75 | 133.0 (-14.8%) | 3617 | 97.5k (-7.6%) | 74 | 126.2 (-19.2%) | 3782 | 95.6k (-9.3%) |
| 8 | 4/64 | 0.396 | 81 | 138.2 (-11.5%) | 3768 | 101.7k (-3.5%) | 81 | 130.7 (-16.3%) | 3951 | 99.6k (-5.5%) |
| 16 | 1/64 | 0.310 | 65 | 124.4 (-20.3%) | 3365 | 90.3k (-14.3%) | 64 | 119.7 (-23.3%) | 3540 | 89.9k (-14.7%) |
| 16 | 2/64 | 0.325 | 67 | 126.1 (-19.2%) | 3416 | 91.8k (-13.0%) | 67 | 121.6 (-22.1%) | 3613 | 91.6k (-13.1%) |
| 16 | 4/64 | 0.357 | 73 | 131.3 (-15.9%) | 3567 | 96.0k (-8.9%) | 73 | 125.5 (-19.6%) | 3758 | 95.1k (-9.8%) |

**$\mu = 28$, rate 1/2.** Today: 218 level-0 queries, 313.7 KiB, 7883 Keccak, 218.4k cycle-eq. C: 207 queries, 276.1 KiB, 7783 Keccak, 192.1k cycle-eq. Percentages are against C.

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.682 | 197 | 286.4 (+3.8%) | 8008 | 217.1k (+13.0%) | 188 | 256.1 (-7.2%) | 8011 | 199.2k (+3.7%) |
| 2 | 2/64 | 0.698 | 209 | 297.4 (+7.7%) | 8322 | 226.2k (+17.8%) | 199 | 263.7 (-4.5%) | 8277 | 205.9k (+7.2%) |
| 2 | 4/64 | 0.729 | 238 | 323.6 (+17.2%) | 9082 | 248.2k (+29.2%) | 227 | 283.0 (+2.5%) | 8955 | 222.9k (+16.0%) |
| 3 | 1/64 | 0.641 | 169 | 260.8 (-5.5%) | 7274 | 195.9k (+2.0%) | 161 | 237.2 (-14.1%) | 7358 | 182.8k (-4.9%) |
| 3 | 2/64 | 0.656 | 179 | 270.0 (-2.2%) | 7536 | 203.5k (+5.9%) | 170 | 243.5 (-11.8%) | 7575 | 188.2k (-2.0%) |
| 3 | 4/64 | 0.688 | 201 | 290.1 (+5.1%) | 8113 | 220.2k (+14.6%) | 191 | 258.2 (-6.5%) | 8084 | 201.0k (+4.6%) |
| 4 | 1/64 | 0.616 | 155 | 247.9 (-10.2%) | 6907 | 185.3k (-3.5%) | 148 | 228.1 (-17.4%) | 7043 | 174.9k (-9.0%) |
| 4 | 2/64 | 0.631 | 164 | 256.2 (-7.2%) | 7143 | 192.2k (+0.0%) | 156 | 233.7 (-15.3%) | 7237 | 179.7k (-6.5%) |
| 4 | 4/64 | 0.662 | 183 | 273.7 (-0.9%) | 7641 | 206.5k (+7.5%) | 174 | 246.3 (-10.8%) | 7672 | 190.7k (-0.8%) |
| 8 | 1/64 | 0.571 | 134 | 228.5 (-17.2%) | 6357 | 169.4k (-11.8%) | 128 | 213.9 (-22.5%) | 6558 | 162.7k (-15.3%) |
| 8 | 2/64 | 0.587 | 141 | 235.0 (-14.9%) | 6541 | 174.7k (-9.0%) | 135 | 218.9 (-20.7%) | 6727 | 166.9k (-13.1%) |
| 8 | 4/64 | 0.618 | 156 | 248.9 (-9.9%) | 6934 | 186.1k (-3.1%) | 149 | 228.8 (-17.1%) | 7067 | 175.5k (-8.7%) |
| 16 | 1/64 | 0.545 | 124 | 219.2 (-20.6%) | 6095 | 161.9k (-15.7%) | 118 | 206.8 (-25.1%) | 6316 | 156.6k (-18.5%) |
| 16 | 2/64 | 0.561 | 130 | 224.8 (-18.6%) | 6252 | 166.4k (-13.4%) | 124 | 211.0 (-23.6%) | 6461 | 160.3k (-16.6%) |
| 16 | 4/64 | 0.592 | 144 | 237.8 (-13.9%) | 6619 | 177.0k (-7.9%) | 137 | 220.3 (-20.2%) | 6776 | 168.2k (-12.5%) |

**$\mu = 28$, rate 1/4.** Today: 109 level-0 queries, 207.7 KiB, 5213 Keccak, 133.4k cycle-eq. C: 104 queries, 192.3 KiB, 5292 Keccak, 123.1k cycle-eq. Percentages are against C.

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.516 | 114 | 205.3 (+6.8%) | 5596 | 148.4k (+20.6%) | 108 | 189.4 (-1.5%) | 5690 | 140.8k (+14.4%) |
| 2 | 2/64 | 0.531 | 119 | 210.1 (+9.3%) | 5727 | 152.2k (+23.6%) | 114 | 193.9 (+0.8%) | 5836 | 144.5k (+17.4%) |
| 2 | 4/64 | 0.562 | 131 | 221.7 (+15.3%) | 6042 | 161.3k (+31.0%) | 125 | 202.1 (+5.1%) | 6104 | 151.2k (+22.8%) |
| 3 | 1/64 | 0.453 | 95 | 186.8 (-2.8%) | 5097 | 134.0k (+8.9%) | 91 | 176.6 (-8.2%) | 5274 | 130.5k (+6.0%) |
| 3 | 2/64 | 0.469 | 100 | 191.7 (-0.3%) | 5229 | 137.8k (+12.0%) | 95 | 179.6 (-6.6%) | 5372 | 132.9k (+8.0%) |
| 3 | 4/64 | 0.500 | 109 | 200.5 (+4.2%) | 5465 | 144.6k (+17.5%) | 104 | 186.4 (-3.1%) | 5592 | 138.4k (+12.4%) |
| 4 | 1/64 | 0.416 | 86 | 178.0 (-7.4%) | 4862 | 127.2k (+3.3%) | 82 | 169.7 (-11.8%) | 5104 | 124.9k (+1.4%) |
| 4 | 2/64 | 0.431 | 90 | 182.0 (-5.4%) | 4966 | 130.2k (+5.8%) | 86 | 172.8 (-10.2%) | 5206 | 127.4k (+3.5%) |
| 4 | 4/64 | 0.463 | 98 | 189.8 (-1.3%) | 5176 | 136.3k (+10.7%) | 93 | 178.1 (-7.4%) | 5323 | 131.7k (+7.0%) |
| 8 | 1/64 | 0.349 | 72 | 164.3 (-14.6%) | 4494 | 116.6k (-5.3%) | 68 | 159.0 (-17.3%) | 4745 | 116.2k (-5.6%) |
| 8 | 2/64 | 0.365 | 75 | 167.2 (-13.0%) | 4572 | 118.9k (-3.4%) | 71 | 161.3 (-16.1%) | 4822 | 118.0k (-4.1%) |
| 8 | 4/64 | 0.396 | 81 | 173.1 (-10.0%) | 4730 | 123.4k (+0.3%) | 78 | 166.6 (-13.3%) | 5001 | 122.4k (-0.6%) |
| 16 | 1/64 | 0.310 | 65 | 157.3 (-18.2%) | 4309 | 111.3k (-9.6%) | 62 | 154.3 (-19.8%) | 4591 | 112.4k (-8.7%) |
| 16 | 2/64 | 0.325 | 67 | 159.3 (-17.2%) | 4362 | 112.8k (-8.4%) | 64 | 155.9 (-19.0%) | 4642 | 113.7k (-7.7%) |
| 16 | 4/64 | 0.357 | 73 | 165.3 (-14.1%) | 4520 | 117.3k (-4.7%) | 70 | 160.5 (-16.5%) | 4796 | 117.4k (-4.6%) |

**$\mu = 30$, rate 1/2.** Today: 218 level-0 queries, 335.9 KiB, 8173 Keccak, 226.9k cycle-eq. C: 203 queries, 297.1 KiB, 8101 Keccak, 200.1k cycle-eq. Percentages are against C.

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.682 | 197 | 311.4 (+4.8%) | 8370 | 227.7k (+13.8%) | 184 | 278.4 (-6.3%) | 8357 | 208.9k (+4.4%) |
| 2 | 2/64 | 0.698 | 209 | 323.0 (+8.7%) | 8685 | 237.0k (+18.4%) | 196 | 287.5 (-3.2%) | 8651 | 216.5k (+8.2%) |
| 2 | 4/64 | 0.729 | 238 | 351.1 (+18.2%) | 9446 | 259.5k (+29.6%) | 223 | 307.8 (+3.6%) | 9313 | 233.4k (+16.6%) |
| 3 | 1/64 | 0.641 | 169 | 284.0 (-4.4%) | 7634 | 206.0k (+2.9%) | 158 | 258.6 (-12.9%) | 7812 | 192.4k (-3.9%) |
| 3 | 2/64 | 0.656 | 179 | 293.8 (-1.1%) | 7897 | 213.8k (+6.8%) | 167 | 265.5 (-10.6%) | 8043 | 198.1k (-1.0%) |
| 3 | 4/64 | 0.688 | 201 | 315.3 (+6.1%) | 8475 | 230.8k (+15.3%) | 188 | 281.5 (-5.3%) | 8455 | 211.4k (+5.6%) |
| 4 | 1/64 | 0.616 | 155 | 270.2 (-9.0%) | 7266 | 195.1k (-2.5%) | 145 | 248.7 (-16.3%) | 7479 | 184.0k (-8.0%) |
| 4 | 2/64 | 0.631 | 164 | 279.1 (-6.1%) | 7503 | 202.1k (+1.0%) | 153 | 254.8 (-14.2%) | 7684 | 189.2k (-5.5%) |
| 4 | 4/64 | 0.662 | 183 | 297.7 (+0.2%) | 8002 | 216.9k (+8.4%) | 171 | 268.6 (-9.6%) | 8145 | 200.7k (+0.3%) |
| 8 | 1/64 | 0.571 | 134 | 249.5 (-16.0%) | 6714 | 178.9k (-10.6%) | 126 | 234.0 (-21.2%) | 7551 | 179.3k (-10.4%) |
| 8 | 2/64 | 0.587 | 141 | 256.4 (-13.7%) | 6899 | 184.3k (-7.9%) | 132 | 238.6 (-19.7%) | 7144 | 175.7k (-12.2%) |
| 8 | 4/64 | 0.618 | 156 | 271.2 (-8.7%) | 7293 | 195.9k (-2.1%) | 146 | 249.4 (-16.0%) | 7504 | 184.7k (-7.7%) |
| 16 | 1/64 | 0.545 | 124 | 239.6 (-19.4%) | 6450 | 171.1k (-14.5%) | 116 | 226.2 (-23.9%) | 7238 | 172.2k (-14.0%) |
| 16 | 2/64 | 0.561 | 130 | 245.5 (-17.4%) | 6608 | 175.8k (-12.2%) | 122 | 230.9 (-22.3%) | 7426 | 176.4k (-11.8%) |
| 16 | 4/64 | 0.592 | 144 | 259.4 (-12.7%) | 6977 | 186.6k (-6.8%) | 134 | 240.2 (-19.1%) | 7196 | 177.0k (-11.6%) |

**$\mu = 30$, rate 1/4.** Today: 109 level-0 queries, 222.6 KiB, 6000 Keccak, 146.3k cycle-eq. C: 102 queries, 206.5 KiB, 5961 Keccak, 134.6k cycle-eq. Percentages are against C.

| $L$ | $\varepsilon$ | $\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1/64 | 0.516 | 114 | 223.3 (+8.1%) | 6557 | 163.1k (+21.2%) | 106 | 205.8 (-0.3%) | 6466 | 153.2k (+13.8%) |
| 2 | 2/64 | 0.531 | 119 | 228.4 (+10.6%) | 6723 | 167.4k (+24.4%) | 111 | 209.9 (+1.7%) | 6622 | 156.7k (+16.4%) |
| 2 | 4/64 | 0.562 | 131 | 240.7 (+16.6%) | 6534 | 170.0k (+26.2%) | 122 | 218.8 (+6.0%) | 6966 | 164.5k (+22.2%) |
| 3 | 1/64 | 0.453 | 95 | 203.6 (-1.4%) | 5925 | 146.8k (+9.1%) | 89 | 191.9 (-7.1%) | 5935 | 141.2k (+4.9%) |
| 3 | 2/64 | 0.469 | 100 | 208.8 (+1.1%) | 6091 | 151.1k (+12.3%) | 93 | 195.2 (-5.5%) | 6060 | 144.0k (+7.0%) |
| 3 | 4/64 | 0.500 | 109 | 218.1 (+5.6%) | 6391 | 158.8k (+18.0%) | 102 | 202.6 (-1.9%) | 6341 | 150.4k (+11.7%) |
| 4 | 1/64 | 0.416 | 86 | 194.3 (-5.9%) | 5626 | 139.1k (+3.4%) | 80 | 184.5 (-10.7%) | 5653 | 134.8k (+0.1%) |
| 4 | 2/64 | 0.431 | 90 | 198.4 (-3.9%) | 5759 | 142.6k (+5.9%) | 84 | 187.8 (-9.1%) | 5778 | 137.6k (+2.2%) |
| 4 | 4/64 | 0.463 | 98 | 206.7 (+0.1%) | 6025 | 149.4k (+11.0%) | 91 | 193.6 (-6.3%) | 5997 | 142.6k (+5.9%) |
| 8 | 1/64 | 0.349 | 72 | 179.6 (-13.0%) | 5160 | 127.1k (-5.6%) | 67 | 173.7 (-15.9%) | 5247 | 125.6k (-6.7%) |
| 8 | 2/64 | 0.365 | 75 | 182.8 (-11.5%) | 5260 | 129.7k (-3.7%) | 70 | 176.2 (-14.7%) | 5341 | 127.7k (-5.1%) |
| 8 | 4/64 | 0.396 | 81 | 189.0 (-8.5%) | 5460 | 134.8k (+0.2%) | 76 | 181.2 (-12.3%) | 5528 | 132.0k (-2.0%) |
| 16 | 1/64 | 0.310 | 65 | 172.2 (-16.6%) | 4928 | 121.1k (-10.0%) | 60 | 167.8 (-18.7%) | 5028 | 120.7k (-10.4%) |
| 16 | 2/64 | 0.325 | 67 | 174.4 (-15.6%) | 4994 | 122.8k (-8.7%) | 63 | 170.4 (-17.5%) | 5122 | 122.8k (-8.8%) |
| 16 | 4/64 | 0.357 | 73 | 180.7 (-12.5%) | 5194 | 128.0k (-4.9%) | 69 | 175.4 (-15.1%) | 5310 | 127.0k (-5.6%) |

A note on the Keccak columns: under the deployed cap rule a level with at most 128 queries and a tree depth of 2 modulo 6 walks 18 path levels instead of 12, which is why 123 queries can cost more permutations than 129 ($\mu = 24$, rate 1/2, with C's knobs) and 126 more than 132 ($\mu = 30$). `scripts/71_payoff_bestcap_output.txt` has the same tables without that artefact.

### 5.4 A better way to use it: DEEP fold at level 0 only (sketch for the boundary row; numbers exact in the model)

The DEEP fold's points are needed where a list bound replaces correlated agreement, which is level 0 only. Levels 1 and later can stay exactly as they are today (Annex B: affine fold, one OOD point, Johnson lists $L_i$), and the two analyses meet at the level-0 query message, whose row becomes $((\tau n_0 + \ell_0 g - 1)/n_0)^{t} + (\bar s + t + 1) L_1/q$: the pinned member of level 1's list is caught by a query, and every other member by the batching, as in Annex B's own query row. I have not written this boundary out in full; it uses nothing beyond the two proofs. `scripts/71_hybrid.py`, with C's knobs, against C (percent, range over $\mu = 24, 28, 30$; the level-0 query counts are those of section 5.2):

| rate | $L$, $\varepsilon$ | $\tau$ | KiB at $\mu = 24, 28, 30$ | bytes | guest Keccak | guest cycle-eq | clear win |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 2, 1/64 | 0.682 | 213.9, 263.3, 283.0 | -4.6 to -4.9 | +5.5 to +5.0 | +0.5 to -1.1 | no |
| 1/2 | 3, 1/64 | 0.641 | 197.9, 244.4, 263.2 | -11.4 to -12.0 | -1.6 to -3.4 | -7.8 to -9.9 | yes |
| 1/2 | 3, 2/64 | 0.656 | 203.6, 250.7, 270.1 | -9.1 to -9.4 | +1.2 to -0.6 | -4.9 to -6.8 | no (bytes 9 percent) |
| 1/2 | 4, 1/64 | 0.616 | 190.4, 235.3, 253.3 | -14.7 to -15.3 | -5.7 to -7.5 | -11.9 to -14.0 | yes |
| 1/2 | 4, 2/64 | 0.631 | 195.0, 240.9, 259.4 | -12.7 to -13.3 | -3.2 to -5.0 | -9.4 to -11.5 | yes |
| 1/2 | 4, 4/64 | 0.662 | 205.9, 253.5, 273.2 | -8.0 to -8.4 | +2.5 to +0.6 | -3.6 to -5.5 | no |
| 1/2 | 8, 1/64 | 0.571 | 178.2, 221.1, 238.6 | -19.7 to -20.8 | -4.8 to -13.7 | -14.3 to -20.6 | yes |
| 1/2 | 8, 4/64 | 0.618 | 191.0, 236.0, 254.0 | -14.5 to -15.1 | -5.4 to -7.1 | -11.6 to -13.7 | yes |
| 1/2 | 16, 1/64 | 0.545 | 172.3, 213.9, 230.8 | -22.3 to -23.4 | -7.1 to -16.8 | -17.8 to -22.4 | yes |
| 1/2 | 16, 4/64 | 0.592 | 183.4, 227.5, 244.8 | -17.6 to -18.4 | -9.2 to -10.9 | -15.4 to -17.8 | yes |
| 1/4 | 3, 1/64 | 0.453 | 147.6, 182.8, 196.2 | -4.9 to -5.4 | +2.6 to +0.8 | -0.7 to -2.3 | no |
| 1/4 | 4, 1/64 | 0.416 | 141.9, 176.0, 188.8 | -8.5 to -9.1 | -0.7 to -2.8 | -5.2 to -7.2 | no (bytes 9 percent) |
| 1/4 | 8, 1/64 | 0.349 | 133.0, 165.2, 178.0 | -13.8 to -14.8 | -7.4 to -10.6 | -12.3 to -14.8 | yes |
| 1/4 | 8, 4/64 | 0.396 | 139.4, 172.9, 185.5 | -10.1 to -10.7 | -2.6 to -5.0 | -7.2 to -9.3 | yes |
| 1/4 | 16, 1/64 | 0.310 | 128.4, 160.6, 172.1 | -16.5 to -17.7 | -10.4 to -14.5 | -15.3 to -18.6 | yes |
| 1/4 | 16, 4/64 | 0.357 | 134.2, 166.8, 179.6 | -13.0 to -14.0 | -6.5 to -9.5 | -11.3 to -13.7 | yes |

(All fifteen rows a rate are in `scripts/71_hybrid_output.txt`.) Against the DEEP fold at every level the hybrid gives back 1.5 to 5.5 points of bytes (the counting bound at the last levels) and wins 2 to 7 points of guest cost, with 8 points in the whole opening instead of 60 to 80, and with levels 1 and later, their Lean proof included, untouched. With it the guest is faster than C whenever the opening is at least 5 percent smaller, at both rates. It is the configuration I would build.

## 6. What could make it unusable, beyond note 68's list

### 6.1 The extractor (checked in `formal/statement.tex` and the paper; the consequences are my analysis, not refereed)

leanVM's end statement is knowledge soundness with a **compiled, straight-line, deterministic extractor of proved running time** (`formal/statement.tex:146-198`): it "descends from the final polynomial to level 0's stack: in each fold round it decodes the previous round's word with at most one error on the columns where the current tuple agrees with the word (on the first $d + 3$ of them)", within a budget of $2^{\max(58, 2\mu + 9)}$. The DEEP-fold paper keeps this ("the extractor never list-decodes: every step is unique decoding of one tuple with at most one error on a set it knows", `sections/05-soundness.tex:133`). Knowledge soundness is not optional here: for a hash-based signature a valid signature always exists, so plain soundness of "there is a signature" says nothing. A tree code breaks the descent at level 0 in two ways.

1. **Erasures.** The step "interpolate through $d + 1$ agreement columns" has no fast analogue: recovering a tree codeword from $\tau n_0$ known leaves spread over the trees is a dense linear system in $k$ unknowns with no algebraic structure I can see (a complete tree would invert by butterflies, but the adversary leaves no subtree of height 2 intact). Gaussian elimination is $k^3$: $2^{54}$ field operations at $\mu = 24$ and $2^{72}$ at $\mu = 30$, against today's budget of $2^{58}$ and $2^{69}$ machine steps. A black-box Krylov solver (Wiedemann: about $2k$ encodings a right-hand side, $2^{54}$ products at $\mu = 30$, 63 lane solves) lands near today's budget (**estimate**), but it is randomized, and its correctness and cost would have to be proved for the cost machine.
2. **Errors.** With a scalar fold a column outside the agreement set of the pinned tuple is repaired by exactly one $\alpha$, and the prover chooses which, so the folded tuple's agreement set contains a wrong column with probability up to $n_0/q$ a round, and $g$ wrong columns with probability up to $n_0/((g+1) q)$. The loss of section 4.2 makes this harmless for soundness and fatal for the descent: decoding a tree code with thousands of errors at unknown places is hopeless (an information set avoids $g$ errors with probability about $(1 - 1/(2\tau))^g$, so $g \le 3$ at most). Hence either the fold grind at level 0 is $\log_2 n_0 - 2$ bits (17 to 25 bits, six times at 64 lanes, five at 32), which is $1.5\, n_0$ permutations at 64 lanes and $1.25\, n_0$ at 32 lanes where $n_0$ is twice as large, 30 to 42 percent of what hashing level 0's Merkle tree costs, **an estimated 4 to 7 percent of proving time at rate 1/2 and 6 to 11 at rate 1/4** (from note 08's measured 15 M permutations a second on one thread and proofs of 1.19 s and 1.64 s on four threads at $\mu = 26$, if the pool's search scales); or soundness stays at 125 bits and knowledge soundness of that message drops to about $128 - \log_2 n_0 + g_f$ bits, 122 with a free grind of $\mu - 11$ bits. Today's affine fold has neither problem: two columns are repaired together with probability $\binom{n}{2}/q^2$, so one error is all the decoder ever meets.

This is the item I would settle before any further work on the list theorem: it is independent of that theorem, and a proved list bound for a code the extractor cannot decode would not meet the statement `formal/` proves today.

### 6.2 All or nothing

Today's protocol degrades gracefully: at the Johnson radius everything is proved. A tree code with a scalar fold has no proved mode at all without the DEEP fold and its own list theorem, because no correlated agreement theorem beyond unique decoding covers it; at unique decoding, $\tau = (1 + \rho)/2$, it needs about 260 queries at rate 1/2 where Reed-Solomon needs 218. There is no partial deployment and no fallback if the theorem's $\varepsilon$ comes out at $4/64$ with $L \le 4$ (the "no" rows of section 5).

### 6.3 Smaller points

- **The repository's rule.** A protocol change lands in both provers, three verifiers and `formal/` together, and CI's Lean job blocks `crates/` until it does. Here that means a machine-checked proof of a probabilistic list-decoding theorem with explicit constants at $n_0 = 2^{26}$, plus section 4.4, plus section 6.1's decoder. I see no way to stage it.
- **An unverifiable public object** (section 4.5): the deployed code is one matrix fixed by Keccak, with no certificate.
- **Two encoders.** Reed-Solomon stays for levels 1 and later and for LeanDA; the tree code adds a twiddle source, a scalar-fold path in three verifiers, and guest bytecode (section 2.5).
- **The guest's sponge and multilinear points**: 30 permutations a point unless tensor-power points are used (section 4.3).
- **Not obstacles**: ring switching, the stacked opening, the partly filled stack, the cache-tiled NTT, `identical_proofs` (the derivation is deterministic), and prover time in T1 (section 3).

## 7. Limits of this note, and reproducing

- Nothing was implemented, compiled or timed. Guest cycles are instruction counts read off `guests/lean_ethereum.py` on top of note 08's one measured profile; prover figures are arithmetic on note 08's and note 24's measurements. Both are **estimates** and are the weakest numbers here; the verdicts at the boundary rows move with them (section 5.2, "Sensitivity").
- The scalar-fold lemma (section 4.2), the boundary row of the hybrid (section 5.4) and the extractor analysis (section 6.1) are sketches by one author and have not been refereed. The Krylov decoder is an idea with an operation count, not a design.
- The tables assume the list hypothesis in the brief's form, a full stack, and the interleaved list $L$ from the paper's projection bound. They do not depend on the distance slack $\varepsilon_0$.
- Bytes and Keccak counts inherit the validation of notes 08 and 67 (measured proofs of today's protocol; the DEEP-fold stream is a specified transcript, not an implemented one).

Reproducing (standard library Python, under a minute in all):

```
python3 scripts/71_payoff.py            # section 5.3; add --bestcap for the retuned cap rule
python3 scripts/71_payoff.py --summary  # section 5.2
python3 scripts/71_payoff.py --points   # section 4.3
python3 scripts/71_hybrid.py            # section 5.4
python3 scripts/71_final_table.py       # the summary's table
```
