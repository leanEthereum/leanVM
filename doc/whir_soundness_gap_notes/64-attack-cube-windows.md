# 64. Adversarial experiments on the cube window (H_2, H_3, H_t)

Researcher 64, round 13. Role: adversary, by experiment first. Every statement below is labelled proved / checked numerically / conjectured.

## 0. Plan

Setting (from note 57): K = GF(2^m), D an F_2-subspace of dimension N with basis b_0..b_{N-1}, n = 2^N, Reed-Solomon of degree below k on D, cube window C = {0, b_0, ..., b_{N-1}}, mixed code c_mu(P)(x) = sum over c in C of mu(x, c) P(x + c) with mu uniform independent. Plan, each item one small script under `scripts/64_*` and one short section here: (1) table-based field arithmetic for GF(2^8) and GF(2^16), encoders, and a check that agreement counts of random pairs match "free agreements plus a 1/q fraction"; (2) confirm that a plain Reed-Solomon list on a quotient domain lifts to the mixed code with a local window (directions b_0, b_1 only) and does not lift with the cube window; (3) search for triples and a word maximizing u_2 + 2 u_3 against 2k for the cube window, random, structured and hill-climbed; (4) free configurations for t = 3, 4, 5 in pure Reed-Solomon, maximizing the sum of (c_x^free - 1)_+ against (t - 1) k; (5) sampling check of the first-moment skeleton at N = 4, q = 16. Added during the round at the lead's request: (6) the same experiments for the random-window design of note 66. Section 7 is the summary.

## 1. Field arithmetic, encoders, pairs (item 1)

Scripts: `scripts/64_lib.py` (log/exp tables for GF(2^4), GF(2^8), GF(2^16); positions are the integers below 2^N, the field element of position v is v, so D = span(1, x, .., x^(N-1)) and the cube window of v is v and its N one-bit flips; Reed-Solomon evaluation, the mixed code, vanishing polynomials, interiors, rank), `scripts/64_item1_pairs.py`, output in `scripts/64_item1_output.txt`.

Prediction [proved, Step 1 of note 57]: for a fixed nonzero difference d, a position x is an agreement with probability 1 if d vanishes on the whole window of x (free) and with probability exactly 1/q otherwise, independently over x. So the number of agreements is |int Z(d)| + Binomial(n - |int Z(d)|, 1/q).

Checked numerically (400 pairs per line, one sampled mu per line). Random pairs have no free agreement and mean agreement n/q; planted pairs (difference = vanishing polynomial of the largest Hamming ball with fewer than k points, times a random cofactor) have exactly the interior of the ball as free agreements.

| q | N | k | random pairs: mean agreements (predicted n/q) | planted ball: size, interior | planted: mean agreements (predicted) |
| --- | --- | --- | --- | --- | --- |
| 2^8 | 4 | 8 | 0.078 (0.063) | 5, 1 | 1.073 (1.059) |
| 2^8 | 5 | 16 | 0.118 (0.125) | 6, 1 | 1.113 (1.121) |
| 2^8 | 6 | 32 | 0.233 (0.250) | 22, 7 | 7.273 (7.223) |
| 2^8 | 6 | 16 | 0.213 (0.250) | 7, 1 | 1.218 (1.246) |
| 2^16 | 6 | 32 | 0.000 (0.001) | 22, 7 | 7.000 (7.001) |
| 2^16 | 6 | 16 | 0.000 (0.001) | 7, 1 | 1.000 (1.001) |

The other lines of the output file agree in the same way. Remark that matters for everything below [proved, Harper]: at toy size the interiors are tiny (the best set with fewer than 32 points of the 6-cube has interior about 9), so (H_2) is nowhere near tight at toy size, and any toy experiment on free agreements must be read through the ratio to the isoperimetric bound, not through the ratio to k.

## 2. Local windows are broken, the cube window is not broken by the same lists (item 2)

Scripts: `scripts/64_item2_local.py`, `scripts/64_item2_flats_diag.py`, output `scripts/64_item2_output.txt`. Setting: GF(2^8), N = 6, W = span(b_0, b_1), L_W the subspace polynomial of W, quotient domain D' = L_W(D) (16 points), k' = k/4. A triple 0, Q_1, Q_2 of plain Reed-Solomon on D' is lifted to P_i = Q_i(L_W(X)), of degree below k.

Pointwise identity for plain Reed-Solomon triples [proved]: with P_0 = 0, P_1 = d_1, P_2 = d_2 and the best word, u_2 + 2 u_3 = |Z(d_1)| + |Z(d_2)| + |Z(d_1 + d_2)| - |Z(d_1) ∩ Z(d_2)| (a common zero lies in all three zero sets and counts 2). With c common zeros and three otherwise disjoint fibres of k' - 1 - c points this is 3(k' - 1) - c, subject to c + 3(k' - 1 - c) <= n'. At rate 1/4 take c = 0: 3(k' - 1) against 2k'. At rate 1/2 the common zeros are necessary: c = 3, k' = 8, n' = 16 gives 18 against 16.

Checked numerically (20 sampled mu per line; "free" lists the free agreements of the pairs (0,1), (0,2), (1,2)):

| k | quotient triple, u_2 + 2u_3 on D' (2k') | local window: free, then u_2 + 2u_3 min / mean / max | cube window: free, then u_2 + 2u_3 min / mean / max | 2k |
| --- | --- | --- | --- | --- |
| 16 | 9 (8) | 12, 12, 12; 36 / 36.35 / 38 | 0, 0, 0; 0 / 0.85 / 3 | 32 |
| 32 | 17 (16) | 28, 28, 24; 68 / 68.15 / 70 | 0, 0, 0; 0 / 0.65 / 2 | 64 |
| 32 | 18 (16) | 28, 28, 28; 72 / 72.05 / 73 | 0, 0, 0; 0 / 1.15 / 3 | 64 |

So with the local window every sampled mu violates (H_3) (36 > 32, 68 and 72 > 64), by exactly four times the quotient excess, all of it free, as Section 10 of note 57 says. With the cube window the same three polynomials have no free agreement at all (the zero sets are unions of cosets of W, and a union of fewer than 16 cosets of a proper coordinate subspace of the 4-cube quotient has empty interior here) and u_2 + 2u_3 is the random term 3n/q = 0.75.

Diagnostic [checked numerically]: among 200000 random choices of two disjoint 4-point root sets A, B in D', 12 gave a third full fibre (f_A + lam f_B with 4 more roots in D'); the generic prediction is 0.06, and in all 12 the three fibres are flats (cosets of 2-dimensional subspaces). So the excess triples of plain Reed-Solomon on a subspace domain are the flats family, about 200 times more frequent than genericity predicts at this size. Flats have empty interior for the cube window [proved: a coset of a proper subspace U contains a window only if all b_i lie in U], which is the structural reason the cube window kills them.

## 3. (H_3) at toy size, cube window, one sampled mu (item 3)

Script: `scripts/64_item3_h3.py m N k iters seed`, output `scripts/64_item3_output.txt`. Triples are (0, d_1, d_2), the word is free (at each position the value shared by the most members), and the score is u_2 + 2u_3.

Three adversaries. A: random d_1, d_2 (300 samples). B: structured families chosen without looking at mu (100 members each): both differences vanish on one Hamming ball; d_1 and d_2 vanish on two antipodal balls; d_1 = lam d_2 + Z_B e (ratio constant on a ball, no free agreement but "cheap doubles": on the interior the three symbols coincide as soon as two do); periodic d_i = A_i(L_U) with U = span(b_0, b_1). C: adaptive, sees mu: each "pair agrees at x" is one linear condition on (d_1, d_2) in K^(2k), so 2k - 1 conditions can always be imposed [proved: generic linear algebra, this is the 2k of the claim]; the search imposes 2k - 2, takes the best member of the 2-dimensional kernel (each further agreement is one root on the pencil), re-imposes a random subset of what holds and repeats.

Prediction including the field-size term [proved as a first moment, not as a maximum]: the expected number of (triple, pattern) with score C is at most Npat(C) q^(2k - 1 - C), with Npat(C) the number of cover patterns of score C; so the maximum should be at most about 2k - 1 + e*, e* the largest e with Npat(2k - 1 + e) >= q^e. This is the "+ small" of (H_3): e* is about 3 H n / log2 q, large for a toy field.

Checked numerically:

| q | N | k | 2k | A: mean, max (3n/q) | B common ball: free, mean, max | B two balls: mean, max | B ratio ball: mean, max | B periodic: mean, max | C adaptive best | ceiling 2k - 1 + e* |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2^8 | 5 | 16 | 32 | 0.35, 3 (0.375) | 2, 2.36, 4 | 2.48, 5 | 0.43, 3 | 0.26, 2 | 35 | 39 |
| 2^8 | 6 | 32 | 64 | 0.71, 4 (0.75) | 14, 14.62, 18 | 14.59, 17 | 0.77, 4 | 0.61, 3 | 67 | 80 |
| 2^8 | 6 | 16 | 32 | 0.72, 4 (0.75) | 2, 2.68, 5 | 2.74, 6 | 0.71, 3 | 0.79, 3 | 36 | 48 |
| 2^16 | 6 | 32 | 64 | 0.003, 1 (0.003) | 14, 14.00, 14 | 14.01, 15 | 0.00, 0 | 0.00, 0 | 64 | 71 |

Reading. (i) Nothing exceeds the ceiling; the adaptive search exceeds 2k itself by 3 or 4 at q = 2^8 and by 0 at q = 2^16, which is the behaviour of the 1/q term, not of a structure (the excess over 2k - 1 drops from 4 to 1 when q is squared, with the same code and search). (ii) The structured families score exactly their free count plus the random term: 2 |int B| + 3n/q, far below 2k at toy size (14 against 64 at N = 6, k = 32). (iii) Free agreements never pay for themselves in a family cut out by independent vanishing conditions [proved]: making d vanish on a set H costs |H| dimensions of the family and gives |int H| < |H| free units, and a ratio ball gives |int B| cheap doubles for |B| - 1 dimensions, so the adaptive score inside such a family is 2k - 1 minus the boundary sizes. Hence the only way to beat 2k + e* is a rank-deficient configuration (more vanishing conditions holding than the dimension count allows) whose coincidence sets have interior. Item 4 searches for exactly that.

Accounting that the proof must use [proved, from Step 1 of note 57]: for a triple put G = common zeros of d_1, d_2 and F_lam = Z(d_1 + lam d_2) minus G for lam in P^1(K) (all fibres, not only 0, 1, infinity). A position costs nothing for two units if its window lies in G, costs nothing for one unit (one more for the second) if its window lies in G ∪ F_lam with lam in {0, 1, infinity}, and costs one for two units if its window lies in G ∪ F_lam for another lam. So the deterministic quantity to bound is Phi = |int G| + |union over lam of int(G ∪ F_lam)| (the interiors pairwise meet exactly in int G), against 2k minus the dimension of the family of such (d_1, d_2).

## 4. Free configurations of t = 3, 4, 5 Reed-Solomon codewords, cube window (item 4)

Scripts: `scripts/64_item4_free.c`, `scripts/64_item4_run.sh`, output `scripts/64_item4_output.txt`. No mu here: the score of t polynomials of degree below k is the sum over x of (c_x^free - 1)_+, c_x^free the largest number of them coinciding on the whole window of x.

Method. The state is the linear space S of tuples (P_1, .., P_{t-1}) (P_0 = 0) satisfying the coincidences imposed so far, kept as a basis in evaluation form. A move imposes P_i = P_j on one more window; its rank cost is the dimension it removes from S, its geometric cost the number of window points where P_i = P_j was not already forced. All forced coincidences are recomputed from S after each move, so a rank-deficient configuration (the only way to beat the dimension count, Section 3) shows up as rank cost below geometric cost, or as coincidences that come for free. Moves forcing two polynomials to be equal are refused. The greedy rule takes the move of least rank cost per unit of score, with four levels of random jitter; 2000, 1000, 400 restarts for t = 3, 4, 5. It rediscovers the common ball, the "sunflower" (P_i - P_0 vanishing on different balls) and mixtures.

Checked numerically (identical best scores over GF(2^8) and GF(2^16)); I(k-1) is Harper's maximal interior of a set of k - 1 points (note 60's script):

| N | k | t | best score found | (t-1) k | (t-1) I(k-1) (common ball) | score / (t-1)k | largest deficiency (geometric minus rank cost) over all runs |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | 16 | 3, 4, 5 | 9, 14, 18 | 32, 48, 64 | 8, 12, 16 | 0.28, 0.29, 0.28 | 0, 0, 2 |
| 5 | 8 | 3, 4, 5 | 2, 4, 5 | 16, 24, 32 | 2, 3, 4 | 0.13, 0.17, 0.16 | 0, 2, 2 |
| 6 | 32 | 3, 4, 5 | 22, 33, 43 | 64, 96, 128 | 20, 30, 40 | 0.34, 0.34, 0.34 | 1, 0, 0 |
| 6 | 16 | 3, 4, 5 | 5, 9, 11 | 32, 48, 64 | 4, 6, 8 | 0.16, 0.19, 0.17 | 1, 4, 4 |

Reading. (i) Nothing comes near (t - 1)k at toy size; the best scores are the common-ball value (t - 1) I(k - 1) plus 1 to 3 units, and the ratio to (t - 1)k is the isoperimetric interior ratio of the toy cube (I(31)/31 = 0.32 in the 6-cube), the same for t = 3, 4, 5. In every final state the score is far below the rank spent (22 for 63, 33 for 95, 43 for 126 at N = 6, k = 32). (ii) Rank deficiency does occur, with the same values over both fields, so it is structural: it is the flats mechanism in its smallest form. Example [proved]: if Z_A = g (L + a) and Z_B = g (L + b) with L(X) = X^2 + sigma X, then every member of the pencil is g (L + c) and vanishes on a pair {y, y + sigma}, so one rank buys two zeros. The deficiency found is at most 4 and the scores stay within 3 units of the common-ball value. (iii) Why flats cannot scale for the cube window [dimension count for the pencil g (L_U + c), same status as the first moment of Section 3, not a bound on a maximum]: its fibres are cosets of U, a coset of a proper subspace has empty interior, so every interior point of G ∪ F_lam must have its N - dim U outside neighbours in G = Z(g), and G costs 2|G| dimensions of the family; the adaptive score of that family is at most 2k - 2|G| + |U| + 8 with |G| >= (N - dim U)|U|, below 2k.

## 4b. The combinatorial relaxation at N = 25: what pairwise sizes plus isoperimetry cannot prove (item 4, continued)

Script: `scripts/64_item4b_relax.py`, output `scripts/64_item4b_output.txt`. Relaxation: every point y carries a partition of {0..t-1} (who coincides at y), the only constraint kept from Reed-Solomon is that each pair coincides on at most k - 1 points, and the score is the sum over x of (largest class of the meet over the window of x) - 1. Sets are unions of cells of the 25-cube (cells = pairs of weights on a 12 + 13 split of the coordinates, 182 cells, exact binomial weights), optimized by simulated annealing (800000 moves) from three seeds. Any proof of the free part of (H_t) that uses only the sizes of pairwise coincidence sets and the cube isoperimetry has to beat these values.

Checked numerically (lower bounds on the maximum of the relaxation, rate 1/2, N = 25):

| t | common ball, (t-1) I(k-1) / (t-1)k | best found / (t-1)k | structure of the best |
| --- | --- | --- | --- |
| 3 | 0.690 | 0.760 | common zeros G plus three fibres |
| 4 | 0.690 | 0.895 | four regions cut by two orthogonal half-cubes, region e = "all but polynomial e coincide" |
| 5 | 0.690 | 0.846 | same family, annealed |

Reading. (i) For t = 3 the lead's "trivial with room at rate 1/2" (note 57, Section 10, item 2) is not established as written: the three zero sets Z(d_1), Z(d_2), Z(d_1 + d_2) are not disjoint, they share the common zeros G, where all three members coincide and the position counts twice. With f_i = |int(G ∪ F_i)| and g = |int G| the free score is f_1 + f_2 + f_3 - g, and the two obvious bounds, 3 I(k - 1) - g and n + g, only give 2.03 k at N = 25 [proved, arithmetic with Harper's value I(k-1) = 0.690 k]. The best configuration found reaches 1.52 k, so the statement is probably true with room, but it needs a stability argument (three near-extremal sets pairwise meeting in the same set), not disjointness. Note 66 lists this as open for N >= 23, consistently. (ii) For t = 4 the relaxation reaches 2.68 k of the 3 k allowed at N = 25, and its limit for large N is 4k [heuristic computation: with boundary fraction b of each half-cube and independent boundaries the score is 2(1 - b) n, and b tends to 0], above 3k as soon as b < 1/4 (N of order 40). Pointwise, this pattern is realized by plain Reed-Solomon exactly when the four regions are the four fibres of one rational function of degree n/4 (the vanishing polynomials of the regions span a pencil), for instance the four cosets of a subspace of codimension 2 with k = n/2 + 1 [proved, by solving P_1 = e_1 Z_2 Z_3 and so on; checked numerically by `scripts/64_item4b_cosets.py` at N = 4 and 6: pointwise sum 32 against 3k = 27 and 128 against 99, largest pairwise agreement k - 1, free sum 0 for the cube window]; cosets have empty interior, so the cube window kills this realization, but nothing in "pairwise sizes plus isoperimetry" does. So for the cube the free part of (H_4) and (H_5) needs a Reed-Solomon-specific statement (no rational function of degree n/4 has four ball-like fibres), exactly the point where note 66 abandons the cube.

## 5. The first moment checked exhaustively at q = 16 (item 5)

Scripts: `scripts/64_item5_exhaustive.c`, `scripts/64_item5_merge.py`, outputs `scripts/64_item5_exhaustive_output.txt` (per mu) and `scripts/64_item5_merged_output.txt`. Parameters: q = 16, N = 4 (D = K, n = 16), k = 4, cube window (5 points), 2k = 8. Instead of a sample of triples the program enumerates ALL 2.1 * 10^9 unordered pairs {d_1, d_2} of distinct nonzero polynomials (every triple (0, d_1, d_2); each triple of codewords up to translation and scaling is counted 45 times), for 256 sampled mu, about 3 seconds each.

Prediction [proved, Step 1 of note 57, exact here]: a window has 5 points and a nonzero polynomial of degree below 4 has at most 3 zeros, so no window is deficient unless the triple is collinear. For a non-collinear triple the position scores are independent with P(2) = 1/q^2, P(1) = 3(q - 1)/q^2; for a collinear one P(2) = 1/q, else 0. The expected number of pairs with score C is the sum of the two convolutions.

Checked numerically (256 mu):

| score C = u_2 + 2u_3 | c = C - 2k - 1 | mean number of pairs at C | standard error | exact expectation | fraction of mu with some triple at C or more | first-moment bound E[N >= C] / 45 |
| --- | --- | --- | --- | --- | --- | --- |
| 9 | 0 | 2.143e6 | 2.3e4 | 2.140e6 | 1.000 | 1 |
| 11 | 2 | 7.091e4 | 2.4e3 | 7.088e4 | 1.000 | 1 |
| 12 | 3 | 1.011e4 | 597 | 1.015e4 | 1.000 | 1 |
| 13 | 4 | 1179 | 117 | 1207 | 0.973 | 1 |
| 14 | 5 | 125.6 | 19 | 134.6 | 0.508 | 1 |
| 15 | 6 | 9.49 | 2.7 | 10.81 | 0.098 | 0.279 |
| 16 | 7 | 0.82 | 0.58 | 1.63 | 0.012 | 0.039 |
| 17 | 8 | 0.18 | 0.18 | 0.05 | 0.004 | 0.002 |

Reading. The expectation is matched at every level within the standard error (the counts are heavy-tailed over mu: with the first 64 samples alone the means at C >= 12 were 20 to 40 percent low, two standard errors). The probability that some triple violates u_2 + 2u_3 <= 2k + c is below the first-moment bound by a factor about 3 where the bound is not trivial (c = 6, 7: 0.098 against 0.279, 0.012 against 0.039), and the single event at c = 8 (one mu of 256) is within the fluctuation of a bound of 0.002. The maximum over all triples is 13 or 14 for 88 percent of the mu, that is 2k + 5 or 2k + 6: at q = 16 the "+ small" of (H_3) is 6 to 9, as the first moment says, and nothing beyond it. For k = 8 at the same N the triple space has 2^64 elements and windows can be deficient; I did not sample it, since the adaptive search of Section 3 already covers larger k.

## 6. Random windows (note 66): c(P)(x) = P(x) + sum over l <= d of mu_l(x) P(pi_l(x)) (added at the lead's request)

Scripts: `scripts/64_rw_lib.py` (window tables, the code above, interiors, a randomized greedy plus swap search for the set of at most s points with the largest interior), and one script per experiment below. Partners are d distinct uniform positions different from x (axiom W1). Expansion statements need n large; every table gives the trend with N.

### 6a. Largest interior of a set of fewer than k points

Script `scripts/64_rw_interior.py`, output `scripts/64_rw_interior_output.txt`. Since every set of at most k - 1 points is the zero set of a polynomial of degree below k [proved], the largest free agreement of a pair is exactly the graph quantity max |int Z| over |Z| <= k - 1, no algebra involved. The search gives lower bounds on that maximum; on the cube it returns Harper's exact optimum in all ten cases (N = 4 to 8, both rates; 1, 4, 10, 26, 55 of k - 1 at rate 1/2), and on random graphs it equals the exhaustive optimum in 36 of 36 small cases (n = 16 and 32, sets of 7 points, d = 2, 4, 6, six graphs each; `scripts/64_rw_exact_small.py`), so it is a reasonable optimizer at toy size. gamma* is the first-moment ceiling of note 66 at the same density (the largest g with phi D(g || phi^d) <= H(phi)), valid for large n only.

Checked numerically, max |int Z| / (k - 1), rate 1/2 (4 or 5 sampled graphs, the maximum over graphs is shown):

| N | n | cube (d = N) | d = 2 | d = 4 | d = 6 | d = 8 |
| --- | --- | --- | --- | --- | --- | --- |
| 4 | 16 | 0.143 | 1.000 | 0.429 | 0.143 | window too large |
| 5 | 32 | 0.267 | 0.867 | 0.533 | 0.333 | 0.200 |
| 6 | 64 | 0.323 | 0.871 | 0.581 | 0.355 | 0.258 |
| 7 | 128 | 0.413 | 0.889 | 0.587 | 0.413 | 0.286 |
| 8 | 256 | 0.433 | 0.882 | 0.606 | 0.394 | 0.291 |
| gamma* (n large) | | 0.69 at N = 25 (Harper) | 1.00 | 0.71 | 0.50 | 0.37 |

Rate 1/4, same order of columns: N = 6: 0.133, 0.800, 0.333, 0.200, 0.133; N = 7: 0.258, 0.774, 0.419, 0.258, 0.194; N = 8: 0.270, 0.778, 0.429, 0.286, 0.206; gamma* 0.91, 0.53, 0.35, 0.25 for d = 2, 4, 6, 8.

Reading. (i) At equal degree the random graph is no better than the cube at toy size (d = 6 at N = 6: 0.355 against 0.323); the advantage is that d stays fixed while the cube's interior fraction grows with N to 0.69. (ii) For fixed d the measured values rise slowly with N and stay below gamma*: at n = 256 they are 0.61, 0.39, 0.29 for d = 4, 6, 8 against ceilings 0.71, 0.50, 0.37. The truth for large n is between the two; the search is a lower bound. (iii) d = 2 is useless: nearly closed sets exist (interior fraction 0.87 to 1.0 at every N; the first moment allows fully closed sets of density above 1/e [proved: the expected number of closed sets of size z is about exp(z (1 - (d - 1) ln(n/z)))]). (iv) d = 4 already exceeds 1/2 at N = 5 and reaches 0.61 at N = 8, so it cannot satisfy the gamma <= 1/2 that the crude bound of note 66 (Section 3, item 2b) needs at rate 1/2; d = 6 is borderline (measured 0.41, ceiling 0.50); d = 8 has room (measured 0.29, ceiling 0.37).

### 6b. (H_3) and free configurations with random windows

Scripts `scripts/64_rw_h3.py` (the three adversaries of Section 3), `scripts/64_item4_free.c` with two more arguments (d and a graph seed; `scripts/64_rw_free_run.sh`), outputs `scripts/64_rw_h3_output.txt`, `scripts/64_rw_free_output_N5.txt`, `scripts/64_rw_free_output_N6.txt`.

(H_3), N = 6, k = 32, 2k = 64, checked numerically:

| q | d | A random: mean (3n/q) | B common zero set of 30 points: interior, free score, max over 100 | C adaptive best (300 iterations) | ceiling 2k - 1 + e* |
| --- | --- | --- | --- | --- | --- |
| 2^8 | 2, 4, 6, 8 | 0.73, 0.77, 0.74, 0.72 (0.75) | 26, 17, 10, 7; 52, 34, 20, 14; 54, 37, 23, 17 | 66, 68, 67, 66 | 80 |
| 2^16 | 2, 4, 6, 8 | 0.003, 0, 0.003, 0.003 (0.003) | same sets; 52, 34, 20, 14; 52, 34, 21, 14 | 65, 64, 64, 64 | 71 |

At N = 5, k = 16, q = 2^16, 800 iterations, four seeds each: adaptive best 32 = 2k for d = 2 and for d = 6 alike. So the adaptive score does not depend on d and equals the cube's (Section 3): 2k - 1 from linear algebra plus the 1/q term. The free part is 2 |int Z| exactly, at most 52 of 64 even at d = 2.

Free configurations, greedy rank search, GF(2^16), two graphs each, best score / (t - 1)k for t = 3, 4, 5:

| N, k | d = 2 | d = 4 | d = 6 | d = 8 | cube (Section 4) |
| --- | --- | --- | --- | --- | --- |
| 5, 16 | 23/32, 35/48, 47/64 | 16/32, 23/48, 30/64 | 10/32, 15/48, 19/64 | 6/32, 9/48, 12/64 | 9/32, 14/48, 18/64 |
| 6, 32 | 55/64, 83/96, 109/128 | 35/64, 50/96, 66/128 | 22/64, 33/96, 43/128 | 17/64, 25/96, 32/128 | 22/64, 33/96, 43/128 |
| 5, 8 | 10/16, 15/24, 20/32 | 4/16, 6/24, 8/32 | 2/16, 3/24, 4/32 | 0, 0, 0 | 2/16, 4/24, 5/32 |
| 6, 16 | 24/32, 35/48, 46/64 | 12/32, 17/48, 23/64 | 7/32, 10/48, 13/64 | 5/32, 7/48, t = 5 not run to the end | 5/32, 9/48, 11/64 |

In every case the best score is (t - 1) times the largest interior of 6a, within one or two units, the largest rank deficiency seen is 1, and the score stays below the rank spent (score minus cost between -2 and -6 at d = 2, where sets are nearly closed, and -15 or lower at d = 6, 8). So with random windows, as with the cube, the search finds nothing better than "all t members coincide on the best-interior set", which is always below (t - 1)k because that set has fewer than k points.

### 6c. Structures that could survive random windows

Scripts `scripts/64_rw_lift.py`, `scripts/64_rw_pool.py`, outputs `scripts/64_rw_lift_output.txt`, `scripts/64_rw_pool_output.txt`.

1. Subspace structures do not survive [checked numerically]. The lifted flats triples of Section 2 (pointwise u_2 + 2u_3 = 36 against 2k = 32, and 72 against 64) keep, under random windows, exactly the free agreements of sets independent of the graph, |Z| (|Z|/n)^d in expectation: total over the three zero sets 1.2, 0.05, 0, 0 for d = 2, 4, 6, 8 at k = 16 (prediction 1.1, 0.03, 0, 0) and 15.2, 2.6, 0.5, 0 at k = 32 (prediction 15.4, 2.8, 0.5, 0.1); u_2 + 2u_3 is that plus 3n/q.

2. What algebra can and cannot do [proved, with the order of the choices: domain, then graph from the oracle, then the adversary]. (i) A single coincidence set can be any set of fewer than k points, so the pair bound is the graph's expansion and nothing else. (ii) t members coinciding on one set Z of at most k - 2 points are generic, score (t - 1)|int Z|; this is what every search above finds. (iii) Anything larger needs at least two different coincidence sets with large interior whose vanishing conditions are dependent (rank deficiency), and then the sets are tied by an algebraic relation: for t = 3 they are G ∪ F_0, G ∪ F_1, G ∪ F_infinity for three fibres of one rational function d_1/d_2. The expansion axiom (W2) is a statement about all sets, proved by a first moment over the graph with 2^n sets, so it bounds every interior whatever the algebra: the free score of a triple is at most 3 gamma k - |int G|, of t members at most gamma (2t - 3) k (note 66). So with gamma <= 1/2 at rate 1/2 no algebraic structure can matter for the free part, and the question "is there an algebraic way" is only relevant when gamma is too large for these bounds (d <= 4, or lower rates). (iv) In that regime the adversary needs rank-deficient configurations whose sets are nearly closed under the partner maps. The only rank-deficient mechanism seen in any search here is the flats pencil g (L_U + c), whose fibres are cosets of one subspace U. For a graph drawn after the domain is fixed, a coset of U has interior fraction about (|U|/n)^d, and since D has at most 2^(N^2) subspaces a union bound over all of them costs nothing [proved]; cosets can be glued by common zeros G = Z(g) (a window inside G plus one coset is deficient), but each point of G costs two dimensions of the family. I know no family of rank-deficient plain Reed-Solomon configurations rich enough (of order 2^(d n) set systems would be needed to defeat a first moment over the graph) and none appeared in the greedy searches (deficiency at most 1 with random windows, at most 4 with the cube). Conjectured: none exists that helps; not needed if gamma <= 1/2.

3. Pooled offsets are a real risk [proved for the bound, checked numerically at toy size]. If partners are x XOR c with c drawn from a public pool of P offsets, any hyperplane U of D containing a fraction f of the pool has interior fraction at least f^d (a position all of whose offsets lie in U stays in its coset), and some hyperplane has f >= (N - 1)/P. For the pool = the N basis directions (a sparse cube) this is ((N - 1)/N)^d = 0.72 at N = 25, d = 8: broken, worse than the full cube. Measured max |int Z| / (k - 1) at rate 1/2, d = 8: N = 7: P = 2N 0.33, P = 4N 0.32, all offsets 0.29; N = 8: basis 0.43, P = 2N 0.48, P = 4N 0.34, all offsets 0.30. At d = 6, N = 8: basis 0.50, P = 2N 0.43, P = 4N 0.40, all offsets 0.39. So a pool of 2N offsets is visibly worse than random at toy size, 4N is close to random, and the pool must in any case be large enough that no hyperplane (more generally no subspace of small codimension) contains most of it; a pool spanning a proper subspace W is the local window of Section 2 again (cosets of W are closed).

## 7. Summary

Nothing found breaks (H_3), (H_4) or (H_5) for the cube window, nor for random windows with d >= 4, at any toy size tried. What the experiments do establish:

1. [checked numerically] Local windows are broken exactly as Section 10 of note 57 says (36 > 32, 68 and 72 > 64 for every mu at N = 6), by flats triples of the quotient, which are about 200 times more frequent than generic at that size; the cube window and random windows remove all their free agreements.
2. [checked numerically, exhaustive at q = 16] The first moment of Step 1 is exact in expectation and within a factor 3 as a tail bound; the maximum of u_2 + 2u_3 is 2k - 1 plus a field-size term (2k + 5 or 6 at q = 16, n = 16; 2k + 2 to 2k + 4 at q = 2^8, n = 32 and 64, by search; 2k or 2k + 1 at q = 2^16), never beyond the first-moment ceiling.
3. [checked numerically] Free configurations, cube or random windows, t = 3, 4, 5: the best found is always (t - 1) times the largest interior of a set of k - 1 points, plus at most 3 units; rank deficiency exists (flats pairs, at most 4) but is never large enough to pay for the boundary.
4. [proved, and it matters for the proof] For the cube the free part is not controlled by "pairwise sizes plus isoperimetry": for t = 3 the common zeros make the trivial bound 2.03 k at N = 25, rate 1/2 (best configuration found 1.52 k), and for t = 4, 5 the relaxation reaches 0.895 and 0.846 of (t - 1)k at N = 25 and exceeds it for larger N. This agrees with note 66's decision to leave the cube.
5. [checked numerically at toy size, ceilings from the first moment] Random windows: interior fractions at rate 1/2 are about 0.88 (d = 2), 0.61 (d = 4), 0.39 to 0.41 (d = 6), 0.29 (d = 8) at n = 128 to 256, rising slowly with N toward ceilings 1, 0.71, 0.50, 0.37. So d = 2 and d = 4 do not give gamma <= 1/2, d = 6 is borderline, d = 8 has room. Pooled offsets need a pool of about 4N or more; a basis pool has gamma >= 0.72 at N = 25, d = 8.

Open, for whoever proves (W2): beyond n = 32 the toy maxima are lower bounds from a heuristic search (exact on the cube and on the small random graphs checked); how far below gamma* the truth sits for n large is not settled by these sizes.
