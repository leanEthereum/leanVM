# 38. The attack frontier of the DEEP-fold protocol (written by the lead from researcher 38's hand-back)

Researcher 38 was cut off before writing its note. This file records its reported results so they are not lost. Scripts: `scripts/38_gf.py`, `38_lists_check.py`, `38_exact_small.py`, `38_families.py`, `38_collide.c`, `38_frontier.py` (all ran), `38_line_attack.py` (did NOT finish: untested), output of `38_frontier.py` in `scripts/38_frontier_output.txt`. Status labels are the researcher's; nothing here was refereed.

## 1. Best list lower bound as a function of the agreement fraction

**New family, "nested half-supports" [proved by hand from the gap lemma, checked].** Let $Q_c(X)$ be the subsets of an affine space $X$ that are disjoint unions of flats of codimension at most $c$ with total size $|X|/2$. Then $|Q_1| = 2^{m+1} - 2$, $|Q_2| = (2^m - 1)(2^m - 2)(2^{m+1} - 8)/6 + 2^{m+1} - 2$ (brute force agrees at $m = 3, 4, 5$: 70, 870, 8742), and $|Q_c| \ge |Q_2(m - c + 2)|^{2^{c-2}}$.

- Rate 1/2, agreement $(1/2 + 2^{-(c+1)})n$, degree $\le n/2$: at least $3\prod_{i=1}^{c-1} q_i(N - c + i)$ polynomials for one word. This improves the stacking count of note 05.
- Rate $2^{-R} \le 1/4$, agreement $\rho(1 + 2^{-c})n$, degree $\le k$: at least $(2^{R+c} - 1) \cdot (\text{admissible flats}) \cdot (q_c(N - R + 1) - 2^{N-R+2} + 2)$.

Checks: all 36540 members enumerated at $N = 5$, $c = 3$; random members at $N = 6..9$ for rates 1/2 to 1/16; at rate 1/4, $N = 6$, $c = 2$ the exact count is 5,723,325 against the bound 130,200.

**Step function at level 0** ($\log_2$ of the list size, degree $\le k$, $N = 24 + R$):

| rate | agreement fraction: $\log_2 L$ |
| --- | --- |
| 1/2 | $3/4$: 1.6; $5/8 + 2^{-(m'+2)}$: $2m' - 2$ (padding); $5/8$: 30.8; $9/16$: 96.0 (new; 102.7 quoted from DKTZ26, unverified); $17/32$: 226.8 (new); $33/64$: 474.5 (new); below $0.5156$: pigeonhole, astronomically large |
| 1/4 | $1/2$: 27.0; $3/8$: 31.8; $5/16$: 77.3; $9/32$: 145.8; $17/64$: 275.6; below $0.2630$: pigeonhole |
| 1/8 | $1/4$: 53.4; $3/16$: 55.3; $5/32$: 105.4; $9/64$: 173.8; below $0.1339$: pigeonhole |
| 1/16 | $0.1523$: 15.6 (not refereed); $1/8$: 79.6; $3/32$: 81.6; $5/64$: 132.8; $9/128$: 201.2; below $0.0681$: pigeonhole |

Roughly $\log_2 L(\rho + \epsilon) \approx 3N/(8\epsilon)$ at rate 1/2 until $\epsilon \approx H(\tau)/64$, where the pigeonhole takes over. Nothing found puts a list of $2^{128}$ or more above $17/32$ at rate 1/2.

## 2. Attack frontier

Requirement used for a real attack: the number of list members through one domain column must be at least $2^{11} q^{s-1}$ for weights independent of the list ("generic", the leanVM case), and $2^{11} q^{s-2}$ when the weighted claim may be chosen adversarially after the points ("worst case"; inherited from note 20 Proposition R3 and note 16, NOT confirmed by researcher 38).

| rate | Johnson (queries) | $s = 2$ generic | $s = 2$ worst case | $s = 3$ generic | $s = 3$ worst case | $s \ge 4$ (both) | gap at $s \ge 4$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 0.7071 (216) | 17/32 (119) | 0.627 (161) | 33/64 (114) | 17/32 (119) | 0.5156 (114) | 102 queries, 47% |
| 1/4 | 0.5 (108) | 9/32 (60) | 1/2 (108) | 17/64 (57) | 9/32 (60) | 0.263 to 0.266 (57) | 51, 47% |
| 1/8 | 0.3536 (72) | 9/64 (39) | 1/4 (54) | 0.1339 (38) | 9/64 (39) | 0.1339 (38) | 34, 47% |
| 1/16 | 0.25 (54) | 9/128 (29) | 0.1523 (40) | 0.0681 (28) | 9/128 (29) | 0.0681 (28) | 26, 48% |

From $s = 4$ or 5 on the frontier is the pigeonhole value $\rho + H(\tau)/64$ and does not move with $s$ up to 40.

Later levels (level-0 rate 1/2), bits per query: Johnson 2.0, 3.5, 5.0, 6.5, 8.0 at levels 1 to 5; generic $s = 2$ frontier 3.83, 6.68, 9.68, 12.63, 15.48; capacity 4, 7, 10, 13, 16.

## 3. How the gap splits

- The proof (Theorem 5.2 of the paper, level 0, one batch) tolerates $\log_2 L \le (104s - 1062)/3$. A fold lemma as good as pinning would tolerate about $52s - 54$. A real attack needs about $128(s - 1) + 11$.
- **In threshold terms the whole gap is the list bound.** If lists were no larger than the lower bounds above, the paper's theorem would already hold just above each step with 13 points above $9/16$, 17 above $17/32$, 24 above $33/64$ at rate 1/2, within one dyadic step of the frontier. The slack in the fold lemma costs points only, not queries.
- The trivial counting bound is useless at levels 0 to 3. It beats Johnson at level 5 with 11 points today and at level 4 only with 50 points.

## 4. Collision statistics (toy fields, checked)

Collisions of list members at a point in the domain are exactly the members through that column. For flats at rate 1/4 there are no collisions outside the domain at all, so the pair-collision probability is exactly $(n/q)^s$. For the other families collisions outside $K$ are within a factor of about 0.7 to 4 of the random model.

## Not done

Items 1(c) and 1(e) of the brief beyond notes 15 and 20; independent verification of the DKTZ26 counts; confirmation of the worst-case column.
