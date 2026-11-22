# Lead notes for the research swarm

Read `doc/whir_soundness_gap.md` first (the problem statement), then this file, which corrects and sharpens it. Notation as there: $K = \mathrm{GF}(2^{64})$, $E$ its quadratic extension, $D = D_{\kappa,R}$ the $\mathbb{F}_2$-span of $1, x, \dots, x^{N-1}$ in $K$ with $N = \kappa + R$, $n = 2^N$, rate $\rho = 2^{-R}$, genuine codewords have degree $< 2^\kappa$, the analysis degree is $d = 2^\kappa - 1 + \ell$. $\Lambda(T)$ is the largest list at agreement $T$.

Status of every claim below: derived by hand by the lead, not machine-checked. Verify before building on it.

## 1. Flats: Johnson is tight at rate 1/4 on subspace domains

For an $\mathbb{F}_2$-subspace $V \subseteq D$ of size $2^s$, $L_V(X) = \prod_{v \in V}(X - v)$ is linearized: $L_V = X^{2^s} + c_{s-1}X^{2^{s-1}} + \dots + c_0 X$. So $Q_V(X) := (L_V(X) - X^{2^s})/X$ has degree $2^{s-1} - 1$, and $Q_V(x) = x^{2^s - 1}$ for every $x \in V \setminus \{0\}$.

Take $s = \kappa + 1$. Then $\deg Q_V = 2^\kappa - 1$ (a genuine codeword), and the single word $w(x) = x^{2^{\kappa+1}-1}$ agrees with $Q_V$ on $2^{\kappa+1} - 1 = 2\rho n - 1$ points, for every subspace $V$ of codimension $R - 1$. Distinct $V$ give distinct $Q_V$. Hence
$$\Lambda(2\rho n - 1) \ \ge\ \binom{N}{R-1}_2 \approx 2^{(R-1)(\kappa+1)} .$$
At $R = 2$ (rate 1/4) this is $2^N - 1 \approx 2^{26}$ genuine codewords at agreement $n/2 - 1$, and the Johnson radius is $\sqrt{\rho}\,n = n/2$. So at rate 1/4 the gap is closed: the proven threshold is within a relative $2^{-8}$ of $n/2$, and no list budget below $2^{26}$ allows $A \le n/2 - 1$. Deployed 109 queries, floor 108.

At other rates flats give $T = 2\rho n$ against Johnson $\sqrt\rho\, n$: equal only at $\rho = 1/4$. At rate 1/2 flats give nothing ($T = n$), and the best known is the coset-union family of the main doc ($T = 9n/16$, list 715 genuine or 11440 in degree $\le d$).

Current picture at level 0 (bits per query $= \log_2(n/T)$, $t = \lceil 108/\text{bits} \rceil$):

| rate | proven (Johnson) | deployed $t$ | best attack $T/n$ | $t$ floor |
| --- | --- | --- | --- | --- |
| 1/2 | $0.7071$ | 218 | $9/16$ | 131 |
| 1/4 | $1/2$ | 109 | $1/2$ (flats) | 108, closed |
| 1/8 | $0.3536$ | 73 | $1/4$ (flats) | 54 |
| 1/16 | $1/4$ | 55 | $1/8$ (flats) | 36 |

Later levels of the ladder have rates $2^{-(R+3i)}$, so low rates matter too: there Johnson gives $R/2$ bits per query and flats cap at $R - 1$.

## 2. The cost model: what a large list actually costs the attacker

Under Fiat-Shamir an attack is a path through the rounds, and its cost is the sum over rounds of $2^{g}/p$ hash evaluations ($g$ the round's grinding bits, $p$ its escape probability). Every path ends at a query round against a codeword that agrees with the committed word on some $T$ points, costing $2^{17}(n/T)^t$.

- A word at agreement $A - 1$ from a claim-satisfying codeword costs $2^{17}(n/(A-1))^t \approx 2^{125}$ and needs no other escape. That is the baseline, and it is why the query term is tight.
- A list of $L$ codewords at agreement $T$ lets the prover switch to a member that satisfies a false claim, by a fold-round or batching escape of probability about $L/|E|$ (each member has its own conic of about $|E|$ escaping $(\alpha,\beta)$). Cost about $2^{128+g}/L$, then the query round at $T$.
- So a list at agreement $T$ only hurts when $A \le T$. If $A > T$ the query round alone already costs the full $2^{125}$. Large lists strictly below the threshold are harmless.
- The list budget is not a constant. It is $L \lesssim 2^{3+g}$ for a message with $g$ grinding bits, so more grinding (cheap: $2^g$ hashes per message) raises it. The OOD term $\binom{L}{2}\kappa/|E|$ is quadratic in $L$ and would need a second OOD point instead.

Consequence: the right target is not "lists $\le 2^{10}$ beyond Johnson". It is a provable bound $\Lambda(T) \le 2^{b}$ for some $T$ below the Johnson threshold, with $b$ up to maybe 30 or 40, paid for with about $b - 10$ more grinding bits. Example: at rate 1/4, lists at $T \in [3n/8, n/2)$ are at least $2^{26}$ (flats); if they were provably at most $2^{30}$, the level could run at $A = 3n/8$ with $t = 77$ instead of 109.

## 3. The pole pair collapses the affine fold (pure MCA only)

With $f_0 = 1/(x - \beta_0)$, $(\alpha + \beta x) f_0 = \beta + (\alpha + \beta\beta_0) f_0$ and the constant $\beta$ is a codeword, so the affine pencil is the scalar pencil $\gamma = \alpha + \beta\beta_0$ and each bad $\gamma$ is a line of $|E|$ bad $(\alpha,\beta)$. This breaks claim-free affine MCA with families of about $2^{10}$ sets with a common locator top. With a nonzero claim weight each line keeps at most 2 escapes. `FoldRoundBound` in `formal/` allows the zero weight.

## 4. Structural facts worth knowing

- Evaluation at $x \in D \subseteq K$ commutes with the $K$-coordinates of $E$: a word over $E$ is two words over $K$, and a list over $E$ is a list of the 2-interleaved code over $K$.
- $x \mapsto x + a$ for $a \in D$ preserves $D$ and degrees. Scalar multiplication does not preserve $D$. $K$ has subfields $\mathrm{GF}(2^{2^i})$ but $D$ is not a subspace over any of them.
- Common-top rigidity: if locators of sets of size $T = 2^k q + r$ share all coefficients above degree $2^k q$, the lower factor is forced. This is why unions of cosets with a varying direction did not give anything at rate 1/2 by hand.

## 5. Rules for agents

- Write your report to `doc/whir_soundness_gap_notes/NN-<name>.md` (your number is in your brief) and scripts next to it under `doc/whir_soundness_gap_notes/scripts/`. Touch nothing else in the repository. No git commands that write (no commit, add, stash, branch).
- No installs or downloads of software on this machine. `python3` is available. Keep any single computation under about ten minutes and four cores.
- In the report, mark every statement as **proved** (with the proof), **checked numerically** (say on what sizes) or **conjectured**. A wrong claim costs more than a missing one. Give negative results too.
- No em dashes or en dashes, no hard-wrapped prose.
