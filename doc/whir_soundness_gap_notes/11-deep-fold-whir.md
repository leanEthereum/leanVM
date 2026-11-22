# 11. DEEP-fold WHIR: the protocol, its round-by-round theorem, parameters and costs

Researcher 11 (round 2). Scope: write out the protocol that uses the DEEP fold lemma of note 07 (its "variant P"), prove its round-by-round soundness from one hypothesis per level on list sizes, and price it. Notation is Annex B's (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`): levels $i = 0, \dots, I-1$, fold factors $\ell_i$, $\kappa_i = \nu_{i+1}$, domains $D_i$ of size $n_i = 2^{\kappa_i + R_i}$, queries $t_i$, lanes $P^{(i,j)}$, halves $F^{(i,j)}, G^{(i,j)}$, running claim $(W^{(i,j)}, \sigma^{(i,j)})$, high part $\mathbf{h}^{(i)}$, novel basis $\mathcal{X}_c$, normalized subspace polynomials $\widehat W_k$, $q = |E| = 2^{128}$. Statuses: **[proved]** (proof in this note), **[checked]** (numerically, sizes given), **[sketch]**, **[conjectured]**, **[estimate]**. Nothing is machine-checked. No Lean or Rust was edited.

## 0. Summary

**The protocol in ten lines (Protocol D, section 1).**

1. Commit as today (Merkle root of the interleaved codeword of $2^{\ell_i}$ lanes).
2. After every commitment $i$ the verifier sends $s_i$ points $z_m = (\theta_m, \zeta_m) \in E^2$ (after a grind), instead of one multilinear point. The prover answers one scalar per point, $y_m = \mathrm{ev}_{z_m}(P^{(i,0)}) := \sum_u \theta_m^{e(u)} P^{(i,0)}_u(\zeta_m)$, $e(u) = \sum_k (1 - u_k) 2^{k-1}$: whole lane polynomials (high parts included) evaluated at $\zeta_m$ and combined across lanes with powers of $\theta_m$.
3. The point claims are never batched inside their level. Level 0's are the commit-time points and replace the commit-time OOD claim; they are not among the weighted claims that $\lambda_0$ batches.
4. Fold round $j$: the prover sends today's four scalars and one scalar per point, $\varphi_m = \mathrm{ev}_{z_m}(F^{(i,j)})$, the value of the first half. Then $(\alpha, \beta)$ as today.
5. Both update the running claim as today and each carried value by $v_m \leftarrow v_m + (\theta_m^{2^{j-1}} + \alpha + \beta\zeta_m)\,\varphi_m$. No division, no extra check.
6. After the level's rounds each point claim reads $P^{(i,\ell_i)}(\zeta_m) = v_m$ on the one folded polynomial.
7. Next commitment and high part $\mathbf{h}^{(i)}$ as today, then the next level's points and answers (step 2), then the queries and $\lambda_{i+1}$ in one message as today.
8. The verifier converts each point claim to the low-part claim $\langle W_{\zeta_m}, f^{(i+1)}\rangle = v_m + \widehat W_{\kappa_i}(\zeta_m)\sum_s \mathbf{h}_s \mathcal{X}_s(\zeta_m)$, where $W_\zeta$ is the column weight of `lem:colweight` at a point of $E$, and $\lambda_{i+1}$ batches the residual claim, these $s_i$ claims and the $t_i$ query claims ($J_{i+1} = 1 + s_i + t_i$).
9. Last level: the final polynomial is sent in the clear; the verifier checks $P(\zeta_m) = v_m$ directly, then queries and tail sumcheck as today.
10. Terminal check as today, each point contributing $\lambda^m \prod_k ((1 + r_k) + r_k \widehat W_k(\zeta_m))$ to the weight: $O(\kappa)$ products a point, the code path of a query with $E$ in place of $K$.

**The theorem (Theorem D, section 2).** Hypothesis $\mathrm{ListBound}_i(L_i)$ for every level: every interleaved word on $D_i$ (any number of lanes) has at most $L_i$ tuples of degree at most $d^{(i)} = 2^{\kappa_i} - 1 + \ell_i$ within agreement $A^{(i,0)} = A_i - \ell_i$. No Johnson hypothesis, no mutual correlated agreement. With $\epsilon_i = (d^{(i)} + 2^{\ell_i})/q$, any real $K_0 \ge 2.72\,q$ and any $\tau \in (0,1)$, the round-by-round errors are:

| verifier message | error |
| --- | --- |
| points after commitment $i$ | $\bigl[\binom{L_i}{2} + \frac{4 L_i^3 q^6}{K_0^3}\sum_{j=0}^{\ell_i - 1}\tau^{-j}\bigr]\,\epsilon_i^{s_i}$ |
| batching $\lambda_0$ | $(J_0 - 1)/q$ |
| fold $(\alpha_{i,j}, \beta_{i,j})$ | $K_0/q^2 + \tau$ (no $\tau$ at $j = \ell_i$) |
| queries of level $i$ and $\lambda_{i+1}$ | $\bigl((A^{(i,\ell_i)} - 1)/n_i\bigr)^{t_i} + (s_i + t_i)/q$ (no second term at the last level) |
| tail round | $2/q$ |

Thresholds $A^{(i,j)} = A_i - (\ell_i - j)$ and the degree bound are today's: agreement loss one per round, no degree growth. With the deployed grinds (query 17, fold 7, point 15 in place of the OOD grind) and $K_0 = 2^9 q$, $\tau = 2^{-119}$, every message is within $2^{-125}$ once $s_i \log_2(1/\epsilon_i) \ge 3\log_2 L_i + 1064$ at level 0 ($\ell = 6$) and $3\log_2 L_i + 826$ later ($\ell = 4$): 11 to 14 points at level 0 for lists of $2^{10}$ to $2^{100}$, 8 to 11 later. The batching grind drops from 13 bits to 7.

**Headline costs** (WHIR opening, full stack, deployed grinds; `scripts/11_deep_fold_whir.py`, table T0; **[checked]** arithmetic on top of note 08's validated model). "No new theorem" uses the Johnson bound at every level and the counting bound at the last one or two levels, so it is unconditional given Theorem D.

| configuration | level-0 queries | $\mu = 24$ | $\mu = 28$ | $\mu = 30$ | guest Keccak, $\mu = 30$ |
| --- | --- | --- | --- | --- | --- |
| rate 1/2, today | 218 | 260.4 KiB | 313.7 KiB | 335.9 KiB | 8173 |
| DEEP fold, no new theorem | 217 | 252.1 (-3.2%) | 306.4 (-2.3%) | 332.0 (-1.2%) | 8005 (-2.1%) |
| ListBound(1/2, 0.66, $2^{40}$) at level 0 | 181 | 223.9 (-14.0%) | 273.8 (-12.7%) | 297.0 (-11.6%) | 7213 (-11.7%) |
| ListBound(1/2, 0.64, $2^{40}$) at level 0 | 168 | 213.6 (-18.0%) | 261.8 (-16.5%) | 284.3 (-15.4%) | 6923 (-15.3%) |
| the same exponent at every level ($\rho_i^{0.644} n_i$, $2^{40}$) | 168 | 206.0 (-20.9%) | 247.7 (-21.0%) | 265.2 (-21.1%) | 6400 (-21.7%) |
| ListBound(1/2, 5/8, $2^{40}$) at level 0 | 160 | 207.3 (-20.4%) | 254.5 (-18.9%) | 276.4 (-17.7%) | 6745 (-17.5%) |
| ListBound(1/2, 9/16, $2^{100}$) at level 0 | 131 | 184.3 (-29.2%) | 227.7 (-27.4%) | 248.0 (-26.2%) | 6103 (-25.3%) |
| the same exponent at every level ($\rho_i^{0.830} n_i$, $2^{100}$) | 131 | 166.2 (-36.2%) | 199.8 (-36.3%) | 213.8 (-36.4%) | 5166 (-36.8%) |
| rate 1/4, today | 109 | 169.9 KiB | 207.7 KiB | 222.6 KiB | 6000 |
| DEEP fold, no new theorem | 109 | 163.6 (-3.7%) | 201.7 (-2.9%) | 220.0 (-1.2%) | 5872 (-2.1%) |
| ListBound(1/4, 3/8, $2^{40}$) at level 0 | 77 | 136.5 (-19.7%) | 170.6 (-17.9%) | 186.9 (-16.0%) | 4977 (-17.1%) |
| ListBound(1/4, 5/16, $2^{70}$) at level 0 | 65 | 126.2 (-25.7%) | 158.8 (-23.6%) | 174.4 (-21.7%) | 4640 (-22.7%) |

The price of the change itself, at $\mu = 30$, rate 1/2 (59 points: 12 8 8 8 8 15): 313 more stream scalars (5.0 KiB; 211 to 524), 73 more Fiat-Shamir permutations (282 to 355), about 4500 more field multiplications for the native verifier out of 85,000 at equal queries (**[checked]** formula count, not measured), about 13,000 guest cycles for the points against about 480 per level-0 query saved (**[estimate]**), and at commit time $2 s_0 2^\mu$ carry-less multiplications fused into the pass that computes today's OOD value, which at $s_0 = 12$, $\kappa_0 = 24$, rate 1/2 equals the multiplication count of the level-0 NTT (**[proved]** count, time **not measured**; note 07's "low single-digit percentage" is not established).

**What is not fully proved** (details in section 2.8):

1. The whole theorem rests on Lemma D4, which is note 07's Theorem 3 re-derived here with several lanes, monomial lane weights and a relativising predicate. I found no error in it, but it is a hand proof, toy-checked by note 07 for one lane only, and researcher 10 is attacking it in parallel.
2. Knowledge soundness: the relativised fold lemma is proved (D4 carries the predicate), the extractor is unchanged and never list-decodes, but the full relativised induction through the levels is only sketched (section 2.7).
3. The hypothesis itself: $\mathrm{ListBound}$ beyond Johnson is **[conjectured]**. It must hold for interleaved words, equivalently for single-lane words over every finite extension of $K$ (Remark D0), which researchers 12 and 13 should check their statements cover.
4. The Fiat-Shamir compilation, the outer protocol's use of the pinned candidate and the level-0 $K$-valuedness are assumed to carry over as today; I did not re-derive them.
5. The cost model's verifier field counts are formula counts from `whir.rs`, the guest cycles and the prover time are estimates. The byte and Keccak numbers reuse note 08's validated formulas with a stream I specified, not one that exists in Rust.

**Flags on note 07** (section 6): the lemma survives my re-derivation; several points of its protocol sketch are corrected or sharpened (lane weights without division, the potential that makes the fold term exactly $K_0/q^2 + \tau$, the batching count, the prover cost, extension-field lists, the last-level numbers).

## 1. Protocol D

### 1.1 Point evaluations

**Definition D1.** A *point* is $z = (\theta, \zeta) \in E^2$. Fix a level with $\ell$ fold rounds. After $j$ rounds ($0 \le j \le \ell$) the lanes are indexed by the remaining lane variables $u = (u_{j+1}, \dots, u_\ell) \in \{0,1\}^{\ell - j}$, with $u_{j+1}$ the variable the next round folds. For a polynomial tuple $U = (U_u)_u$ of that shape,
$$\mathrm{ev}^{(j)}_z(U) := \sum_{u} \theta^{e_j(u)}\, U_u(\zeta), \qquad e_j(u) := \sum_{k=j+1}^{\ell} (1 - u_k)\,2^{k-1} .$$
For $j = \ell$ this is $P(\zeta)$. The whole polynomial is evaluated, coefficients of index $2^\kappa$ and above included: a point claim is not a weighted claim in the sense of `def:tuple-claim`.

**Lemma D1 (four facts). [proved]** (E1) $\mathrm{ev}^{(j)}_z$ is $E$-linear. (E2) If $F = U_{(0,\cdot)}$ and $G = U_{(1,\cdot)}$ are the halves of a tuple $U$ with lane variables $u_j, \dots, u_\ell$, then $\mathrm{ev}^{(j-1)}_z(U) = \theta^{2^{j-1}}\,\mathrm{ev}^{(j)}_z(F) + \mathrm{ev}^{(j)}_z(G)$. (E3) For $a \in E[X]$, $\mathrm{ev}^{(j)}_z(aU) = a(\zeta)\,\mathrm{ev}^{(j)}_z(U)$; in particular $\mathrm{ev}^{(j)}_z(G + (\alpha + \beta X)F) = \mathrm{ev}^{(j)}_z(G) + (\alpha + \beta\zeta)\,\mathrm{ev}^{(j)}_z(F)$. (E4) If $U \ne 0$ has degree at most $\Delta$, then $\Pr_{z \leftarrow E^2}[\mathrm{ev}^{(j)}_z(U) = 0] \le (\Delta + 2^\ell - 2^j)/q$.

*Proof.* (E1) and (E3) are immediate. (E2): $e_{j-1}(0, u') = 2^{j-1} + e_j(u')$ and $e_{j-1}(1, u') = e_j(u')$. (E4): $\sum_u \theta^{e_j(u)} U_u(\zeta)$ is a polynomial in $(\theta, \zeta)$; the exponents $e_j(u)$ are distinct for distinct $u$ (binary digits), so it is nonzero as soon as one $U_u$ is; its total degree is at most $\max_u e_j(u) + \Delta = 2^\ell - 2^j + \Delta$; Schwartz-Zippel (`lem:sz`). $\square$

Why this shape. Evaluation at $\zeta$ commutes exactly with the affine fold (E3), high parts included, so one answer per half is all a round needs and the value of $XF$ is not a free scalar. The lane weights are monomials in one scalar $\theta$ rather than note 07's $\mathrm{eq}(r, \cdot)$ with $r \in E^{\ell}$: the split (E2) then gives the second half's value by one multiplication instead of a division by $r_j$ (which needed an exceptional event $r_j = 0$), and a point is two sampled scalars instead of $\ell + 1$. The price is $2^\ell$ instead of $\ell$ in $\epsilon$, which is immaterial next to $d$ (63 against $2^{24}$ at level 0; half a bit per point at a last level with $\kappa = 4$).

### 1.2 The protocol

**Protocol D (WHIR with affine folds and carried out-of-domain points).** Parameters as in Protocol `fig:protocol`, plus a number of points $s_i \ge 1$ per level.

**Commit**$(f : \{0,1\}^\nu \to K)$. $\mathbf{P}$ sends the oracle $O^{(0)}$ as today. $\mathbf{V}$ sends $z^{(0)}_m = (\theta^{(0)}_m, \zeta^{(0)}_m) \leftarrow E^2$ for $m = 1, \dots, s_0$. $\mathbf{P}$ sends $y^{(0)}_m \in E$, honestly $\mathrm{ev}^{(0)}_{z^{(0)}_m}(P^{(0,0)})$. The *point claims* $(z^{(0)}_m, y^{(0)}_m)$ join what the opening proves. There is no multilinear OOD claim any more.

**Open**$(\{(W_k, c_k)\}_{k = 1..J_0})$. $\mathbf{V}$ sends $\lambda_0 \leftarrow E$. The running claim is $(W^{(0,0)}, \sigma^{(0,0)}) := (\sum_k \lambda_0^{k-1} W_k, \sum_k \lambda_0^{k-1} c_k)$ and the carried values are $v^{(0,0)}_m := y^{(0)}_m$. For $i = 0, \dots, I-1$:

1. *(fold rounds)* For $j = 1, \dots, \ell_i$:
   - (a) $\mathbf{P}$ sends $v_G, v_F, \sigma_0, \sigma_1 \in E$ as in Protocol `fig:protocol`, and $\varphi^{(i,j)}_m \in E$ for $m = 1, \dots, s_i$, honestly $\varphi^{(i,j)}_m = \mathrm{ev}^{(j)}_{z^{(i)}_m}(F^{(i,j)})$.
   - (b) $\mathbf{V}$ sends $\alpha_{i,j}, \beta_{i,j} \leftarrow E$.
   - (c) Both set $W^{(i,j)}$ and $\sigma^{(i,j)}$ as in Protocol `fig:protocol`, and for every $m$
   $$v^{(i,j)}_m := v^{(i,j-1)}_m + \bigl((\theta^{(i)}_m)^{2^{j-1}} + \alpha_{i,j} + \beta_{i,j}\,\zeta^{(i)}_m\bigr)\,\varphi^{(i,j)}_m .$$
   $\mathbf{P}$ sets $P^{(i,j)} := G^{(i,j)} + (\alpha_{i,j} + \beta_{i,j}X)F^{(i,j)}$.

   After the $\ell_i$ rounds, honestly $P^{(i,\ell_i)}(\zeta^{(i)}_m) = v^{(i,\ell_i)}_m$ for every $m$, besides the two identities of Protocol `fig:protocol`.
2. If $i < I - 1$:
   - (a) *(commit)* $\mathbf{P}$ sends the oracle $O^{(i+1)}$, then $\mathbf{h}^{(i)}$, as today.
   - (b) *(points)* $\mathbf{V}$ sends $z^{(i+1)}_m \leftarrow E^2$, $m = 1, \dots, s_{i+1}$; $\mathbf{P}$ sends $y^{(i+1)}_m \in E$, honestly $\mathrm{ev}^{(0)}_{z^{(i+1)}_m}(P^{(i+1,0)})$.
   - (c) *(query)* $\mathbf{V}$ sends $t_i$ i.i.d. query points $x_{i,q} \leftarrow D_i$ and $\lambda_{i+1} \leftarrow E$, one message.
   - (d) *(read)* $\mathbf{V}$ computes $c_{i,q}$ from the opened columns as today, and converts the level's point claims: with $H^{(i)} := \sum_{s < \ell_i} \mathbf{h}^{(i)}_s \mathcal{X}_s$,
   $$c'_{i,m} := v^{(i,\ell_i)}_m + \widehat W_{\kappa_i}(\zeta^{(i)}_m)\,H^{(i)}(\zeta^{(i)}_m) \qquad (\text{honestly } \mathcal{P}_{f^{(i+1)}}(\zeta^{(i)}_m)).$$
   - (e) *(next level)* The $J_{i+1} := 1 + s_i + t_i$ claims (residual, converted points, queries) are batched:
   $$W^{(i+1,0)} := W^{(i,\ell_i)} + \sum_{m=1}^{s_i} \lambda_{i+1}^{m}\, W_{i,\zeta^{(i)}_m} + \lambda_{i+1}^{s_i + 1}\sum_q \lambda_{i+1}^{q}\, W_{i,x_{i,q}}, \qquad \sigma^{(i+1,0)} := \sigma^{(i,\ell_i)} + \sum_{m=1}^{s_i} \lambda_{i+1}^{m}\, c'_{i,m} + \lambda_{i+1}^{s_i+1}\sum_q \lambda_{i+1}^{q}\, c_{i,q},$$
   where $W_{i,x}(u) := \prod_k \widehat W_k(x)^{u_k}$ on $\{0,1\}^{\kappa_i}$ for any $x \in E$ (the column weight of `lem:colweight`, at a point that need not be in the domain). The carried values of the new level are $v^{(i+1,0)}_m := y^{(i+1)}_m$.
3. If $i = I - 1$: *(final)* $\mathbf{P}$ sends the coefficients of $P^{(i,\ell_i)}$. $\mathbf{V}$ checks $P^{(i,\ell_i)}(\zeta^{(i)}_m) = v^{(i,\ell_i)}_m$ for every $m$, then sends the queries, checks them, and runs the tail sumcheck and the terminal check, all as today.

$\mathbf{V}$ accepts iff every check passed.

What is sampled when: per commitment, $2 s_i$ scalars (the points), once; per fold round, $(\alpha, \beta)$ as today and nothing else; per level, the queries and one $\lambda$ as today. What the prover adds: $s_i$ answers per commitment and $s_i$ scalars per round, that is $s_i(1 + \ell_i)$ scalars a level (112 bytes a point at level 0, 80 later), against one OOD value today.

### 1.3 Completeness, bases, and the verifier's work

**Completeness. [proved]**, and **[checked]** on a toy instance (`scripts/11_protocol_toy.py`: $\mathrm{GF}(2^{16})$, two levels with $\ell = 3, 2$ and $\kappa = 4, 2$, then a two-variable tail; 20 honest runs, 1900 identities, all checks pass; eight kinds of altered prover values are rejected in 20 of 20 runs each). By (E2), $v^{(i,j-1)}_m = \theta^{2^{j-1}}\varphi + \mathrm{ev}^{(j)}(G)$ when $v^{(i,j-1)}_m = \mathrm{ev}^{(j-1)}(P^{(i,j-1)})$ and $\varphi = \mathrm{ev}^{(j)}(F)$; by (E3) the folded tuple has $\mathrm{ev}^{(j)}(P^{(i,j)}) = \mathrm{ev}^{(j)}(G) + (\alpha + \beta\zeta)\varphi$, which is the update of step 1(c) in characteristic two. At the level's end $P^{(i,\ell_i)} = \mathcal{P}_{f^{(i+1)}} + \widehat W_{\kappa_i} H^{(i)}$ is an identity of polynomials, so it holds at $\zeta$, and $\mathcal{P}_g(\zeta) = \sum_u g(u)\prod_k \widehat W_k(\zeta)^{u_k} = \langle W_{i,\zeta}, g\rangle$ is Definition `def:enc` expanded, valid at every $\zeta \in E$.

**Bases.** The answers are evaluations, so they have no basis. The novel basis enters in three places. (1) The prover gets $P_u(\zeta)$ from the novel-basis coefficients $f(u, \cdot)$ as the inner product with the tensor $(\mathcal{X}_c(\zeta))_c = \bigotimes_k (1, \widehat W_k(\zeta))$. (2) The conversion of step 2(d) uses $\widehat W_{\kappa}(\zeta)$ and $\mathcal{X}_s(\zeta)$, $s < \ell$, the code of today's high-part correction at a query. (3) At the last level the verifier evaluates the final polynomial at $\zeta$ from its novel-basis coefficients, as it does at a query.

**The verifier's weights are MLE-friendly. [proved]** `lem:colweight`'s product formula $\widehat{W_x}(r) = \prod_{k < \kappa} ((1 + r_k) + r_k \widehat W_k(x))$ only uses that $W_x$ is a tensor, so it holds for $x = \zeta \in E$. The values $\widehat W_k(\zeta)$ follow the chain of `lem:chain` with arithmetic in $E$: one squaring in $E$ and two multiplications by constants of $K$ a step. So a point claim is a `GluedClaim` of `crates/verifier/src/whir.rs` with scalar $\lambda^m$ and the weight `induced_weight` of one query at $\zeta$: $O(\kappa_i)$ field operations at the terminal point, and $O(\kappa_i + \ell_i)$ for the conversion. Counts in section 3.4.

**What the native verifier changes.** `read_ood` becomes "grind, sample $2s$ scalars, read $s$ answers"; `verify_whir`'s round loop reads $4 + s$ scalars and updates $s$ carried values; the level tail computes $s$ converted values and pushes $s$ glued claims in place of the one OOD claim; the final level adds $s$ evaluations of `novel_eval(&folded, ..)` at points of $E$. The outer protocol stops adding the commitment's OOD claim to the stacked claims and hands the level-0 points to `verify_whir`.

**What the recursive verifier additionally computes** (`guests/lean_ethereum.py`, `open_stacked` and `check_opening_terminal`). Per level: $2 s_i$ squeezes for the points in place of today's $\nu_{i+1}$ for the OOD point (58 points at $\mu = 30$ with no new theorem are 116 squeezes, against today's $30 + 24 + 20 + 16 + 12 + 8 = 110$ coordinates), and $s_i$ answers read. Per fold round and point: one more scalar absorbed, one squaring of $\theta$, two products and three additions. Per point at the level's end: the chain $\widehat W_k(\zeta)$, $k \le \kappa_i$, by $\widehat W_{k+1} = \mathsf{c}_k^{-1}\widehat W_k(\widehat W_k + 1)$ (two products a step; a query's chain is table lookups on its index bits, a point's is arithmetic), `novel_eval` of the high part, two products for the batch. Per point at the terminal check: the product chain of `residual_query` with $\widehat W_k(\zeta)$ in place of $\widehat W_k(x)$. At the last level: $s$ runs of `novel_eval` on the final polynomial. Removed: the per-level `eq_prefix_chain` of the OOD claims. A point is "a query without its Merkle path, its row fold and its window decoding". Hints: none are needed (the update has no division); every value read from the stream is bound by the transcript and pinned by the final point check or the terminal check.

### 1.4 Design choices that were considered

- **Points fixed per commitment, not fresh per round.** A point claim on a folded tuple can only be discharged where the folded polynomial is next committed (with its high part) or sent, so a claim introduced mid-level rides to the level's end anyway. Fresh points after round $j$ cost $1 + (\ell - j)$ scalars each and one more verifier message (with its grind) per batch, and save only the nested factor of Lemma D6, while the first batch still needs enough points for $q^3\epsilon^s$ to be small. Example at level 0 with lists $2^{40}$: one batch at commit time, 12 points, 84 scalars; a batch of 6 for round 1 ($6 \times 7$ scalars) and a fresh batch of 11 after it ($11 \times 6$), 108 scalars, and the fresh batch's lane values are $E \times E$ products on the folded tuple, so the prover gains nothing either. **[checked]** arithmetic (`points_needed` with $\ell = 1$ and $\ell = 5$). Fresh batches remain a sound extension (adding claims only shrinks the set the invariant quantifies over), should the nested factor ever matter.
- **Answers for the two halves, not for the lanes.** Sending all $2^\ell$ lane values at each point at commit time is the same soundness for $64 s_0$ scalars instead of $7 s_0$.
- **Univariate in the coefficient variable.** A multilinear point weighs only the low part, so the answer for $XF$ would be a third free value per point and Lemma D2 would fail (note 07, section 3.7).

## 2. Round-by-round soundness

### 2.1 Hypothesis and thresholds

Thresholds and degree bound are Annex B's: each level has one free integer $A_i \le n_i$, and
$$d^{(i)} := 2^{\kappa_i} - 1 + \ell_i, \qquad A^{(i,j)} := A_i - (\ell_i - j), \qquad 0 \le j \le \ell_i .$$
We require $A^{(i,0)} \ge d^{(i)} + 2$ (Lemma D4 needs $d + 2 \le A$ at every round; any threshold of interest is far above it). For an interleaved word $O$ with $m$ lane variables, $\mathrm{List}(O; A, d)$ is the set of polynomial tuples of degree at most $d$ agreeing with $O$ on at least $A$ columns (`def:interleaved`).

**Hypothesis $\mathrm{ListBound}_i(L_i)$.** For every $0 \le m \le \ell_i$ and every interleaved word $O : \{0,1\}^m \times D_i \to E$: $|\mathrm{List}(O; A^{(i,0)}, d^{(i)})| \le L_i$.

**Remark D0 (which words). [proved]** $\mathrm{ListBound}$ for $h$ lanes over $E$ is the same statement as a list bound for single-lane words over the extension of $E$ of degree $h$: choose a basis $b_1, \dots, b_h$ of the extension over $E$ and send a tuple $(U_u)$ to $\sum_u b_u U_u$; distinct tuples go to distinct polynomials of the same degree with at least the same agreement, and conversely the coordinates of a polynomial over the extension form a tuple. The same holds from $K$ to $E$ (note 00, section 4). So the hypothesis is: *for every finite extension $F$ of $K$ of degree up to $2^{\ell_i + 1}$ (128 at level 0), every word $D_i \to F$ has at most $L_i$ polynomials over $F$ of degree at most $d^{(i)}$ within agreement $A^{(i,0)}$.* A bound proved only for $K$-valued or $E$-valued single-lane words is not enough. The Johnson bound and the counting bound hold over every alphabet, so they qualify:

- **Johnson. [proved]** (`thm:johnson-interleaved`) If $(A^{(i,0)})^2 > n_i d^{(i)}$, $\mathrm{ListBound}_i$ holds with $L_i = \mathrm{jl}(A^{(i,0)}, d^{(i)})$.
- **Counting. [proved]** For every $A \ge d + 1$, $|\mathrm{List}(O; A, d)| \le \binom{n}{d+1}/\binom{A}{d+1}$: each member agrees with $O$ on at least $\binom{A}{d+1}$ sets of $d + 1$ columns, and two members that agree with $O$ on the same $d + 1$ columns are equal.

### 2.2 The theorem

Let $\epsilon_i := (d^{(i)} + 2^{\ell_i})/q$.

**Theorem D (RBR soundness of Protocol D).** Suppose $\mathrm{ListBound}_i(L_i)$ for every level $i$. Let $K_0 \ge 2.72\,q$ be real, let $\binom{n_i}{2} \le 2q$ for every $i$, and let $0 < \tau < 1$. Call the input claims (the weighted claims $\{(W_k, c_k)\}_k$ together with the level-0 point claims $\{(z^{(0)}_m, y^{(0)}_m)\}_m$) *false* if no $U \in \mathrm{List}(O^{(0)}; A^{(0,0)}, d^{(0)})$ has $\mathrm{ev}^{(0)}_{z^{(0)}_m}(U) = y^{(0)}_m$ for all $m$ and $\langle W_k, g_U\rangle = c_k$ for all $k$. Then Protocol D has the following round-by-round soundness error at each verifier message:

$$\begin{array}{llcl}
\text{points } z^{(i)} \text{ after commitment } i: & \varepsilon^{\mathrm{pt}}_i &=& \Bigl[\dbinom{L_i}{2} + \dfrac{4 L_i^3 q^6}{K_0^3}\displaystyle\sum_{j=0}^{\ell_i - 1}\tau^{-j}\Bigr]\,\epsilon_i^{\,s_i}, \\[2ex]
\text{batching } \lambda_0: & \varepsilon^{\mathrm{batch}} &=& \dfrac{J_0 - 1}{q}, \\[2ex]
\text{fold } (\alpha_{i,j}, \beta_{i,j}): & \varepsilon^{\mathrm{fold}}_{i,j} &=& \dfrac{K_0}{q^2} + \tau \quad (j < \ell_i), \qquad \dfrac{K_0}{q^2} \quad (j = \ell_i), \\[2ex]
\text{query message of level } i: & \varepsilon^{\mathrm{query}}_i &=& \Bigl(\dfrac{A^{(i,\ell_i)} - 1}{n_i}\Bigr)^{t_i} + \dfrac{s_i + t_i}{q}, \\[2ex]
\text{each of the } \nu_I \text{ tail rounds}: & \varepsilon^{\mathrm{tail}} &=& \dfrac{2}{q},
\end{array}$$

the second query term being absent at the last level. The points of level 0 are sent at commit time: their error is charged there, and the opening starts from a state in which they are good (section 2.5). **[proved]** from Lemmas D1 to D6 below, to the standard of the proof of `thm:rbr`; see section 2.8 for what "proved" does not cover.

Compared with `thm:rbr`: the Johnson hypothesis $(A^{(i,0)})^2 > n_i d^{(i)}$ and $\varepsilon_{\mathrm{aff}}$ are gone; no list size multiplies a term of order $1/q$; lists enter only cubed against $\epsilon_i^{s_i}$, and squared in the pinning term.

### 2.3 The DEEP fold round

Fix a level ($\ell$, $d$, $D$ of size $n$), a round $j \in \{1, \dots, \ell\}$ and an interleaved word $O$ with lane variables $u_j, \dots, u_\ell$, halves $O_0, O_1$ of $h = 2^{\ell - j}$ lanes each. For a challenge $c = (\alpha, \beta)$ write $a_c(X) := \alpha + \beta X$ and $O_c := O_1 + a_c\,O_0$ (the affine fold). Let $A$ be an integer with $d + 2 \le A \le n$ and $\Lambda$ a bound on $|\mathrm{List}(O_c; A, d)|$ valid for every $c$. Let $\mathcal{T} := \{(c, P) : c \in E^2,\ P \in \mathrm{List}(O_c; A, d)\}$, so $|\mathcal{T}| \le \Lambda q^2$; it depends on $O$ only.

For three elements $(c_1, P_1), (c_2, P_2), (c_3, P_3)$ of $\mathcal{T}$ with pairwise distinct challenges put $L_1 := a_{c_2} + a_{c_3}$, $L_2 := a_{c_1} + a_{c_3}$, $L_3 := a_{c_1} + a_{c_2}$ and
$$Q := L_1 P_1 + L_2 P_2 + L_3 P_3 ,$$
a tuple of degree at most $d + 1$, symmetric in the three elements. The triple is *dependent* if $Q = 0$.

**Lemma D2 (dependency; note 07, Lemma 1). [proved]** (a) If for one point $z$ and one pair of values $(y^F, y^G)$ the three elements satisfy $\mathrm{ev}^{(j)}_z(P_k) = y^G + a_{c_k}(\zeta)\,y^F$, then $\mathrm{ev}^{(j)}_z(Q) = 0$. (b) If the triple is dependent, the rational tuples $F := (P_1 + P_2)/L_3$ and $G := P_1 + a_{c_1}F$ satisfy $P_k = G + a_{c_k}F$ for $k = 1, 2, 3$.

*Proof.* In characteristic two $L_1 + L_2 + L_3 = 0$ and $L_1 a_{c_1} + L_2 a_{c_2} + L_3 a_{c_3} = 2(a_{c_1}a_{c_2} + a_{c_1}a_{c_3} + a_{c_2}a_{c_3}) = 0$. (a) By (E1) and (E3), $\mathrm{ev}_z(Q) = \sum_k L_k(\zeta)\,(y^G + a_{c_k}(\zeta)y^F) = 0$. (b) $L_3 \ne 0$ as $c_1 \ne c_2$. $P_2 = P_1 + L_3 F = G + (a_{c_1} + L_3)F = G + a_{c_2}F$. And $L_3 P_3 = L_1 P_1 + L_2 P_2 = (L_1 + L_2)G + (L_1 a_{c_1} + L_2 a_{c_2})F = L_3(G + a_{c_3}F)$. $\square$

**Lemma D3 (a class is a line or a near pair; note 07, Lemma 2, with the near-pair clause). [proved]** Let $\mathcal{W}' \subseteq \mathcal{T}$ have pairwise distinct challenges and contain two elements with which every other element forms a dependent triple, and let $(F, G)$ be the rational pair of Lemma D2(b), so $P_c = G + a_c F$ for every $(c, P_c) \in \mathcal{W}'$.
(i) If $|\mathcal{W}'| > q$, then $F$ and $G$ are polynomial tuples with $\deg F \le d - 1$ and $\deg G \le d$.
(ii) If moreover $|\mathcal{W}'| > \binom{n}{2}$, let $Z := \{x \in D : F(x) = O_0(x),\ G(x) = O_1(x)\}$. Then all but at most $\binom{n}{2}$ elements $(c, P_c)$ of $\mathcal{W}'$ have at most one agreement column of $P_c$ with $O_c$ outside $Z$. In particular $|Z| \ge A - 1$, the tuple $U := (F, G)$ is in $\mathrm{List}(O; A - 1, d)$, and for those elements $U$ agrees with $O$ on all but at most one column of the agreement set of $P_c$ with $O_c$ ($U$ is a *near tuple* of $P_c$).

*Proof.* (i) For two elements, $P_c + P_{c'} = (a_c + a_{c'})F$ is a polynomial tuple of degree at most $d$ and $a_c + a_{c'} \ne 0$ has degree at most one. If a component of $F$ is not a polynomial, its denominator in lowest terms divides every $a_c + a_{c'}$, hence is $X + x_0$ for one $x_0 \in E$, and $(\alpha + \alpha') = (\beta + \beta')x_0$ for all pairs: the challenges of $\mathcal{W}'$ lie on the line $\alpha + x_0\beta = \text{const}$ and $|\mathcal{W}'| \le q$. If $F$ is a polynomial tuple and all challenges share $\beta$, again $|\mathcal{W}'| \le q$. Otherwise some $a_c + a_{c'}$ has degree exactly one, so $\deg F \le d - 1$ and $\deg G = \deg(P_c + a_c F) \le d$. (ii) Let $(c, P_c) \in \mathcal{W}'$ and $x \notin Z$ with $P_c(x) = O_c(x)$. Then $(G + O_1)(x) = a_c(x)\,(F + O_0)(x)$ in $E^h$. If $(F + O_0)(x) = 0$ then $(G + O_1)(x) = 0$ and $x \in Z$; so $(F + O_0)(x) \ne 0$ and the scalar $\alpha + \beta x$ is determined. Two such columns $x \ne x'$ determine $c$. So at most $\binom{n}{2}$ challenges have two agreement columns outside $Z$. As $|\mathcal{W}'| > \binom{n}{2}$, some element has at most one, and its agreement set has at least $A$ columns, so $|Z| \ge A - 1$. $\square$

**Lemma D4 (DEEP fold round with its claims; note 07, Theorem 3 and Corollary 4). [proved]** In the setting above let $K_0 \ge 30$ be real with $0.74\,K_0 \ge \max(2q, \binom{n}{2})$. For a vector of points $\mathbf{z} = (z_1, \dots, z_s) \in (E^2)^s$ let $N(\mathbf{z})$ be the number of ordered triples of $\mathcal{T}$ with pairwise distinct challenges that are not dependent and have $\mathrm{ev}^{(j)}_{z_m}(Q) = 0$ for all $m$, and let
$$\mathrm{Exc}_j(O) := \{\mathbf{z} : N(\mathbf{z}) \ge K_0^3/4\} .$$
(1) For independent uniform points, $\Pr[\mathbf{z} \in \mathrm{Exc}_j(O)] \le 4\Lambda^3 q^6\,\epsilon^s / K_0^3$ with $\epsilon := (d + 2^\ell)/q$.
(2) Let $\mathbf{z} \notin \mathrm{Exc}_j(O)$. Let $(W, \sigma)$ be a weighted claim on tuples with lane variables $u_j, \dots, u_\ell$, let $(v_m)_{m \le s}$ be values in $E$, and let $B$ be any predicate on such tuples (take $B$ true for plain soundness). Suppose every $U \in \mathrm{List}(O; A - 1, d)$ with $B(U)$ and $\mathrm{ev}^{(j-1)}_{z_m}(U) = v_m$ for all $m$ has $\langle W, U\rangle \ne \sigma$. Then for every prover message $(v_G, v_F, \sigma_0, \sigma_1, (\varphi_m)_m)$, fewer than $K_0$ challenges $c = (\alpha, \beta)$ admit a $P \in \mathrm{List}(O_c; A, d)$ such that
   - (p) $\mathrm{ev}^{(j)}_{z_m}(P) = v_m + (\theta_m^{2^{j-1}} + \alpha + \beta\zeta_m)\,\varphi_m$ for all $m$,
   - (w) $\langle \widehat W(\alpha, \cdot), P\rangle = v_G + \alpha(v_G + \sigma) + \alpha^2 v_F + \beta\sigma_0 + \alpha\beta(\sigma_0 + \sigma_1)$, and
   - (b) every near tuple of $P$ (a tuple of degree at most $d$ agreeing with $O$ on all but at most one column of the agreement set of $P$ with $O_c$) satisfies $B$.

*Proof.* (1) $\mathcal{T}$ is fixed by $O$. For a fixed non-dependent triple, $Q \ne 0$ has degree at most $d + 1$ and lane variables $u_{j+1}, \dots, u_\ell$, so by (E4) and independence all $s$ evaluations vanish with probability at most $((d + 1 + 2^\ell - 2^j)/q)^s \le \epsilon^s$. Hence $\mathbb{E}[N] \le |\mathcal{T}|^3\epsilon^s \le \Lambda^3 q^6 \epsilon^s$, and Markov gives the claim.
(2) Put $y^F_m := \varphi_m$ and $y^G_m := v_m + \theta_m^{2^{j-1}}\varphi_m$, so (p) reads $\mathrm{ev}^{(j)}_{z_m}(P) = y^G_m + a_c(\zeta_m)\,y^F_m$. Suppose at least $K_0$ challenges are as stated, and choose one $P_c$ for each: a set $\mathcal{W} \subseteq \mathcal{T}$ with distinct challenges, $K := |\mathcal{W}| \ge K_0$. By Lemma D2(a) every triple of $\mathcal{W}$ has $\mathrm{ev}^{(j)}_{z_m}(Q) = 0$ for all $m$, so the non-dependent ordered triples of $\mathcal{W}$ number at most $N(\mathbf{z}) < K_0^3/4 \le K^3/4$. Averaging over the $K(K-1)$ ordered pairs, some pair of elements has fewer than $K^2/(4(K-1))$ third elements that are not dependent with it. Let $\mathcal{W}'$ be that pair together with the elements dependent with it: $|\mathcal{W}'| > K - K^2/(4(K-1)) \ge 0.74\,K$ as $K \ge 30$. Now $|\mathcal{W}'| > \max(2q, \binom{n}{2})$, so Lemma D3 gives polynomial tuples $F, G$ with $U := (F, G) \in \mathrm{List}(O; A - 1, d)$ and $P_c = G + a_c F$ on $\mathcal{W}'$.
*$U$ satisfies the carried point claims.* Fix $m$. The elements of $\mathcal{W}'$ with one value of $a_c(\zeta_m) = \alpha + \beta\zeta_m$ lie on a line, at most $q$ of them, so two elements have different values, and by (E3) the two equations $\mathrm{ev}(G) + a_c(\zeta_m)\,\mathrm{ev}(F) = y^G_m + a_c(\zeta_m)\,y^F_m$ give $\mathrm{ev}^{(j)}_{z_m}(F) = y^F_m$ and $\mathrm{ev}^{(j)}_{z_m}(G) = y^G_m$. By (E2), $\mathrm{ev}^{(j-1)}_{z_m}(U) = \theta_m^{2^{j-1}} y^F_m + y^G_m = v_m$.
*$U$ satisfies $B$.* By Lemma D3(ii) some element of $\mathcal{W}'$ has $U$ as a near tuple of its $P_c$, and (b) holds for that element.
*Contradiction.* By hypothesis $\sigma^\ast := \langle W, U\rangle \ne \sigma$. As in the proof of `lem:fold-list`, for every $c$ the value $\langle \widehat W(\alpha, \cdot), G + a_c F\rangle$ is the right side of (w) with the pair's own four values and $\sigma^\ast$ in place of $\sigma$ (the low part of $XF$ depends only on the low part of $F$, `lem:mulx`). The difference of the two sides is a polynomial of degree at most two in $(\alpha, \beta)$ whose constant term and coefficient of $\alpha$ vanish together only if $\sigma^\ast = \sigma$; it is nonzero and has at most $2q$ zeros. But (w) holds on all of $\mathcal{W}'$, more than $2q$ challenges. $\square$

Remarks. The only input from the code is $\Lambda$. A family of pole pairs (which breaks pure affine MCA with error (number of members)$/q$, note 00 section 3) costs here what one costs, because the answers at the points are those of one rational pair (note 07, section 3.2). The agreement loss of one and the degrees $(d - 1, d)$ are those of `thm:mca-affine`, which is why thresholds and the degree bound do not move. The loss cannot be removed by this argument: forcing $|Z| \ge A$ needs $|\mathcal{W}'| > nq$, an error of order $n/q$.

### 2.4 Pinning and the points' potential

**Lemma D5 (pinning). [proved]** Let $O$ be an interleaved word with $\ell$ lane variables and $|\mathrm{List}(O; A, d)| \le L$. For independent uniform points, except with probability at most $\binom{L}{2}\bigl((d + 2^\ell - 1)/q\bigr)^s$, any two distinct members $U \ne U'$ of the list have $\mathrm{ev}^{(0)}_{z_m}(U) \ne \mathrm{ev}^{(0)}_{z_m}(U')$ for some $m$. Call such points *separating* for $O$: then for every answer vector at most one list member is consistent with all answers.

*Proof.* (E4) for $U + U' \ne 0$ of degree at most $d$, independence, and a union over pairs. $\square$

A level's points are sampled once but used in every round, and the word of round $j \ge 2$ depends on the challenges of the earlier rounds, which the prover can grind. The next lemma charges this to the point message and to the fold challenges.

**Lemma D6 (potential). [proved]** Fix a level with committed word $O$ and write $O^{(k)}$ for $O$ folded by challenges $c_1, \dots, c_k$. Let $\varepsilon_\ast \ge \sup_{O'} \Pr_{\mathbf{z}}[\mathbf{z} \in \mathrm{Exc}_j(O')]$ for every $j$. For $0 \le k < j \le \ell$ let
$$\pi^{(k)}_j(\mathbf{z}; c_1, \dots, c_k) := \Pr_{c_{k+1}, \dots, c_{j-1}}\bigl[\mathbf{z} \in \mathrm{Exc}_j(O^{(j-1)})\bigr], \qquad T_k := \sum_{j=k+1}^{\ell} \tau^{-(j-k-1)}\,\pi^{(k)}_j ,$$
so $\pi^{(j-1)}_j \in \{0, 1\}$ and $T_\ell = 0$. Then: (a) $\Pr_{\mathbf{z}}[T_0 \ge 1] \le \varepsilon_\ast\sum_{j=0}^{\ell-1}\tau^{-j}$. (b) If $T_{k-1} < 1$ then $\mathbf{z} \notin \mathrm{Exc}_k(O^{(k-1)})$ and $\Pr_{c_k}[T_k \ge 1] < \tau$.

*Proof.* The folds of $O$ are functions of $O$ and the challenges alone; no prover message enters. (a) By Fubini $\mathbb{E}_{\mathbf{z}}[\pi^{(0)}_j] = \mathbb{E}_{c}\Pr_{\mathbf{z}}[\mathbf{z} \in \mathrm{Exc}_j(O^{(j-1)})] \le \varepsilon_\ast$, so $\mathbb{E}[T_0] \le \varepsilon_\ast\sum_{j=1}^{\ell}\tau^{-(j-1)}$; Markov. (b) The term $j = k$ of $T_{k-1}$ is $\pi^{(k-1)}_k \in \{0,1\}$ with coefficient one, so it is zero. And $\mathbb{E}_{c_k}[\pi^{(k)}_j] = \pi^{(k-1)}_j$, so $\mathbb{E}_{c_k}[T_k] = \sum_{j > k}\tau^{-(j-k-1)}\pi^{(k-1)}_j = \tau\sum_{j>k}\tau^{-(j-k)}\pi^{(k-1)}_j \le \tau\,T_{k-1} < \tau$; Markov. $\square$

The factor $\tau^{-(\ell - 1)}$ is not an artifact of the bookkeeping. A prover that grinds $c_1$ at density $\tau$ to reach a word for which the points are exceptional at density $\tau$ over $c_2$, and so on, is what round-by-round soundness must exclude, and without knowledge of the structure of the exceptional sets Markov is tight for it. Choosing $\tau = q^{-2}$ is the union bound over all challenge prefixes (no $\tau$ in the fold term, 256 bits a round in the point term); $\tau = 2^{-119}$ costs 119 bits a round.

### 2.5 Proof of Theorem D

A tuple $U$ *satisfies* a weighted claim $(W, \sigma)$ if $\langle W, U\rangle = \sigma$ (this depends only on $g_U$) and a point claim $(z, v)$ at round $j$ if $\mathrm{ev}^{(j)}_z(U) = v$. Let $O^{(i,j)}$ be the level-$i$ oracle folded by its first $j$ challenges and $\mathrm{List}^{(i,j)} := \mathrm{List}(O^{(i,j)}; A^{(i,j)}, d^{(i)})$, of size at most $L_i$ by $\mathrm{ListBound}_i$ (the word $O^{(i,j)}$ has $\ell_i - j$ lane variables and $A^{(i,j)} \ge A^{(i,0)}$). Let $T^{(i)}_k$ be the potential of Lemma D6 for level $i$, with $\mathrm{Exc}_j$ taken at $A = A^{(i,j)}$, $d = d^{(i)}$, $\Lambda = L_i$ and the theorem's $K_0$ (the conditions of Lemma D4 hold: $0.74 \cdot 2.72 > 2$ and $\binom{n_i}{2} \le 2q$). Call the points $z^{(i)}$ *good* for $O^{(i)}$ if they are separating for $O^{(i)}$ at $(A^{(i,0)}, d^{(i)})$ and $T^{(i)}_0 < 1$.

*The invariant.* At each point of the protocol: some check of $\mathbf{V}$ has already failed, or the condition attached to the last verifier message holds.

- At the start of the opening: the points $z^{(0)}$ are good for $O^{(0)}$, and the input claims are false.
- After $\lambda_i$ ($j = 0$; for $i \ge 1$ this is the query message of level $i - 1$) and after the fold challenge of round $j$:
$$(\mathrm{I}_{i,j})\quad \text{no } U \in \mathrm{List}^{(i,j)} \text{ satisfies the running claim } (W^{(i,j)}, \sigma^{(i,j)}) \text{ and all point claims } (z^{(i)}_m, v^{(i,j)}_m); \qquad (\mathrm{G}_{i,j})\quad T^{(i)}_j < 1 .$$
- After the points $z^{(i+1)}$: $(\mathrm{I}_{i,\ell_i})$ holds and $z^{(i+1)}$ is good for $O^{(i+1)}$.
- After the final query message: $f^{(I)}$ does not satisfy the running claim.
- After each tail round: the running sumcheck claim is false.

Properties (i), (ii), (iv) of Definition `def:rbr` are as in the proof of `thm:rbr`: each condition involves only the messages up to the last verifier message (the carried values $v^{(i,j)}_m$ are functions of the prover's $\varphi$'s sent before the challenge; goodness of points is a property of the commitment and the points), and at the end $\mathbf{V}$ checks the last sumcheck claim itself. It remains to bound each verifier message.

*Points $z^{(i)}$ (at commit time for $i = 0$; step 2(b) for $i \ge 1$).* The word $O^{(i)}$ is fixed before the points. By Lemma D5 they are separating except with probability $\binom{L_i}{2}\epsilon_i^{s_i}$. By Lemma D4(1) with $\Lambda = L_i$, $\varepsilon_\ast = 4L_i^3q^6\epsilon_i^{s_i}/K_0^3$ bounds the exceptional probability of every round and every folded word, so by Lemma D6(a) $T^{(i)}_0 \ge 1$ with probability at most $\varepsilon_\ast\sum_{j < \ell_i}\tau^{-j}$. The condition $(\mathrm{I}_{i-1,\ell_{i-1}})$ does not involve the new points. Total: $\varepsilon^{\mathrm{pt}}_i$.

*Batching $\lambda_0$.* The points are separating, so at most one $U^\ast \in \mathrm{List}^{(0,0)}$ satisfies all point claims $(z^{(0)}_m, y^{(0)}_m)$. If there is none, $(\mathrm{I}_{0,0})$ holds for every $\lambda_0$. Otherwise, as the input claims are false, $U^\ast$ violates some weighted claim; $\sum_k \lambda_0^{k-1}(\langle W_k, U^\ast\rangle - c_k)$ is a nonzero polynomial of degree less than $J_0$ and vanishes with probability at most $(J_0 - 1)/q$. There is no union over the list: the other members stay excluded by the unbatched point claims. $(\mathrm{G}_{0,0})$ is part of the starting state.

*Fold challenge $(\alpha_{i,j}, \beta_{i,j})$.* Before it, $(\mathrm{I}_{i,j-1})$ and $(\mathrm{G}_{i,j-1})$ hold and the prover has sent its round message. By Lemma D6(b), $z^{(i)} \notin \mathrm{Exc}_j(O^{(i,j-1)})$. Apply Lemma D4(2) with $O = O^{(i,j-1)}$, $A = A^{(i,j)}$, $(W, \sigma) = (W^{(i,j-1)}, \sigma^{(i,j-1)})$, $v_m = v^{(i,j-1)}_m$, $B$ true: its hypothesis is $(\mathrm{I}_{i,j-1})$, since $A - 1 = A^{(i,j-1)}$, and conditions (p), (w) are exactly "$P$ satisfies the new point claims and the new running claim". So $(\mathrm{I}_{i,j})$ fails for fewer than $K_0$ of the $q^2$ challenges. By Lemma D6(b) again, $(\mathrm{G}_{i,j})$ fails with probability less than $\tau$ (and never for $j = \ell_i$).

*Query message of level $i < I - 1$.* Before it the prover has committed $O^{(i+1)}$, sent $\mathbf{h}^{(i)}$ and, after the points, the answers $y^{(i+1)}$. The points are separating, so at most one $U^\ast \in \mathrm{List}^{(i+1,0)}$ satisfies all new point claims; it is fixed before the queries. If there is none, $(\mathrm{I}_{i+1,0})$ holds. Otherwise let $g^\ast := g_{U^\ast}$ and $P^\ast := \mathcal{P}_{g^\ast} + \widehat W_{\kappa_i}H^{(i)}$, of degree at most $d^{(i)}$.
- If $P^\ast$ agrees with $w^{(i)} = O^{(i,\ell_i)}$ on at least $A^{(i,\ell_i)}$ columns, then by $(\mathrm{I}_{i,\ell_i})$ either $P^\ast$ violates the running claim, and then $g^\ast$ violates the residual claim (a claim weighs only the low part), or $P^\ast(\zeta^{(i)}_m) \ne v^{(i,\ell_i)}_m$ for some $m$, and then $\langle W_{i,\zeta_m}, g^\ast\rangle = \mathcal{P}_{g^\ast}(\zeta_m) = P^\ast(\zeta_m) + \widehat W_{\kappa_i}(\zeta_m)H^{(i)}(\zeta_m) \ne c'_{i,m}$: $g^\ast$ violates a converted point claim.
- Otherwise all $t_i$ queries land on agreement columns with probability at most $((A^{(i,\ell_i)} - 1)/n_i)^{t_i}$, and a query off the agreement set gives a consistency claim that $g^\ast$ violates, exactly as in the proof of `thm:rbr`.

So, except with that probability, $U^\ast$ violates one of the $J_{i+1} = 1 + s_i + t_i$ claims of step 2(e), and $\lambda_{i+1}$, uniform and independent of them, leaves the batch violated except with probability $(J_{i+1} - 1)/q = (s_i + t_i)/q$. Every other member of $\mathrm{List}^{(i+1,0)}$ violates a new point claim. This is $(\mathrm{I}_{i+1,0})$; $(\mathrm{G}_{i+1,0})$ is the goodness of $z^{(i+1)}$.

*Final query message.* At $i = I - 1$ the prover has sent $P := P^{(i,\ell_i)}$ of degree at most $d^{(i)}$ with low part $f^{(I)}$. If $P$ agrees with $w^{(i)}$ on at least $A^{(i,\ell_i)}$ columns, then by $(\mathrm{I}_{i,\ell_i})$ either $P(\zeta^{(i)}_m) \ne v^{(i,\ell_i)}_m$ for some $m$ and $\mathbf{V}$'s point check fails, or $P$, hence $f^{(I)}$, violates the running claim. Otherwise some query has $P(x) \ne w^{(i)}(x)$ except with probability $((A^{(i,\ell_i)} - 1)/n_i)^{t_i}$, and $\mathbf{V}$'s query check fails.

*Tail round.* Unchanged: $2/q$. $\square$

### 2.6 Degree slack, lanes, agreement loss, the level-0 claims

- **Degree slack.** Every list of level $i$ is taken at the one degree $d^{(i)} = 2^{\kappa_i} - 1 + \ell_i$, as today. Lemma D3(i) returns halves of degrees $(d - 1, d)$ from folds of degree $d$, so nothing grows going back through the rounds.
- **Interleaved lanes.** Lemmas D2 to D4 are stated for $h$-lane halves; the lane structure enters only through $\mathrm{ev}$, whose four facts are Lemma D1, and through $\Lambda$, which $\mathrm{ListBound}$ bounds for every lane count. No packing into an extension field is needed in the proof; it appears only in Remark D0.
- **Agreement loss.** One column per round, as today: $A^{(i,j)} = A_i - (\ell_i - j)$. The queries see $A^{(i,\ell_i)} - 1$.
- **The level-0 batching of the input claims.** $(J_0 - 1)/q$ instead of $(J_0 - 1)L_0/q$, with $J_0 \le 514$: 7 bits of grind by the rule $\lceil\log_2 N\rceil - 3$ instead of 13, and `MAX_LIST_0` has no role left in the PCS.
- **The outer protocol.** It faces one pinned candidate as today: the commit-time points pin a tuple $U^\ast$, hence its message, where today's OOD point pins a message. "False input claims" is the same interface as today's with "satisfies the OOD claim" replaced by "satisfies the point claims". I did not re-derive the outer protocol's use of it.
- **Level 0 is $K$-valued.** List members at level 0 are tuples over $E$ agreeing with $K$-valued lanes on more than $d$ columns, hence over $K$ (`Candidates.lean`, `exists_map_of_isInK`); unchanged. The folded words of level 0 are $E$-valued from round 1 on, which is why $\mathrm{ListBound}_0$ is needed for $E$-valued lanes.

### 2.7 Knowledge soundness

**[sketch]**, except where marked. The formalization's notion (`Sound/Spec.lean`, `Descent.lean`) is: from "every candidate that is bad violates one of the claims", an accepting run has a *good trace*, meaning the final polynomial descends, level by level and round by round through *near tuples* (one-error decoding on the agreement set), to a level-0 list member that is not bad. The extractor is that descent. It never list-decodes: each step is unique decoding with at most one error on a known agreement set. This matters more here than today, because beyond the Johnson radius no efficient list decoder is known; an extractor that had to produce the candidate from the commitment alone would be in trouble, the descent extractor is not.

What changes: (1) The invariant is relativised to a predicate $B$ on tuples, pulled back through each round by `pullT`. Lemma D4 is stated with exactly that predicate, clauses (b) and "with $B(U)$": **[proved]**. It gives the relativised fold step with the same count $K_0$, because the explaining pair $U$ is a near tuple of one of the winning $P_c$ (Lemma D3(ii)). (2) At level entry the relativised step is today's with "the one member consistent with the point answers" in place of a union over the list; the predicate `nextBn` (the next level's tuple is bad if $P^\ast_U$ is bad for level $i$) is unchanged. (3) At the final level the extra point check only adds a way to reject. I have not written the relativised induction over the levels in full; it follows `levelsSpec` step by step, and I see no new difficulty, but it is not checked.

### 2.8 Which steps are proved, and which are not

Proved in this note, by hand: Lemmas D1 to D6; Theorem D for every message, with the state function of section 2.5; completeness; the counting and Johnson instances of the hypothesis; Remark D0; the relativised Lemma D4.

Not proved, or proved only modulo something:

1. **Lemma D4 is the crux and is new mathematics** (note 07, Theorem 3). I re-derived every step and added the lane weights and the predicate. Numerical evidence exists for one lane on $\mathrm{GF}(2^5)$ only (note 07, section 3.3); the multi-lane form and the probability bound at real sizes are not checkable by brute force. Researcher 10's verdict should override mine.
2. **Knowledge soundness** is a sketch beyond the relativised lemma.
3. **Round-by-round to Fiat-Shamir** is inherited from the existing framework (state function with static conditions, as today's OOD separation). The potential $T_k$ is a legitimate part of the state (a function of the commitment, the points and the challenges), but nobody has checked it against the formal `Spec` structure, whose potential `V` would have to carry it.
4. **The hypothesis.** Beyond Johnson and counting, $\mathrm{ListBound}$ is conjectural, and it is needed over extension fields (Remark D0).
5. **Protocol details not exercised by the toy**: Merkle openings, grinding, the sponge order of the new messages, level 0 over $K$ with $E$-valued points, the rotation of the stack's variables. The toy checks the algebra only.

## 3. Parameters and cost

### 3.1 The model

`scripts/11_deep_fold_whir.py` (standard library; imports note 08's `whir_model.py` for the ladder and today's queries and `costs.py` for today's costs and the Merkle and sponge formulas). For each level it takes a list bound from one of three sources (Johnson; the counting bound; an assumed $\mathrm{ListBound}(\rho, \tau, 2^b)$ with $A^{(i,0)} = \lceil\tau n\rceil$), then picks the least $s_i$ and $t_i$ for which the point message and the query message are within $2^{-125}$ after their grinds. Every accept or reject is an exact integer comparison. Choices:

- **Fold round.** $K_0 = 2^{g_{\mathrm{fold}} + 2}\,q$ and $\tau = 2^{-(126 - g_{\mathrm{fold}})}$: the two terms are equal and the round is exactly $2^{-125}$ after its grind. Deployed $g_{\mathrm{fold}} = 7$: $K_0 = 2^9 q$, $\tau = 2^{-119}$. With no fold grind at all, $K_0 = 4q$ and $\tau = 2^{-126}$ still work.
- **Points.** Grind $g_{\mathrm{pt}} = 15$ (today's OOD grind). $s_i$ is the least integer with $\varepsilon^{\mathrm{pt}}_i \le 2^{-(125 - g_{\mathrm{pt}})}$.
- **Batching.** 7 bits ($513/q$).
- **Queries.** Grind 17 as today; $t_i$ least with $\varepsilon^{\mathrm{query}}_i \le 2^{-108}$.
- **Johnson levels.** The fewest queries the Johnson radius allows, then the largest threshold with that count, which makes the Johnson list small ($2^6$ to $2^{12}$).

Selftest (`selftest` argument): the Merkle byte formula reproduces note 08's for today's configurations; Johnson levels never need more queries than today's analysis and are within one of note 08's Johnson limit; every chosen $s_i$ is minimal and every message within target when recomputed in floating point. **[checked]**

Today's numbers are note 08's (exact). The new stream is: per commitment the root, a grind nonce, $2s$ sampled scalars and $s$ answers; per round $4 + s$ scalars and a nonce; the rest as today. Its sponge count uses `costs.SpongeCount` (four absorbed scalars a permutation, one permutation a sample).

### 3.2 What a point buys

T1, deployed grinds. "Bits needed" is $\log_2$ of the bracket of $\varepsilon^{\mathrm{pt}}$ at $L = 1$ plus the 110 bits of target: $s \log_2(1/\epsilon) \ge$ bits needed $+ 3\log_2 L$. **[checked]**

| level shape | $\kappa$ | $\ell$ | $\log_2(1/\epsilon)$ | bits needed at $L = 1$ | $s$ for $L = 2^{10}, 2^{40}, 2^{70}, 2^{100}, 2^{334}$ |
| --- | --- | --- | --- | --- | --- |
| $\mu = 30$ level 0 | 24 | 6 | 104.0 | 1064 | 11, 12, 13, 14, 20 |
| $\mu = 30$ level 1 | 20 | 4 | 108.0 | 826 | 8, 9, 10, 11, 17 |
| $\mu = 30$ level 3 | 12 | 4 | 116.0 | 826 | 8, 9, 9, 10, 16 |
| $\mu = 30$ level 5 | 4 | 4 | 122.9 | 826 | 7, 8, 9, 10, 15 |
| $\mu = 24$ level 4 | 2 | 4 | 123.5 | 826 | 7, 8, 9, 10, 15 |

The 1064 bits at level 0 are $384$ ($q^3$) $+ 2 - 27$ ($4/2^{27}$) $+ 595$ ($\tau^{-5}$) $+ 110$. One more point pays for 35 more bits of list at level 0 and 36 to 41 later, for 112 or 80 bytes. The nested factor is more than half of the budget; each bit of fold grind saves $\ell + 2$ bits (8 at level 0), so a fold grind of 12 bits instead of 7 saves 40 bits, less than half a point, for $2^{12}$ hashes a round.

### 3.3 Queries and proof size as a function of the proven ListBound

T3. Level 0 at the stated threshold with the stated list; later levels with no new theorem (Johnson, and counting where it wins). KiB are the whole WHIR opening, change against today in brackets. **[checked]** arithmetic; every row below the second of each rate is conditional on a **[conjectured]** list bound. The columns show that the list size hardly matters (0.1 KiB per 30 bits) and the threshold is everything.

| rate | level-0 threshold | bits a query | level-0 queries | $s_0$ at $\mu = 30$ for lists $2^{10}, 2^{40}, 2^{70}, 2^{100}$ | KiB at $\mu = 24$ / 28 / 30, list $2^{40}$ | KiB at $\mu = 30$, list $2^{100}$ | guest Keccak, $\mu = 30$, list $2^{40}$ | level-0 query cycles saved, $\mu = 30$ (est.) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | today (Johnson, CWYZ fold) | 0.498 | 218 | 1 multilinear point | 260.4 / 313.7 / 335.9 | | 8173 | |
| | Johnson, DEEP fold (no new theorem) | 0.498 | 217 | 11 (Johnson list $2^7$) | 252.1 (-3.2%) / 306.4 (-2.3%) / 332.0 (-1.2%) | | 8005 (-2.1%) | 554 |
| | $0.66\,n$ | 0.599 | 181 | 11, 12, 13, 14 | 223.9 (-14.0%) / 273.8 (-12.7%) / 297.0 (-11.6%) | 297.2 (-11.5%) | 7213 (-11.7%) | 20487 |
| | $0.64\,n$ | 0.644 | 168 | 11, 12, 13, 14 | 213.6 (-18.0%) / 261.8 (-16.5%) / 284.3 (-15.4%) | 284.5 (-15.3%) | 6923 (-15.3%) | 27685 |
| | $5n/8$ | 0.678 | 160 | 11, 12, 13, 14 | 207.3 (-20.4%) / 254.5 (-18.9%) / 276.4 (-17.7%) | 276.6 (-17.6%) | 6745 (-17.5%) | 32115 |
| | $9n/16$ | 0.830 | 131 | 11, 12, 13, 14 | 184.1 (-29.3%) / 227.6 (-27.4%) / 247.8 (-26.2%) | 248.0 (-26.2%) | 6099 (-25.4%) | 48172 |
| 1/4 | today (Johnson, CWYZ fold) | 0.994 | 109 | 1 multilinear point | 169.9 / 207.7 / 222.6 | | 6000 | |
| | Johnson, DEEP fold (no new theorem) | 0.991 | 109 | 11 (Johnson list $2^6$) | 163.6 (-3.7%) / 201.7 (-2.9%) / 220.0 (-1.2%) | | 5872 (-2.1%) | 0 |
| | $7n/16$ | 1.193 | 91 | 11, 12, 13, 14 | 148.4 (-12.6%) / 184.3 (-11.3%) / 201.5 (-9.5%) | 201.7 (-9.4%) | 5372 (-10.5%) | 10382 |
| | $3n/8$ | 1.415 | 77 | 11, 12, 13, 14 | 136.5 (-19.7%) / 170.6 (-17.9%) / 186.9 (-16.0%) | 187.1 (-15.9%) | 4977 (-17.1%) | 18458 |
| | $5n/16$ | 1.678 | 65 | 11, 12, 13, 14 | 126.1 (-25.8%) / 158.7 (-23.6%) / 174.3 (-21.7%) | 174.5 (-21.6%) | 4638 (-22.7%) | 25379 |
| 1/8 | today (Johnson, CWYZ fold) | 1.490 | 73 | 1 multilinear point | 136.8 / 168.9 / 180.7 | | 4914 | |
| | Johnson, DEEP fold (no new theorem) | 1.479 | 73 | 11 (Johnson list $2^6$) | 130.9 (-4.3%) / 163.7 (-3.1%) / 178.6 (-1.2%) | | 4804 (-2.2%) | 0 |
| | $5n/16$ | 1.678 | 65 | 11, 12, 13, 14 | 123.8 (-9.5%) / 155.6 (-7.9%) / 170.1 (-5.9%) | 170.3 (-5.8%) | 4587 (-6.7%) | 4614 |
| | $n/4$ | 2.000 | 55 | 11, 12, 13, 14 | 114.8 (-16.1%) / 145.4 (-13.9%) / 159.2 (-11.9%) | 159.4 (-11.8%) | 4304 (-12.4%) | 10382 |
| | $3n/16$ | 2.415 | 45 | 11, 12, 13, 14 | 105.7 (-22.7%) / 135.0 (-20.1%) / 148.2 (-18.0%) | 148.4 (-17.9%) | 4022 (-18.2%) | 16150 |
| 1/16 | today (Johnson, CWYZ fold) | 1.983 | 55 | 1 multilinear point | 119.4 / 147.9 / 158.7 | | 4318 | |
| | Johnson, DEEP fold (no new theorem) | 1.964 | 55 | 11 (Johnson list $2^6$) | 112.3 (-5.9%) / 140.7 (-4.8%) / 153.0 (-3.6%) | | 4115 (-4.7%) | 0 |
| | $3n/16$ | 2.415 | 45 | 11, 12, 13, 14 | 103.0 (-13.7%) / 130.1 (-12.0%) / 141.9 (-10.6%) | 142.1 (-10.5%) | 3842 (-11.0%) | 5768 |
| | $n/8$ | 3.000 | 37 | 11, 12, 13, 14 | 95.4 (-20.1%) / 121.5 (-17.8%) / 132.7 (-16.4%) | 133.0 (-16.2%) | 3616 (-16.3%) | 10382 |
| | $3n/32$ | 3.415 | 32 | 11, 12, 13, 14 | 90.6 (-24.1%) / 116.1 (-21.5%) / 127.0 (-20.0%) | 127.2 (-19.8%) | 3474 (-19.6%) | 13266 |

Reading against the attack side (note 09, section 1): at rate 1/2 the known lists start at $0.629\,n$, so the rows $0.66$ and $0.64$ are the ones a theorem could give without contradicting anything known; $5/8$ needs $b \ge 31$ and $9/16$ needs $b \ge 103$. At rate 1/4 anything below $n/2$ needs $b \ge 26$ on the present domain; at rates 1/8 and 1/16 the rows $n/4$ and $n/8$ need $b \ge 51$ and $b \ge 77$. At $\mu = 30$ level 0 takes 11 points up to $b = 26$, 12 up to 61, 13 up to 95, 14 up to 130: every one of these budgets costs at most three points over the minimum.

T4. The same exponent at every level: threshold $\rho_i^\gamma n_i$ with $\gamma = \log\tau/\log\rho_0$, lists $2^{40}$ at every level ($\gamma = 1/2$ is Johnson, 1 is capacity). All **[conjectured]** inputs; this is the size of the prize, not a proposal.

| rate | $\gamma$ (level-0 threshold) | queries per level ($\mu = 30$) | points per level | KiB at $\mu = 24$ / 28 / 30 | native Keccak, $\mu = 30$ | guest Keccak, $\mu = 30$ |
| --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 0.599 ($0.66\,n$) | 181 46 26 19 14 12 | 12 9 9 9 8 8 | 221.3 (-15.0%) / 266.5 (-15.1%) / 285.4 (-15.1%) | 8479 (-16.3%) | 6894 (-15.7%) |
| 1/2 | 0.644 ($0.64\,n$) | 168 42 24 17 13 11 | 12 9 9 9 8 8 | 206.0 (-20.9%) / 247.7 (-21.0%) / 265.2 (-21.1%) | 7850 (-22.5%) | 6400 (-21.7%) |
| 1/2 | 0.678 ($5n/8$) | 160 40 23 16 13 10 | 12 9 9 9 8 8 | 197.3 (-24.2%) / 237.0 (-24.5%) / 253.6 (-24.5%) | 7492 (-26.0%) | 6119 (-25.1%) |
| 1/2 | 0.830 ($9n/16$) | 131 33 19 14 11 9 | 12 9 9 9 8 8 | 165.6 (-36.4%) / 199.1 (-36.6%) / 212.9 (-36.6%) | 6244 (-38.4%) | 5144 (-37.1%) |
| 1/4 | 0.596 ($7n/16$) | 91 37 23 17 13 11 | 12 9 9 9 8 8 | 146.1 (-14.0%) / 177.8 (-14.4%) / 190.1 (-14.6%) | 5642 (-16.1%) | 5065 (-15.6%) |
| 1/4 | 0.708 ($3n/8$) | 77 31 20 14 11 9 | 12 9 9 9 8 8 | 125.7 (-26.0%) / 153.3 (-26.2%) / 163.0 (-26.8%) | 4807 (-28.6%) | 4335 (-27.7%) |
| 1/4 | 0.839 ($5n/16$) | 65 26 17 12 10 8 | 12 9 9 9 8 8 | 108.6 (-36.1%) / 132.0 (-36.5%) / 140.8 (-36.7%) | 4132 (-38.6%) | 3744 (-37.6%) |
| 1/8 | 0.559 ($5n/16$) | 65 33 22 17 13 11 | 12 9 9 9 8 8 | 125.4 (-8.4%) / 153.6 (-9.1%) / 163.9 (-9.3%) | 4885 (-10.9%) | 4404 (-10.4%) |
| 1/8 | 0.667 ($n/4$) | 55 28 19 14 11 10 | 12 9 9 9 8 8 | 108.1 (-21.0%) / 132.7 (-21.4%) / 141.6 (-21.7%) | 4194 (-23.5%) | 3796 (-22.8%) |
| 1/8 | 0.805 ($3n/16$) | 45 23 15 12 9 8 | 12 9 9 9 8 8 | 91.2 (-33.3%) / 111.0 (-34.3%) / 118.2 (-34.6%) | 3481 (-36.5%) | 3169 (-35.5%) |
| 1/16 | 0.604 ($3n/16$) | 45 26 18 14 12 10 | 12 9 9 9 8 8 | 101.2 (-15.2%) / 124.7 (-15.7%) / 132.7 (-16.4%) | 3950 (-18.3%) | 3561 (-17.5%) |
| 1/16 | 0.750 ($n/8$) | 37 21 15 12 10 8 | 12 9 9 9 8 8 | 85.5 (-28.4%) / 105.0 (-29.0%) / 111.7 (-29.6%) | 3304 (-31.6%) | 2994 (-30.7%) |
| 1/16 | 0.854 ($3n/32$) | 32 19 13 10 8 7 | 12 9 9 9 8 8 | 76.0 (-36.4%) / 92.4 (-37.5%) / 98.2 (-38.1%) | 2895 (-40.1%) | 2637 (-38.9%) |

Level 0 carries two thirds to three quarters of the gain (compare T3), so a list bound at the level-0 rate alone is most of the prize. With lists $2^{100}$ instead of $2^{40}$ every row is 0.7 to 1.0 KiB larger (points 14 11 11 10 10 10).

### 3.4 Verifier and prover work, grinding

T6 (excerpt; the script prints every rate). "No new theorem" configuration. Verifier multiplications are counted from `whir.rs` by formula (docstring of `verifier_mults`; EE is $E \times E$, "all" adds $E \times K$ and $K \times K$): **[checked]** as a count, not measured. Guest point cycles: **[estimate]**, two cycles a multiplication of the point path plus 20 a point, the ratio note 08 fitted on the query path. The last column is $2 s_0 2^\mu$ over $\tfrac12\kappa_0 2^{\mu + R}$.

| $\mu$ | rate | grinds query/fold/point/batch | points per level | KiB | guest Keccak | grind ($\log_2$ perms) | verifier mults EE / all (today) | guest point cycles (est.) | point clmul over level-0 NTT mults |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 24 | 1/2 | 17/7/15/7 | 10 8 8 26 9 | 252.1 (-3.2%) | 5530 (-3.8%) | 19.65 | 17425 / 69325 (14694 / 66674) | 10278 | 1.11 |
| 24 | 1/2 | 17/0/0/7 | 11 8 8 27 10 | 252.0 (-3.2%) | 5527 (-3.8%) | 19.32 | 17590 / 69548 | 10784 | 1.22 |
| 24 | 1/4 | 17/7/15/7 | 10 8 8 28 10 | 163.6 (-3.7%) | 4163 (-3.6%) | 19.65 | 11576 / 42102 (8610 / 38820) | 10644 | 0.56 |
| 28 | 1/2 | 17/7/15/7 | 11 8 8 8 28 10 | 306.4 (-2.3%) | 7687 (-2.5%) | 19.91 | 20152 / 83330 (16404 / 79102) | 13408 | 1.00 |
| 28 | 1/2 | 17/0/0/7 | 11 9 8 8 29 10 | 306.1 (-2.4%) | 7682 (-2.5%) | 19.59 | 20276 / 83506 | 13800 | 1.00 |
| 28 | 1/4 | 17/7/15/7 | 11 8 8 8 31 11 | 201.7 (-2.9%) | 5025 (-3.6%) | 19.91 | 13805 / 52029 (9808 / 47176) | 13910 | 0.50 |
| 30 | 1/2 | 17/7/15/7 | 11 8 8 8 8 15 | 332.0 (-1.2%) | 8005 (-2.1%) | 19.91 | 20946 / 89911 (17111 / 85422) | 12918 | 0.92 |
| 30 | 1/2 | 17/0/0/7 | 12 9 9 8 8 16 | 331.8 (-1.2%) | 8006 (-2.0%) | 19.59 | 21271 / 90372 | 13920 | 1.00 |
| 30 | 1/2 | 17/12/20/7 | 11 8 8 8 7 15 | 331.9 (-1.2%) | 7998 (-2.1%) | 22.78 | 20896 / 89843 | 12762 | 0.92 |
| 30 | 1/4 | 17/7/15/7 | 11 8 8 8 8 15 | 220.0 (-1.2%) | 5872 (-2.1%) | 19.91 | 14201 / 56443 (10276 / 51508) | 12918 | 0.46 |
| 30 | 1/16 | 17/7/15/7 | 11 8 8 8 8 16 | 153.0 (-3.6%) | 4115 (-4.7%) | 19.91 | 10349 / 37080 (6462 / 32538) | 13072 | 0.11 |

- **Native verifier.** At Johnson thresholds the points add about 5 percent to the field multiplications (20 percent to the $E \times E$ ones), and nothing to the Merkle work, which dominates. With a lowered threshold the query savings dominate: at $\mu = 30$, rate 1/2, $\mathrm{ListBound}(0.64, 2^{40})$ gives 76,251 multiplications against 85,422 and 8505 native Keccak permutations against 10,130.
- **Guest.** A level-0 query costs about 480 cycles (note 08, measured at $\mu = 23$), the points about 13,000 in all (estimate), so the change alone costs the guest about as much as 27 level-0 queries and pays for itself only with a lowered threshold: at $0.64\,n$ the level-0 queries save about 27,700 cycles, net about 15,000 of the roughly 161,000 query cycles. Keccak counts fall in every row because queries fall and the sponge grows by only 73 permutations.
- **Grinding.** The fold and point grinds can be removed for at most one more point at some levels (rows 17/0/0/7): the same bytes, one nonce and one grind check fewer per fold round and per commitment (32 at $\mu = 30$), and total grinding falls from $2^{19.9}$ to $2^{19.6}$ permutations. More fold grinding buys nothing visible. The batching grind is 7 bits in every row. I would deploy without the fold and point grinds; it is one constant.
- **Prover. [proved]** count, **time not measured.** For each level-0 point the prover needs the $2^{\ell_0}$ lane values $P_u(\zeta_m)$; every later answer of the level is these values folded by the challenges (E3), no further pass over the stack. That is $2^\mu$ products $K \times E$ per point (two carry-less multiplications each, accumulated unreduced against a table of $\mathcal{X}_c(\zeta_m)$ for the low half of the bits, one $E \times E$ product per block), all $s_0$ points fused into the single pass that computes today's OOD value. Total $2 s_0 2^\mu$ carry-less multiplications: at $s_0 = 12$, $\kappa_0 = 24$ this equals the level-0 NTT's $\tfrac12\kappa_0 2^{\mu + R}$ multiplications at rate 1/2, half of them at rate 1/4, an eighth at rate 1/16. The NTT's are full products with reduction, stores and several passes; these are accumulate-only in one streaming pass. Level 0's commitment is about a fifth of proving time in note 08's measured run, so my guess is 3 to 10 percent of proving time at rate 1/2. It needs a measurement before anyone relies on it. Later levels are $2^{6}$ times smaller.

### 3.5 The error budget of one configuration

T7: $\mu = 30$, rate 1/2, $\mathrm{ListBound}(1/2, 0.64, 2^{40})$ at level 0, $\log_2$ of each message's error. **[checked]**

| message | before the grind | grind bits | after |
| --- | --- | --- | --- |
| batching $\lambda_0$ ($J_0 = 514$) | -119.00 | 7 | -126.00 |
| points of level 0 ($s = 12$, $L = 2^{40}$, assumed) | -174.00 | 15 | -189.00 |
| each of the 6 fold rounds of level 0 | -118.00 | 7 | -125.00 |
| query message of level 0 ($t = 168$) | -108.17 | 17 | -125.17 |
| points of level 1 ($s = 8$, $L = 2^6$, Johnson) | -130.28 | 15 | -145.28 |
| each of the 4 fold rounds of levels 1 to 5 | -118.00 | 7 | -125.00 |
| query messages of levels 1 to 4 ($t = 55, 31, 22, 17$) | -108.00 | 17 | -125.00 |
| points of levels 2, 3, 4 ($s = 8$, Johnson) | -153.43, -188.10, -216.61 | 15 | below -168 |
| points of level 5 ($s = 15$, $L = 2^{339}$, counting) | -110.29 | 15 | -125.29 |
| query message of level 5 ($t = 7$) | -108.34 | 17 | -125.34 |
| each tail round | -127.00 | 0 | -127.00 |

## 4. What is available with no new theorem

Everything in this section is unconditional given Theorem D. **[proved]** list bounds, **[checked]** arithmetic.

**4.1 Johnson thresholds without their slack.** Today's analysis stops short of the Johnson radius for three reasons that the DEEP fold removes: list factors on terms of order $1/q$ (batching $513 L_0 \le 2^{16}$, OOD pairs), the interpolation inequality of `def:epsaff` at small sizes, and $\varepsilon_{\mathrm{aff}}$ itself. With Protocol D every level reaches note 08's "Johnson limit" column: one query fewer on most levels (217 55 31 22 17 14 against 218 55 32 23 18 15 at $\mu = 30$, rate 1/2), and two or three fewer on the last levels of small stacks. This alone does not pay for the points: T2's "DEEP, Johnson" rows are within $+2.0$ and $-1.0$ percent of today's bytes.

**4.2 Counting at the last levels.** The counting bound $\binom{n}{d+1}/\binom{A}{d+1}$ is astronomically large and still affordable where $d$ is small, because lists enter only as $3\log_2 L$ bits against about 120 bits a point. T5 (`counting_level` takes the threshold with the fewest bytes):

| ladder | level | $\kappa$ | $d$ | $n$ | Johnson: queries, $s$, bytes | counting: queries, $s$, $\log_2 L$, bytes | saved |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $\mu = 24$, rate 1/2 | 3 (last but one) | 6 | 67 | $2^{16}$ | 22, 8, 13897 | 11, 26, 762, 9080 | 4816 B |
| $\mu = 24$, rate 1/2 | 4 (last) | 2 | 7 | $2^{15}$ | 18, 7, 11004 | 10, 9, 92, 6811 | 4193 B |
| $\mu = 24$, rate 1/16 | 3 (last but one) | 6 | 67 | $2^{19}$ | 17, 8, 12728 | 9, 28, 852, 8922 | 3805 B |
| $\mu = 24$, rate 1/16 | 4 (last) | 2 | 7 | $2^{18}$ | 15, 7, 10837 | 8, 10, 112, 6532 | 4305 B |
| $\mu = 28$, rate 1/2 | 4 (last but one) | 6 | 67 | $2^{19}$ | 17, 8, 12728 | 9, 28, 852, 8922 | 3805 B |
| $\mu = 28$, rate 1/2 | 5 (last) | 2 | 7 | $2^{18}$ | 15, 7, 10837 | 8, 10, 112, 6532 | 4305 B |
| $\mu = 28$, rate 1/16 | 4 (last but one) | 6 | 67 | $2^{22}$ | 14, 8, 12071 | 7, 34, 1103, 8679 | 3392 B |
| $\mu = 28$, rate 1/16 | 5 (last) | 2 | 7 | $2^{21}$ | 12, 7, 10065 | 7, 10, 125, 6535 | 3530 B |
| $\mu = 30$, rate 1/2 | 4 (last but one) | 8 | 259 | $2^{21}$ | 17, 8, 13816 | no gain | 0 |
| $\mu = 30$, rate 1/2 | 5 (last) | 4 | 19 | $2^{20}$ | 14, 7, 11095 | 7, 15, 339, 6711 | 4383 B |
| $\mu = 30$, rate 1/16 | 4 (last but one) | 8 | 259 | $2^{24}$ | 14, 8, 12967 | no gain | 0 |
| $\mu = 30$, rate 1/16 | 5 (last) | 4 | 19 | $2^{23}$ | 12, 7, 10833 | 6, 16, 376, 6629 | 4204 B |

So the last level runs near capacity (7 queries instead of 14 or 15; note 07 estimated 9 or 8), and when the ladder ends on $\kappa = 2$ (stacks with $\mu \equiv 0 \bmod 4$) the level before it, $\kappa = 6$, gains too, with 26 to 34 points. At $\kappa = 8$ the list ($2^{2000}$ and more) costs more points than the queries save. No other elementary bound applies: Johnson and counting are the two consequences of "two codewords agree on at most $d$ columns", and nothing between them is known for these parameters.

**4.3 The total.** T2 (every rate and size). "DEEP, Johnson" uses 4.1 only; "DEEP, Johnson + counting" adds 4.2.

| $\mu$ | rate | | queries per level | points per level | list bounds ($\log_2$) | WHIR KiB | point scalars, KiB | native Keccak | guest Keccak | verifier mults EE / all |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 24 | 1/2 | today | 218 55 32 23 20 | 1 multilinear | 127 171 194 152 105 (plain) | 260.4 | | 7684 | 5748 | 14694 / 66674 |
| | | DEEP, Johnson | 217 55 31 22 18 | 10 8 8 8 7 | 7 6 9 9 9 | 260.9 (+0.2%) | 3.5 | 7649 (-0.5%) | 5735 (-0.2%) | 16944 / 69483 |
| | | DEEP, Johnson + counting | 217 55 31 11 10 | 10 8 8 26 9 | 7 6 9 762 92 | 252.1 (-3.2%) | 5.1 | 7378 (-4.0%) | 5530 (-3.8%) | 17425 / 69325 |
| 24 | 1/4 | today | 109 44 28 21 18 | 1 multilinear | 127 171 194 216 149 (plain) | 169.9 | | 5012 | 4318 | 8610 / 38820 |
| | | DEEP, Johnson | 109 44 28 20 17 | 10 8 8 8 7 | 6 6 6 9 8 | 172.2 (+1.4%) | 3.5 | 5034 (+0.4%) | 4348 (+0.7%) | 10953 / 42023 |
| | | DEEP, Johnson + counting | 109 44 28 10 9 | 10 8 8 28 10 | 6 6 6 825 102 | 163.6 (-3.7%) | 5.3 | 4774 (-4.7%) | 4163 (-3.6%) | 11576 / 42102 |
| 24 | 1/8 | today | 73 37 25 19 17 | 1 multilinear | 127 171 194 229 211 (plain) | 136.8 | | 4050 | 3524 | 6415 / 28800 |
| | | DEEP, Johnson | 73 37 25 19 16 | 10 8 8 7 7 | 6 6 6 7 8 | 139.6 (+2.0%) | 3.4 | 4083 (+0.8%) | 3561 (+1.1%) | 8737 / 32029 |
| | | DEEP, Johnson + counting | 73 37 25 10 8 | 10 8 8 26 10 | 6 6 6 764 121 | 130.9 (-4.3%) | 5.2 | 3823 (-5.6%) | 3378 (-4.1%) | 9339 / 32134 |
| 24 | 1/16 | today | 55 32 23 18 16 | 1 multilinear | 127 171 194 229 296 (plain) | 119.4 | | 3549 | 3082 | 5250 / 23488 |
| | | DEEP, Johnson | 55 31 22 17 15 | 10 8 8 8 7 | 6 9 8 9 8 | 120.3 (+0.7%) | 3.5 | 3522 (-0.8%) | 3070 (-0.4%) | 7535 / 26427 |
| | | DEEP, Johnson + counting | 55 31 22 9 8 | 10 8 8 28 10 | 6 9 8 852 112 | 112.3 (-5.9%) | 5.3 | 3288 (-7.4%) | 2906 (-5.7%) | 8219 / 26718 |
| 28 | 1/2 | today | 218 55 32 23 18 16 | 1 multilinear | 127 154 171 194 229 296 (plain) | 313.7 | | 9409 | 7883 | 16404 / 79102 |
| | | DEEP, Johnson | 217 55 31 22 17 15 | 11 8 8 8 8 7 | 7 6 9 8 9 8 | 314.4 (+0.2%) | 4.2 | 9357 (-0.6%) | 7851 (-0.4%) | 19468 / 83039 |
| | | DEEP, Johnson + counting | 217 55 31 22 9 8 | 11 8 8 8 28 10 | 7 6 9 8 852 112 | 306.4 (-2.3%) | 6.0 | 9123 (-3.0%) | 7687 (-2.5%) | 20152 / 83330 |
| 28 | 1/4 | today | 109 44 28 21 17 15 | 1 multilinear | 127 154 171 194 229 296 (plain) | 207.7 | | 6235 | 5213 | 9808 / 47176 |
| | | DEEP, Johnson | 109 44 28 20 16 14 | 11 8 8 8 8 7 | 6 6 6 8 9 9 | 209.8 (+1.0%) | 4.2 | 6230 (-0.1%) | 5218 (+0.1%) | 12958 / 51527 |
| | | DEEP, Johnson + counting | 109 44 28 20 8 7 | 11 8 8 8 31 11 | 6 6 6 8 977 137 | 201.7 (-2.9%) | 6.4 | 5989 (-3.9%) | 5025 (-3.6%) | 13805 / 52029 |
| 28 | 1/8 | today | 73 37 25 19 16 15 | 1 multilinear | 127 154 171 194 229 296 (plain) | 168.9 | | 5088 | 4283 | 7413 / 35580 |
| | | DEEP, Johnson | 73 37 25 19 15 13 | 11 8 8 8 8 7 | 6 6 6 7 9 10 | 171.0 (+1.2%) | 4.2 | 5082 (-0.1%) | 4284 (+0.0%) | 10575 / 40003 |
| | | DEEP, Johnson + counting | 73 37 25 19 8 7 | 11 8 8 8 31 10 | 6 6 6 7 941 128 | 163.7 (-3.1%) | 6.3 | 4869 (-4.3%) | 4103 (-4.2%) | 11429 / 40596 |
| 28 | 1/16 | today | 55 32 23 18 15 14 | 1 multilinear | 127 154 171 194 229 296 (plain) | 147.9 | | 4472 | 3975 | 6121 / 29352 |
| | | DEEP, Johnson | 55 31 22 17 14 12 | 11 8 8 8 8 7 | 6 9 8 9 9 12 | 147.5 (-0.3%) | 4.2 | 4384 (-2.0%) | 3913 (-1.6%) | 9190 / 33331 |
| | | DEEP, Johnson + counting | 55 31 22 17 7 7 | 11 8 8 8 34 10 | 6 9 8 9 1103 125 | 140.7 (-4.8%) | 6.5 | 4193 (-6.2%) | 3762 (-5.4%) | 10191 / 34142 |
| 30 | 1/2 | today | 218 55 32 23 18 15 | 1 multilinear | 127 148 162 181 209 256 (plain) | 335.9 | | 10130 | 8173 | 17111 / 85422 |
| | | DEEP, Johnson | 217 55 31 22 17 14 | 11 8 8 8 8 7 | 7 6 9 8 9 10 | 336.2 (+0.1%) | 4.2 | 10056 (-0.7%) | 8120 (-0.7%) | 20595 / 89893 |
| | | DEEP, Johnson + counting | 217 55 31 22 17 7 | 11 8 8 8 8 15 | 7 6 9 8 9 339 | 332.0 (-1.2%) | 4.9 | 9927 (-2.0%) | 8005 (-2.1%) | 20946 / 89911 |
| 30 | 1/4 | today | 109 44 28 21 17 15 | 1 multilinear | 127 148 162 181 209 256 (plain) | 222.6 | | 6728 | 6000 | 10276 / 51508 |
| | | DEEP, Johnson | 109 44 28 20 16 13 | 11 8 8 8 8 8 | 6 6 6 8 9 12 | 223.9 (+0.6%) | 4.3 | 6688 (-0.6%) | 5974 (-0.4%) | 13892 / 56418 |
| | | DEEP, Johnson + counting | 109 44 28 20 16 7 | 11 8 8 8 8 15 | 6 6 6 8 9 318 | 220.0 (-1.2%) | 4.9 | 6568 (-2.4%) | 5872 (-2.1%) | 14201 / 56443 |
| 30 | 1/8 | today | 73 37 25 19 16 15 | 1 multilinear | 127 148 162 181 209 256 (plain) | 180.7 | | 5482 | 4914 | 7783 / 39128 |
| | | DEEP, Johnson | 73 37 25 19 15 13 | 11 8 8 8 8 7 | 6 6 6 7 9 9 | 182.6 (+1.0%) | 4.2 | 5457 (-0.5%) | 4901 (-0.3%) | 11371 / 44103 |
| | | DEEP, Johnson + counting | 73 37 25 19 15 7 | 11 8 8 8 8 15 | 6 6 6 7 9 313 | 178.6 (-1.2%) | 4.9 | 5338 (-2.6%) | 4804 (-2.2%) | 11737 / 44195 |
| 30 | 1/16 | today | 55 32 23 18 16 14 | 1 multilinear | 127 148 162 181 209 256 (plain) | 158.7 | | 4832 | 4318 | 6462 / 32538 |
| | | DEEP, Johnson | 55 31 22 17 14 12 | 11 8 8 8 8 7 | 6 9 8 9 9 10 | 157.2 (-1.0%) | 4.2 | 4694 (-2.9%) | 4209 (-2.5%) | 9926 / 36921 |
| | | DEEP, Johnson + counting | 55 31 22 17 14 6 | 11 8 8 8 8 16 | 6 9 8 9 9 376 | 153.0 (-3.6%) | 5.0 | 4576 (-5.3%) | 4115 (-4.7%) | 10349 / 37080 |

Verdict: with no new theorem the change is worth 1 to 6 percent of the opening (most at small stacks and low rates), a slightly cheaper Keccak count, a slightly dearer field count, and a soundness proof that no longer needs the affine MCA theorem. That is not a reason to deploy it; it is a complete, unconditional instance of the mechanism, including levels that run beyond the Johnson radius.

## 5. Lean-shaped statements against the existing formalization

Shapes only: nothing below was compiled. Names follow `formal/lean_vm/LeanVM/Protocol/Whir/Sound/` and `ToArkLib/Whir/`.

**The hypothesis.** `tlist` is `Sound/Tuple.lean`'s (it equals `AffineCombiner.tupleList` through `agreeT = agree`, as `FoldRoundCwyz.lean` already uses).

```lean
/-- Every interleaved word on `dom`, of any lane type, has at most `L` tuples of degree ≤ d within agreement `A`. -/
def ListBound {n : ℕ} (dom : Fin n ↪ E) (d A L : ℕ) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] (Q : ρ → Fin n → E), (tlist dom Q A d).card ≤ L

theorem listBound_johnson {n} (dom : Fin n ↪ E) {d A : ℕ} (hgap : n * d < A * A) :
    ListBound dom d A (jl n A d) := fun _ _ Q ↦ card_tlist_le_jl dom Q A d hgap      -- exists today

theorem listBound_counting {n} (dom : Fin n ↪ E) {d A : ℕ} (hA : d + 1 ≤ A) :
    ListBound dom d A (n.choose (d + 1) / A.choose (d + 1))                           -- new, a double count
```

**Points.** A new file `Sound/Points.lean` (Definition D1, Lemma D1).

```lean
/-- `ev_z^{(j)}` on a tuple of `m` lane variables, the level's variables `j+1 .. j+m`. -/
noncomputable def evPt (j : ℕ) {m : ℕ} (z : E × E) : ((Fin m → Bool) → E[X]) →ₗ[E] E where
  toFun U := ∑ u, z.1 ^ (∑ k : Fin m, if u k then 0 else 2 ^ (j + k)) * (U u).eval z.2
  ...
theorem evPt_joinT (z) (F G : (Fin m → Bool) → E[X]) :                               -- (E2)
    evPt j z (joinT F G) = z.1 ^ 2 ^ j * evPt (j + 1) z F + evPt (j + 1) z G
theorem evPt_smul (z) (a : E[X]) (U) : evPt j z (fun u ↦ a * U u) = a.eval z.2 * evPt j z U   -- (E3)
theorem card_evPt_eq_zero_le (hU : U ≠ 0) (hd : DegLE Δ U) :                         -- (E4), replaces Ood.lean's count
    (univ.filter fun z : E × E ↦ evPt j z U = 0).card ≤ (Δ + 2 ^ (j + m)) * Fintype.card E
```

**The fold round.** `FoldRoundBound` gains the points and becomes a property of one word and one vector of points; the theorem bounds the vectors for which it fails.

```lean
/-- The DEEP fold-round lemma in counting form (Lemma D4(2)), for the halves `f g` and the points `z`. -/
def DeepFoldRoundBound {n s : ℕ} (dom : Fin n ↪ E) (d A N : ℕ) {ρ : Type} [Fintype ρ]
    (ev : Fin s → (ρ → E[X]) →ₗ[E] E) (ζ : Fin s → E) (f g : ρ → Fin n → E) : Prop :=
  ∀ (Λ₀ Λ₁ : (ρ → E[X]) →ₗ[E] E) (c : E) (Bp : (ρ → E[X]) → (ρ → E[X]) → Prop) (yF yG : Fin s → E),
    (∀ F G, DegLE d F → DegLE d G → A - 1 ≤ (agreeT dom F f ∩ agreeT dom G g).card → Bp F G →
      (∀ i, ev i F = yF i ∧ ev i G = yG i) → Λ₀ F + Λ₁ G ≠ c) →
    ∀ u₀ v c₀ c₁ : E, (univ.filter fun t : E × E ↦ ∃ P : ρ → E[X], DegLE d P ∧
        A ≤ (agreeT dom P fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x).card ∧
        (∀ F G, NearPairT dom d f g (agreeT dom P fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x) F G → Bp F G) ∧
        (∀ i, ev i P = yG i + (t.1 + t.2 * ζ i) * yF i) ∧
        (1 - t.1) * Λ₀ P + t.1 * Λ₁ P =
          u₀ + t.1 * (c - u₀) + t.1 ^ 2 * v + t.2 * c₀ + t.1 * t.2 * (c₁ - c₀)).card ≤ N

/-- Lemma D4(1): few point vectors are exceptional. `q = Fintype.card E`. -/
theorem card_deepExc_le {n s j m : ℕ} (dom : Fin n ↪ E) {d A L K₀ : ℕ}
    (hL : ∀ t : E × E, (tlist dom (fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x) A d).card ≤ L)
    (hK : 30 ≤ K₀) (h2q : 200 * q ≤ 74 * K₀) (hn : 100 * n.choose 2 ≤ 74 * K₀) (hA : d + 2 ≤ A) :
    (univ.filter fun z : Fin s → E × E ↦
        ¬ DeepFoldRoundBound dom d A K₀ (fun i ↦ evPt (j + 1) (z i)) (fun i ↦ (z i).2) f g).card * K₀ ^ 3
      ≤ 4 * L ^ 3 * q ^ 6 * (d + 2 ^ (j + 1 + m)) ^ s * q ^ s
```

**The level's hypotheses.** `RoundBounds` is replaced (its `bound` field was the CWYZ lemma; now the bound is a theorem and the structure carries the list hypothesis and arithmetic).

```lean
structure RoundBoundsD (P : LevelCode) (s : ℕ) (εmax : ENNReal) where
  L : ℕ
  K₀ : ℕ
  τ : ℚ≥0
  hA : P.ℓ + P.deg + 2 ≤ P.A
  list : ListBound P.dom P.deg (P.thr 0) L                       -- the only non-arithmetic field
  hK : 30 ≤ K₀ ∧ 200 * q ≤ 74 * K₀ ∧ 100 * P.n.choose 2 ≤ 74 * K₀
  eF : (2 : ENNReal)⁻¹ ^ Whir.foldGrindingBits * (K₀ / q ^ 2 + τ) ≤ εmax
  ePt : (2 : ENNReal)⁻¹ ^ Whir.pointGrindingBits *
      ((L.choose 2 + 4 * L ^ 3 * q ^ 6 / K₀ ^ 3 * ∑ j ∈ range P.ℓ, τ⁻¹ ^ j) * ((P.deg + 2 ^ P.ℓ) / q) ^ s) ≤ εmax
```

`MidOK` loses `gap` (the Johnson hypothesis of the next level) and `eO`, `eO1` (the OOD point), and its `eQ` reads `eQuery P t + (t + s) / q` with `s` the level's points; `FinalOK` is unchanged. `LadderOK` threads the `s i`.

**The invariant.** `RoundInv` gains the level's points and carried values (read off the history, as `rounds` is) and the potential:

```lean
/-- `T_k` of Lemma D6 for the rounds still to come. -/
noncomputable def pointPot (P : LevelCode) (τ : ℚ≥0) (K₀ : ℕ) (O : ℕ → Fin P.n → E)
    (z : Fin s → E × E) (rounds : List FoldRound) : ℚ≥0 :=
  ∑ j ∈ Finset.Ico rounds.length P.ℓ, τ⁻¹ ^ (j - rounds.length) *
    ((univ.filter fun cs : Fin (j - rounds.length) → E × E ↦
        ¬ DeepFoldRoundBound P.dom P.deg (P.thr (j + 1)) K₀ (fun i ↦ evPt (j + 1) (z i)) (fun i ↦ (z i).2)
            (half false (foldsA P.dom (rounds ++ List.ofFn (mk ∘ cs)) O))
            (half true (foldsA P.dom (rounds ++ List.ofFn (mk ∘ cs)) O))).card : ℚ≥0)
      / q ^ (2 * (j - rounds.length))

def RoundInvD (s : WhirState) (rounds : List FoldRound) (z : Fin sᵢ → E × E) (v : Fin sᵢ → E)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  [the first four clauses of RoundInv] ∧
  TViol P.κ P.dom (rowsOf (P.ℓ - rounds.length) (foldsA P.dom rounds (laneO i cs P.n)))
    (runW w ℓ₀ s) s.claim (P.thr rounds.length) P.deg
    (fun U ↦ roundPred i P B rounds cs (P.ℓ - rounds.length) U ∧ ∀ k, evPt rounds.length (z k) U = v k) ∧
  pointPot P τ K₀ (laneO i cs P.n) z rounds < 1
```

**The theorem.** `whirSpec` and `stackedSpec` keep their statements with `RB : ∀ j, RoundBoundsD (codes j) (pts j) εmax` in place of `RoundBounds`, a `WhirPre` that reads "every candidate of the level-0 word at level 0's threshold *that satisfies the commitment's point claims* violates `(w, t)`, and the commitment's points are good", and `stackedSpec`'s lead `eBatch claims.length 1`, that is $(J - 1)/|E|$, with no `L₀`, `hfin`, `hL₀`. The commitment's point message gets its own specification with escape `ePt` (as the OOD point has `escRet_oodPoint_le` today). The post-condition `traceGood` is unchanged.

**Files.**

| file(s) | fate |
| --- | --- |
| `ToArkLib/Whir/AffineCombiner{Chart, Core, Excluded, Factor, FactorCount, Hensel, Interpolation, Lemma43, Mca, Packing, Params, ReducedFactor, Reduction, Trivariate, YZDegree, Deployed, DeployedTable}.lean` (17 files, about 4300 lines: interpolation, Hensel lifting, the factor counts, the admissible triples and their certificate table) | delete |
| `ToArkLib/Whir/AffineCombinerDefs.lean` (`agree`, `pairList`, `tupleList`, `DegLE`) | keep |
| `ToArkLib/Whir/AffineCombinerFold.lean`, `AffineCombinerFoldRel.lean` | replace by one file `DeepFold.lean`: Lemmas D2, D3, D4. It keeps the degree-two residual count ("$2q$ zeros") and `NearPair` from them. Expected size: a few hundred lines; the ingredients are polynomial identities in characteristic two, divisibility by a polynomial of degree one, root counting and Markov |
| `ToArkLib/Whir/Johnson.lean`, `JohnsonCount.lean`, `Counting.lean`, `Interleaved.lean` | keep (Johnson becomes one instance of `ListBound`; add `listBound_counting`) |
| `ToArkLib/Whir/Ood.lean` | replace by the bivariate count `card_evPt_eq_zero_le` and the pinning count |
| `Sound/FoldRoundCwyz.lean` | delete |
| `Sound/FoldRound.lean` | replace: `DeepFoldRoundBound`, `card_foldEsc_le` with the point claims in `foldEsc` |
| `Sound/Folds.lean` | replace `RoundBounds`, `RoundInv`, `foldRoundSpec`; add the potential step (Lemma D6(b)) |
| `Sound/LevelMid.lean`, `LevelFacts.lean`, `Escape.lean`, `Group.lean` | adapt: points in place of the OOD point, pinning in place of OOD separation, `eLam` without the list, the converted claims in `glueLevel` |
| `Sound/LevelFinal.lean` | adapt: the final point check |
| `Sound/Weights.lean` | adapt: `eqEval` weight out, column weight at a point of `E` in (the existing `inducedWeight` lemmas at `x ∈ E`) |
| `Sound/Spec.lean`, `Start.lean` | adapt as above |
| `Sound/Code.lean`, `Tuple.lean`, `State.lean`, `Sumcheck.lean`, `Tail.lean`, `Queries.lean`, `Prob.lean`, `Generic.lean`, `Novel.lean`, `Lanes.lean`, `Cut.lean`, `Descent*.lean`, `Newton*.lean`, `LowMsgC.lean`, `StackA.lean`, `Candidates.lean` | keep (`LevelCode.listMax` becomes a field of `RoundBoundsD`) |
| `Whir/Params/{Check, Deployed, DescentCheck, Iface}.lean` | the fold-round certificate (`foldRoundOK` and its table) goes; the level check becomes the two inequalities `eF`, `ePt` and the query inequality |
| `Statement/LeanVmVerifier.lean`, `lean_vm/LeanVM/Wire/Encoding.lean` | change with the Rust verifier (new stream) |

Net effect on the trusted base and the proof: the deepest part of the present development (the CWYZ interpolation argument and its kernel-checked parameter table) is replaced by an elementary lemma plus a named hypothesis. With Johnson lists the hypothesis is discharged by the existing `card_tlist_le_jl`, so the end theorem stays unconditional.

## 6. Remarks on note 07 and on the red team's target

I assumed Theorem 3 of note 07 and re-derived it as Lemmas D2 to D4. What I checked and what I changed:

1. **The lemma.** Every step of Lemma 1, Lemma 2, Theorem 3 and Corollary 4 holds as far as I can see. The three thresholds on $|\mathcal{W}'|$ that the argument needs are: more than $q$ (polynomial pair, and consistency with the answers), more than $\binom{n}{2}$ (membership in the pair list), more than $2q$ (the claim). All follow from $0.74 K_0 \ge \max(2q, \binom{n}{2})$. I did not find an error. Things a red team might probe that I could not test: the Markov step is over the product of $s$ independent points and needs $Q \ne 0$ to be independent of them, which holds because $\mathcal{T}$ is defined before the points; the bound $|\mathcal{T}| \le \Lambda q^2$ needs the list bound for every folded word, including those of $h$ lanes.
2. **Lane weights. Changed.** Note 07 uses $\mathrm{eq}(r, \cdot)$ and recovers the second half's value by dividing by $r_{i,j}$, with the event $r_{i,j} = 0$ charged to the points. Monomial weights in one scalar remove the division, the event and $\ell - 1$ sampled coordinates a point.
3. **The fold term. Sharpened.** Note 07 states $K_0/q^2 + \tau$ for the fold and $2\varepsilon_{\mathrm{pt}}\tau^{-(\ell-1)}$ for the points, from a recursive "good points" definition. A per-round union over the later rounds would give $(\ell - j)\tau$; the single potential $T_k$ of Lemma D6 gives exactly $\tau$ and $\varepsilon_\ast\sum_{j<\ell}\tau^{-j}$, with a two-line proof.
4. **The batching count.** Note 07's table has $(t + s + 1)/q$ at the query message; it is $(s_i + t_i)/q$ with $s_i$ the points of the level that just ended, not of the next one.
5. **Prover cost.** Note 07 expects a low single-digit percentage. The count is $2 s_0 2^\mu$ carry-less multiplications, as many as the level-0 NTT's multiplications at rate 1/2. Unmeasured either way.
6. **Extension fields.** Note 07 says "the only input from the code is $\Lambda$". True, but $\Lambda$ is a list size for words over extensions of $E$ of degree up to 32 (Remark D0). A list bound obtained by an argument specific to $K$-valued words would not suffice.
7. **The last level.** 14 to 7 queries with 15 points at $\mu = 30$ (note 07: 15 to 9, or 8), and at $\mu \equiv 0 \bmod 4$ the last two levels gain.
8. **Knowledge soundness.** Not examined in note 07. Section 2.7: the relativised lemma holds, and the extractor does not list-decode.

One structural observation for whoever continues: the nested factor $\tau^{-(\ell - 1)}$ is where most of the points go (595 of 1064 bits at level 0). It would vanish if one could prove that the exceptional sets $\mathrm{Exc}_j(O^{(j-1)})$ of the folds of one word are nested or correlated, for example $\mathbf{z} \in \mathrm{Exc}_j(O^{(j-1)})$ for a noticeable fraction of $c_{j-1}$ implies $\mathbf{z}$ is exceptional for a statement about $O^{(j-2)}$ itself. I did not find such a statement; it would cut level 0 from 12 points to 6 and the prover's point work in half.

## 7. Reproduction

- `python3 doc/whir_soundness_gap_notes/scripts/11_deep_fold_whir.py`: tables T0 to T7 (about one second). `... selftest`: the model's consistency checks.
- `python3 doc/whir_soundness_gap_notes/scripts/11_protocol_toy.py [seed]`: the toy run of Protocol D (completeness identities C1 to C5, tamper rejection C6; under a second).
- Both import nothing outside the standard library; the first imports `scripts/08_retuning/whir_model.py` and `costs.py`.
