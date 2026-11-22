# 14. DEEP-fold WHIR: the definitive statement

Researcher 14 (round 3). This note reconciles notes 10 and 11 into one protocol, gives the round-by-round theorem with every transition proved, treats knowledge soundness and the interface with the outer protocol, and reduces the hypothesis to single-lane words over $K$. Notation is Annex B's (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`): levels $i = 0, \dots, I-1$, variable counts $\nu_i$, fold factors $\ell_i$, $\kappa_i = \nu_{i+1}$, domains $D_i \subseteq K$ of size $n_i = 2^{\kappa_i + R_i}$, queries $t_i$, lanes $P^{(i,j)}$ with halves $F^{(i,j)}, G^{(i,j)}$, running claim $(W^{(i,j)}, \sigma^{(i,j)})$, high part $\mathbf{h}^{(i)}$, novel basis $\mathcal{X}_c$, normalized subspace polynomials $\widehat W_k$, $\mathcal{P}_g$ the polynomial with novel-basis coefficients $g$, $q = |E| = 2^{128}$. Statuses: **[proved]** (complete proof in this note, by hand, not machine-checked), **[checked]** (numerically, sizes given), **[conjectured]**, **[inherited]** (a statement of the existing formalization that I read and rely on without re-proving). No Lean or Rust was edited. Scripts: `scripts/14_params.py`, `scripts/14_interleave.c`, `scripts/14_extractor_toy.py`.

## 0. Summary

1. **One protocol** (section 1). Notes 10 and 11 describe the same protocol up to a handful of choices; section 1.1 decides each. The result is note 11's Protocol D with note 10's orderings made explicit and note 10's constants.
2. **One theorem** (Theorem D', section 4). Under $\mathrm{ListBound}_i(L_i)$ for every level, every verifier message of the stacked opening has the round-by-round error of the theorem card (section 8). Every transition is proved here; nothing is "as in Annex B" except the three items listed in section 4.5, each with the reason it applies verbatim. I found no error in notes 10 and 11. The differences from note 11's Theorem D are cosmetic: the constant $1/(K_0(K_0-1)(K_0-M))$ for $4/K_0^3$, $\epsilon_i = (d^{(i)} + 2^{\ell_i} - 1)/q$, and the level-0 message counted with the ring switch, $(J_0 + 1)/q$.
3. **Knowledge soundness holds, with the extractor of today's proof** (section 5). The fold lemma is proved in relativised form (Lemma F, clause (b)), and the induction through rounds and levels is written out (Theorem K). The extractor is the agreement-set descent: it starts from the final polynomial, and at each round going back decodes one tuple with at most one error on a known set. It never list-decodes, runs in time polynomial in the proof and the committed words, and on an accepted run that escaped no message it outputs exactly the tuple the commit-phase answers pin (Corollary K2). Nothing fails. **[proved]**, toy-checked.
4. **The interface is today's with one substitution** (section 6): "the candidate answering the OOD claim" becomes "the candidate answering the $s_0$ point claims". The outer phases, the ring switch, the bytecode claim and the recursion consume only "at most one $K$-valued candidate stack, fixed before the first outer challenge", which Protocol D provides. Section 6.5 lists every place in `formal/` and in the crates that uses the Johnson list size or the OOD point, with what replaces it.
5. **The hypothesis reduces to single-lane words over $K$** (section 7). Two reductions, both **[proved]**, neither needs the other:
   - *Tree bound (Theorem I, a sharpened Gopalan-Guruswami-Raghavendra bound).* If every single-lane word has at most $L$ members at agreement $A$ and degree $d$, every interleaved word (any lanes, any alphabet) has at most $N_{L,g}(n-d)$, $g = A - d$, where $N(\Phi) = 1$ for $\Phi < 2g$ and $N(\Phi) = N(\Phi - g) + (L-1)N(\lfloor\Phi/2\rfloor)$ otherwise. This is $L$ for $A > (n+2d)/3$, $2L - 1$ for $A > (n+3d)/4$, $L^2 + L - 1$ for $A > (n+4d)/5$, and at most $\sum_{k \le r}\binom{b}{k}(L-1)^k$ with $b = \lfloor (n-A)/(A-d)\rfloor$, $r = \lfloor\log_2((n-d)/(A-d))\rfloor$. No cap on $L$.
   - *Projection (Proposition R2', note 13's Proposition 3.4, verified and sharpened).* If every $K$-valued single-lane word has at most $L \le 2^{62}$ members, every word over any extension or lane count has at most $L/(1 - L/2^{64})$: no loss in the exponent, at every threshold.
   - Best of the two: single $K$-valued words suffice with at most a factor 2 whenever $L \le 2^{62}$ or $A > (n+3d)/4$ (rate 1/2: above $5n/8$). Outside both ranges the hypothesis should be stated for single $E$-valued words ($L \le 2^{126}$); from $K$-valued words alone the tree bound loses a power ($L^2$ to $L^4$).
   - At note 13's predicted lists every cell but two needs 11 or 12 points at level 0. The two cells with lists above $2^{62}$ (rate 1/2 at $9n/16$, rate 1/16 at $n/8$) need 14 and 13 points under a direct interleaved or $E$-valued hypothesis, 20 and 18 from $K$-valued words alone.
6. **Residual gaps** (section 9): the hypothesis itself; everything is on paper; the Fiat-Shamir compilation and the outer phases are inherited from the existing formalization, not re-derived; recursion across levels has the status it has today; the two proof losses ($q^3$ and $\tau^{-(\ell-1)}$) are probably artifacts but nothing better is proved.

## 1. Protocol D, unified

### 1.1 Where notes 10 and 11 differ, and the decision

| item | note 10 | note 11 | decision, and why |
| --- | --- | --- | --- |
| lane weights of a point | $\mathrm{eq}(r, u)$ with a division by $r_j$ (error or completeness term $s\ell/q$), or multilinear monomials $\prod_k r_k^{u_k}$, $r \in E^{\ell}$ | monomials $\theta^{e(u)}$ in one scalar, $e(u) = \sum_k (1 - u_k)2^{k-1}$ | note 11's. No division, no failure event, two sampled scalars a point instead of $\ell + 1$ (about 120 squeezes instead of about 300 at $\mu = 30$). The price is $2^\ell - 1$ instead of $\ell$ in the numerator of $\epsilon$: 63 against $2^{24}$ at level 0. |
| what the prover sends per point and round | $y^G$ (monomial variant) or $y^F$ (eq variant) | $\varphi = \mathrm{ev}(F)$, the first half's value | $\varphi$. With these weights the split is $\mathrm{ev}(U) = \theta^{2^{j-1}}\mathrm{ev}(F) + \mathrm{ev}(G)$, so the second half's value is derived and never sent. The prover does not send $y^G$. |
| all points of a level in one verifier message | required (correction 4) | implied by the figure | explicit: the $2 s_i$ scalars are squeezed with no prover message between them. With one message a point the exceptional event would cost $s/\epsilon$ instead of $\epsilon^{-s}$. |
| independence | lane coordinates independent per point | $(\theta_m, \zeta_m)$ i.i.d. | i.i.d. uniform in $E^2$, fresh per commitment. |
| points inside $D$ | optionally draw $\zeta \in E \setminus D$ | not excluded | not excluded, and no term is added. Schwartz-Zippel over uniform $\zeta \in E$ already covers the event (it is inside $\epsilon^s$, note 10 section 2.3), exclusion would not improve any proved bound, and it would add a rejection step to three verifiers. |
| each answer absorbed before its fold challenge | required (correction 4) | in the figure | explicit in step 1(a) to 1(b) below. |
| last level | must check the carried claims on the polynomial sent (correction 3) | present | present, step 3. |
| constant of the exceptional probability | $1/(K_0(K_0-1)(K_0-M))$, $M = \max(2q, \binom n2)$ | $4/K_0^3$ under $0.74K_0 \ge M$ | note 10's: integers only, and smaller. |
| $\epsilon$ | $(d + 1 + \ell)/q$ (multilinear weights) | $(d + 2^\ell)/q$ | $(d + 2^\ell - 1)/q$, which is what Lemma E gives for both uses. |
| reuse of points across rounds | recursive sets $\mathrm{Bad}_j$ (Proposition 8.1) | potential $T_k$ (Lemma D6) | the potential. Same numbers; it is one real-valued function of (commitment, points, challenges), the shape the formal `Spec` already has for its own potential. |
| batching count | $(t + s)/q$ | $(s_i + t_i)/q$, $s_i$ the points of the level that just ended | the same. At level 0 the message also carries the ring switch: $(J_0 + 1)/q$ in the stacked opening. |

### 1.2 Point evaluations

**Definition E.** A *point* is $z = (\theta, \zeta) \in E^2$. Fix a level with $\ell$ lane variables $u_1, \dots, u_\ell$, where round $j$ folds $u_j$. After $j$ rounds a tuple $U = (U_u)$ is indexed by $u = (u_{j+1}, \dots, u_\ell) \in \{0,1\}^{\ell-j}$, and
$$\mathrm{ev}^{(j)}_z(U) := \sum_u \theta^{e_j(u)}\,U_u(\zeta), \qquad e_j(u) := \sum_{k=j+1}^{\ell}(1 - u_k)\,2^{k-1}.$$
For $j = \ell$ this is $U(\zeta)$. Whole polynomials are evaluated, coefficients of index $2^\kappa$ and above included.

**Lemma E. [proved]** (E1) $\mathrm{ev}^{(j)}_z$ is $E$-linear in $U$. (E2) If $F = U_{(0,\cdot)}$, $G = U_{(1,\cdot)}$ are the halves of a tuple $U$ with lane variables $u_j, \dots, u_\ell$, then $\mathrm{ev}^{(j-1)}_z(U) = \theta^{2^{j-1}}\mathrm{ev}^{(j)}_z(F) + \mathrm{ev}^{(j)}_z(G)$. (E3) For $a \in E[X]$, $\mathrm{ev}^{(j)}_z(aU) = a(\zeta)\,\mathrm{ev}^{(j)}_z(U)$. (E4) If $U \ne 0$ has degree at most $\Delta$, then $\Pr_{z \leftarrow E^2}[\mathrm{ev}^{(j)}_z(U) = 0] \le (\Delta + 2^\ell - 2^j)/q$.

*Proof.* (E1), (E3): by definition. (E2): $e_{j-1}(0, u') = 2^{j-1} + e_j(u')$ and $e_{j-1}(1, u') = e_j(u')$. (E4): $\sum_u \theta^{e_j(u)}U_u(\zeta)$ is a polynomial in $(\theta, \zeta)$. The exponents $e_j(u)$ are pairwise distinct (binary digits), so it is nonzero when some $U_u$ is. Its total degree is at most $\max_u e_j(u) + \Delta = 2^\ell - 2^j + \Delta$. Schwartz-Zippel (`lem:sz`). $\square$

Both uses below have bound $\epsilon := (d + 2^\ell - 1)/q$: tuples of degree at most $d$ at $j = 0$, and of degree at most $d + 1$ at $j \ge 1$.

### 1.3 The protocol

Parameters: those of Protocol `fig:protocol`, a number of points $s_i \ge 1$ per level, and four grinds $b_{\mathrm{pt}}, b_{\mathrm{batch}}, b_{\mathrm{fold}}, b_{\mathrm{query}}$. "Squeeze" and "absorb" refer to the duplex sponge of `sec:e2e-fiat-shamir`: every scalar the prover sends is absorbed before the next squeeze, a grind nonce is absorbed by the permutation that produces the next challenge, and consecutive squeezes with nothing sent between them are one verifier message.

**Commit**$(f : \{0,1\}^\nu \to K)$.

- C1. $\mathbf P$ sends the Merkle root of $O^{(0)}$, as today ($O^{(0)}[u, \cdot] = \mathrm{Enc}_0(f(u, \cdot))$, lanes $P^{(0,0)}_u = \mathcal{P}_{f(u,\cdot)} \in K[X]$).
- C2. Grind $b_{\mathrm{pt}}$. $\mathbf V$ samples $z^{(0)}_m = (\theta^{(0)}_m, \zeta^{(0)}_m) \leftarrow E^2$ for $m = 1, \dots, s_0$: $2s_0$ squeezes, one message.
- C3. $\mathbf P$ sends $y^{(0)}_m \in E$, $m = 1, \dots, s_0$; honestly $y^{(0)}_m = \mathrm{ev}^{(0)}_{z^{(0)}_m}(P^{(0,0)})$. The pairs $(z^{(0)}_m, y^{(0)}_m)$ are the *point claims* of the commitment. There is no multilinear out-of-domain claim and the point claims are not among the weighted claims of the opening.

**Open**$(\{(W_k, c_k)\}_{k=1..J_0})$, $1 \le J_0 \le 512$ weighted claims (`def:tuple-claim`).

- O1. Grind $b_{\mathrm{batch}}$. $\mathbf V$ samples $\lambda_0 \leftarrow E$ (in the stacked opening: the sixteen ring-switching scalars, then $\lambda_0$, one message). Set $(W^{(0,0)}, \sigma^{(0,0)}) := (\sum_k \lambda_0^{k-1}W_k, \sum_k \lambda_0^{k-1}c_k)$ and $v^{(0,0)}_m := y^{(0)}_m$.

For $i = 0, \dots, I - 1$:

1. *(fold rounds)* For $j = 1, \dots, \ell_i$:
   - (a) $\mathbf P$ sends $v_G, v_F, \sigma_0, \sigma_1 \in E$ exactly as in Protocol `fig:protocol`, then $\varphi^{(i,j)}_m \in E$ for $m = 1, \dots, s_i$; honestly $\varphi^{(i,j)}_m = \mathrm{ev}^{(j)}_{z^{(i)}_m}(F^{(i,j)})$. All $4 + s_i$ scalars are absorbed.
   - (b) Grind $b_{\mathrm{fold}}$. $\mathbf V$ samples $\alpha_{i,j}, \beta_{i,j} \leftarrow E$.
   - (c) Both set $W^{(i,j)} := \widehat{W^{(i,j-1)}}(\alpha_{i,j}, \cdot)$, $\sigma^{(i,j)}$ by the formula of Protocol `fig:protocol`, and for every $m$
   $$v^{(i,j)}_m := v^{(i,j-1)}_m + \bigl((\theta^{(i)}_m)^{2^{j-1}} + \alpha_{i,j} + \beta_{i,j}\,\zeta^{(i)}_m\bigr)\,\varphi^{(i,j)}_m .$$
   $\mathbf P$ sets $P^{(i,j)} := G^{(i,j)} + (\alpha_{i,j} + \beta_{i,j}X)F^{(i,j)}$.
2. If $i < I - 1$:
   - (a) *(commit)* $\mathbf P$ sends the root of $O^{(i+1)}$, then $\mathbf{h}^{(i)} \in E^{\ell_i}$, as today.
   - (b) *(points)* Grind $b_{\mathrm{pt}}$. $\mathbf V$ samples $z^{(i+1)}_m \leftarrow E^2$, $m = 1, \dots, s_{i+1}$, one message. $\mathbf P$ sends $y^{(i+1)}_m \in E$, honestly $\mathrm{ev}^{(0)}_{z^{(i+1)}_m}(P^{(i+1,0)})$.
   - (c) *(query)* Grind $b_{\mathrm{query}}$. $\mathbf V$ samples $t_i$ i.i.d. $x_{i,q} \leftarrow D_i$ and $\lambda_{i+1} \leftarrow E$, one message.
   - (d) *(read)* $\mathbf V$ opens the columns $O^{(i)}[\cdot, x_{i,q}]$, folds each to $w^{(i)}(x_{i,q})$ and sets $c_{i,q} := w^{(i)}(x_{i,q}) + \widehat W_{\kappa_i}(x_{i,q})H^{(i)}(x_{i,q})$ with $H^{(i)} := \sum_{s<\ell_i}\mathbf{h}^{(i)}_s\mathcal{X}_s$, as today. It converts the level's point claims:
   $$c'_{i,m} := v^{(i,\ell_i)}_m + \widehat W_{\kappa_i}(\zeta^{(i)}_m)\,H^{(i)}(\zeta^{(i)}_m), \qquad m = 1, \dots, s_i .$$
   - (e) *(next level)* The $J_{i+1} := 1 + s_i + t_i$ claims (residual, converted points, queries) are batched with distinct powers:
   $$W^{(i+1,0)} := W^{(i,\ell_i)} + \sum_{m=1}^{s_i}\lambda_{i+1}^{m}W_{i,\zeta^{(i)}_m} + \sum_{q=1}^{t_i}\lambda_{i+1}^{s_i+q}W_{i,x_{i,q}}, \qquad \sigma^{(i+1,0)} := \sigma^{(i,\ell_i)} + \sum_{m=1}^{s_i}\lambda_{i+1}^{m}c'_{i,m} + \sum_{q=1}^{t_i}\lambda_{i+1}^{s_i+q}c_{i,q},$$
   with $W_{i,x}(u) := \prod_k\widehat W_k(x)^{u_k}$ on $\{0,1\}^{\kappa_i}$ for any $x \in E$ (`lem:colweight` at a point that need not be in the domain). The new carried values are $v^{(i+1,0)}_m := y^{(i+1)}_m$.
3. If $i = I - 1$: *(final)* $\mathbf P$ sends the $2^{\nu_I} + \ell_i$ novel-basis coefficients of $P := P^{(i,\ell_i)}$. $\mathbf V$ checks $P(\zeta^{(i)}_m) = v^{(i,\ell_i)}_m$ for every $m$. Grind $b_{\mathrm{query}}$; $\mathbf V$ samples $t_i$ queries, opens and folds the columns and checks $w^{(i)}(x_{i,q}) = P(x_{i,q})$. Then the $\nu_I$ sumcheck rounds and the terminal check of Protocol `fig:protocol`, unchanged, the terminal weight now containing the converted point claims' weights $\lambda^m\prod_k((1 + r_k) + r_k\widehat W_k(\zeta_m))$.

$\mathbf V$ accepts iff every check passed.

What is sampled: per commitment $2s_i$ scalars; per fold round $(\alpha, \beta)$; per level the queries and one $\lambda$. What the prover adds to today's stream: $s_i$ answers per commitment and $s_i$ scalars per fold round, in place of one OOD value per commitment. What the verifier adds: the update of step 1(c) (one squaring, two products per point and round), the conversions, $s_{I-1}$ evaluations of the final polynomial, and $O(\kappa)$ products per point at the terminal check.

### 1.4 Completeness

**[proved]**, and **[checked]** on a toy instance (`scripts/11_protocol_toy.py`, whose algebra is exactly the protocol above: 20 honest runs, 1900 identities; eight kinds of altered prover values rejected in 20 of 20 runs). Induction on $j$: if $v^{(i,j-1)}_m = \mathrm{ev}^{(j-1)}(P^{(i,j-1)})$ then by (E2) it equals $\theta^{2^{j-1}}\varphi + \mathrm{ev}^{(j)}(G)$, and by (E1), (E3) $\mathrm{ev}^{(j)}(P^{(i,j)}) = \mathrm{ev}^{(j)}(G) + (\alpha + \beta\zeta)\varphi = v^{(i,j-1)}_m + (\theta^{2^{j-1}} + \alpha + \beta\zeta)\varphi$ in characteristic two. At a level's end $P^{(i,\ell_i)} = \mathcal{P}_{f^{(i+1)}} + \widehat W_{\kappa_i}H^{(i)}$ as polynomials, so at $\zeta$, and $\mathcal{P}_g(\zeta) = \langle W_{i,\zeta}, g\rangle$ for every $\zeta \in E$ is Definition `def:enc` expanded. Completeness is perfect: no division, no rejection sampling.

## 2. Hypothesis, thresholds, standing assumptions

Thresholds and degree bound are Annex B's: $d^{(i)} := 2^{\kappa_i} - 1 + \ell_i$ and $A^{(i,j)} := A_i - (\ell_i - j)$ for one free integer $A_i \le n_i$ per level. $\mathrm{List}(O; A, d)$ is the set of polynomial tuples of degree at most $d$ agreeing with the interleaved word $O$ on at least $A$ columns (`def:interleaved`).

**Hypothesis $\mathrm{ListBound}_i(L_i)$.** For every $0 \le m \le \ell_i$ and every interleaved word $O : \{0,1\}^m \times D_i \to E$: $|\mathrm{List}(O; A^{(i,0)}, d^{(i)})| \le L_i$.

Lists at a larger agreement are subsets, so the same $L_i$ bounds every list the proof uses. Section 7 reduces this to single-lane words. Two instances are theorems: Johnson ($L_i = \mathrm{jl}(A^{(i,0)}, d^{(i)})$ when $(A^{(i,0)})^2 > n_id^{(i)}$, `thm:johnson-interleaved`) and counting ($L_i = \binom{n_i}{d+1}/\binom{A}{d+1}$ for $A \ge d + 1$, note 11 section 2.1).

**Standing assumptions**, all satisfied by every deployed ladder (`derive_config`: $\ell_0 = 6$, $\ell_i = 4$ after, $\kappa_{I-1} = \nu_I \in \{2, \dots, 5\}$, $n_i \le 2^{28}$):

- (S1) $1 \le \ell_i \le 2^{\kappa_i}$ (so that the high part $\widehat W_{\kappa_i}H^{(i)}$, $\deg H^{(i)} < \ell_i$, is the part of index $2^{\kappa_i}$ and above of a polynomial of degree at most $d^{(i)}$);
- (S2) $d^{(i)} + 2 \le A^{(i,0)}$ and $A_i \le n_i$;
- (S3) $\binom{n_i}{2} \le 2q$;
- (S4) $K_0$ is an integer with $K_0 > M := 2q$, and $0 < \tau < 1$.

## 3. Lemmas

Fix a level ($\ell$, $d$, $D$ of size $n$), a round $j \in \{1, \dots, \ell\}$, and an interleaved word $O$ with lane variables $u_j, \dots, u_\ell$, halves $O_0, O_1$ of $h = 2^{\ell-j}$ lanes. For $c = (\alpha, \beta) \in E^2$ put $a_c := \alpha + \beta X$ and $O_c := O_1 + a_cO_0$. Fix an integer $A \le n$ and let $\Lambda \ge \max_c|\mathrm{List}(O_c; A, d)|$. Let $\mathcal{T} := \{(c, P) : c \in E^2, P \in \mathrm{List}(O_c; A, d)\}$, a set that depends on $O$, $A$, $d$ only, with $|\mathcal T| \le \Lambda q^2$.

For a pair of rational $h$-tuples $(F, G)$ its *class* is $\mathcal{C}(F, G) := \{(c, P) \in \mathcal T : P = G + a_cF\}$; a class has at most one element per challenge. For three elements $(c_k, P_k)$ put $a_k := a_{c_k}$ and
$$Q := (a_2 + a_3)P_1 + (a_1 + a_3)P_2 + (a_1 + a_2)P_3,$$
a tuple of degree at most $d + 1$.

**Lemma L1 (linear space; note 10, Lemma 2.1; note 07, Lemma 1). [proved]**

- (a) Two elements of $\mathcal T$ with different challenges lie in exactly one class, that of $F = (P_1 + P_2)/(a_1 + a_2)$, $G = P_1 + a_1F$.
- (b) Three elements with pairwise different challenges lie in one class if and only if $Q = 0$.
- (c) If for a point $z$ and values $y^F, y^G \in E$ the three elements satisfy $\mathrm{ev}^{(j)}_z(P_k) = y^G + a_k(\zeta)y^F$, then $\mathrm{ev}^{(j)}_z(Q) = 0$.
- (d) Let $\mathcal W \subseteq \mathcal T$ have $K$ elements with pairwise different challenges, and suppose every class contains at most $M'$ elements of $\mathcal W$, $2 \le M'$. Then at least $K(K-1)(K - M')$ ordered triples of distinct elements of $\mathcal W$ are not in one class.

*Proof.* (a) $a_1 + a_2 \ne 0$ as $c_1 \ne c_2$, and $G + a_2F = P_1 + (a_1 + a_2)F = P_2$. If both lie in $\mathcal C(F', G')$ then $P_1 + P_2 = (a_1 + a_2)F'$, so $F' = F$, $G' = G$. (b) With $(F, G)$ the pair of the first two: $(a_2 + a_3)(G + a_1F) + (a_1 + a_3)(G + a_2F) = (a_1 + a_2)G + (a_1a_2 + a_1a_3 + a_1a_2 + a_2a_3)F = (a_1 + a_2)(G + a_3F)$. So $Q = (a_1 + a_2)(G + a_3F + P_3)$, which is zero exactly when $P_3 = G + a_3F$. (c) By (E1), (E3), $\mathrm{ev}_z(Q) = y^G\sum_kL_k(\zeta) + y^F\sum_kL_k(\zeta)a_k(\zeta)$ with $L_1 = a_2 + a_3$ and so on; $\sum_kL_k = 0$ and $\sum_kL_ka_k = 2(a_1a_2 + a_1a_3 + a_2a_3) = 0$ in characteristic two. (d) By (a) every ordered pair of $\mathcal W$ lies in exactly one class, which holds at most $M' - 2$ further elements of $\mathcal W$. So at most $K(K-1)(M'-2)$ ordered triples lie in one class, out of $K(K-1)(K-2)$. $\square$

**Lemma L2 (size of a class; note 10, Lemma 2.2; note 07, Lemma 2). [proved]** Let $\mathcal C = \mathcal C(F, G)$ have at least two elements.

- (a) If some component of $F$ is not a polynomial, all challenges of $\mathcal C$ lie on one line $\alpha + x_0\beta = \gamma$ of $E^2$: $|\mathcal C| \le q$.
- (b) If $F$ is a polynomial tuple of degree at least $d$, all challenges of $\mathcal C$ share $\beta$: $|\mathcal C| \le q$.
- (c) Otherwise $\deg F \le d - 1$ and $\deg G \le d$. Let $Z := \{x \in D : F(x) = O_0(x), G(x) = O_1(x)\}$. At most $\binom{n - |Z|}{2}$ elements $(c, P)$ of $\mathcal C$ have two or more agreement columns of $P$ with $O_c$ outside $Z$. Hence if $|Z| \le A - 2$ then $|\mathcal C| \le \binom{n}{2}$; and if $|Z| \ge A - 1$ then $U := (F, G) \in \mathrm{List}(O; A - 1, d)$, and all but at most $\binom n2$ elements $(c, P)$ of $\mathcal C$ have $U$ as a *near tuple*: $U$ agrees with $O$ on all but at most one column of the agreement set of $P$ with $O_c$.

*Proof.* For two elements, $P_c + P_{c'} = (a_c + a_{c'})F$ is a polynomial tuple of degree at most $d$, and $a_c + a_{c'} \ne 0$ has degree at most one. (a) Write the component in lowest terms with denominator $\Delta$, $\deg\Delta \ge 1$. Then $\Delta$ divides every $a_c + a_{c'}$, so $\Delta = X + x_0$ with $x_0 \in E$ and $a_c + a_{c'} = (\beta + \beta')(X + x_0)$, that is $\alpha + x_0\beta = \alpha' + x_0\beta'$. (b) $(a_c + a_{c'})F$ has degree at most $d$ only if $a_c + a_{c'}$ is constant. (c) The remaining case is a polynomial tuple $F$ of degree at most $d - 1$, and then $G = P_c + a_cF$ is a polynomial tuple of degree at most $d$. Let $(c, P) \in \mathcal C$ and $x \in D \setminus Z$ with $P(x) = O_c(x)$. Then $(G + O_1)(x) = a_c(x)\,(F + O_0)(x)$ in $E^h$. If $(F + O_0)(x) = 0$ then $(G + O_1)(x) = 0$ and $x \in Z$; so $(F + O_0)(x) \ne 0$ and the scalar $a_c(x) = \alpha + \beta x$ is determined by $F, G, O$ and $x$. Two such columns $x \ne x'$ determine $c$ (the system has determinant $x + x' \ne 0$), and $c$ determines the element. So each pair of columns outside $Z$ accounts for at most one element. If $|Z| \le A - 2$, every element has at least $A - |Z| \ge 2$ agreement columns outside $Z$. If $|Z| \ge A - 1$, $U$ has degree at most $d$ and agrees with $O$ on $Z$. $\square$

**Lemma F (the DEEP fold round, with its claims and a predicate; note 07 Theorem 3 and Corollary 4, note 10 Theorem A, note 11 Lemma D4). [proved]** Let $K_0 > M := \max(2q, \binom n2)$ be integers. For $\mathbf z = (z_1, \dots, z_s) \in (E^2)^s$ let $N(\mathbf z)$ be the number of ordered triples of elements of $\mathcal T$ with pairwise different challenges and $Q \ne 0$ such that $\mathrm{ev}^{(j)}_{z_m}(Q) = 0$ for all $m$, and
$$\mathrm{Exc}_j(O) := \{\mathbf z : N(\mathbf z) \ge K_0(K_0 - 1)(K_0 - M)\}.$$

- (1) For independent uniform points, $\Pr[\mathbf z \in \mathrm{Exc}_j(O)] \le \dfrac{\Lambda^3q^6\,\epsilon^s}{K_0(K_0-1)(K_0-M)}$, $\epsilon = (d + 2^\ell - 1)/q$.
- (2) Let $\mathbf z \notin \mathrm{Exc}_j(O)$. Let $(W, \sigma)$ be a weighted claim on tuples with lane variables $u_j, \dots, u_\ell$, let $v_1, \dots, v_s \in E$, and let $B$ be any predicate on such tuples. Suppose every $U \in \mathrm{List}(O; A - 1, d)$ with $B(U)$ and $\mathrm{ev}^{(j-1)}_{z_m}(U) = v_m$ for all $m$ has $\langle W, U\rangle \ne \sigma$. Then for every prover message $(v_G, v_F, \sigma_0, \sigma_1, \varphi_1, \dots, \varphi_s) \in E^{4+s}$, fewer than $K_0$ challenges $c = (\alpha, \beta)$ admit a $P \in \mathrm{List}(O_c; A, d)$ with
   - (p) $\mathrm{ev}^{(j)}_{z_m}(P) = v_m + (\theta_m^{2^{j-1}} + \alpha + \beta\zeta_m)\varphi_m$ for all $m$,
   - (w) $\langle\widehat W(\alpha, \cdot), P\rangle = v_G + \alpha(v_G + \sigma) + \alpha^2v_F + \beta\sigma_0 + \alpha\beta(\sigma_0 + \sigma_1)$,
   - (b) every near tuple of $P$ (a tuple of degree at most $d$ agreeing with $O$ on all but at most one column of the agreement set of $P$ with $O_c$) satisfies $B$.

For plain soundness take $B$ true, and (b) is void.

*Proof.* (1) $\mathcal T$ is fixed by $O$ before the points. For a fixed triple with $Q \ne 0$, $Q$ has degree at most $d + 1$ and lane variables $u_{j+1}, \dots, u_\ell$, so by (E4) and independence all $s$ evaluations vanish with probability at most $((d + 1 + 2^\ell - 2^j)/q)^s \le \epsilon^s$. So $\mathbb E[N] \le |\mathcal T|^3\epsilon^s \le \Lambda^3q^6\epsilon^s$, and Markov's inequality gives the claim.

(2) Put $y^F_m := \varphi_m$ and $y^G_m := v_m + \theta_m^{2^{j-1}}\varphi_m$, so (p) reads $\mathrm{ev}^{(j)}_{z_m}(P) = y^G_m + a_c(\zeta_m)y^F_m$. Suppose at least $K_0$ challenges are as stated and choose one $P_c$ for each: a set $\mathcal W \subseteq \mathcal T$ of $K \ge K_0$ elements with pairwise different challenges, each satisfying (p), (w), (b). We show every class contains at most $M$ elements of $\mathcal W$. Let $\mathcal C = \mathcal C(F, G)$ contain at least two.

- If $F$ is not a polynomial tuple, or has degree at least $d$: at most $q$ (L2(a), (b)).
- Otherwise $(F, G)$ is a polynomial pair of degrees $(d - 1, d)$. If $|Z| \le A - 2$: at most $\binom n2$ (L2(c)).
- Otherwise $U := (F, G) \in \mathrm{List}(O; A - 1, d)$. For each $m$ put $\delta^F_m := \mathrm{ev}^{(j)}_{z_m}(F) + y^F_m$ and $\delta^G_m := \mathrm{ev}^{(j)}_{z_m}(G) + y^G_m$. An element $(c, G + a_cF)$ of $\mathcal C \cap \mathcal W$ satisfies (p), which by (E1), (E3) reads $\delta^G_m + (\alpha + \beta\zeta_m)\delta^F_m = 0$.
  - If $(\delta^F_m, \delta^G_m) \ne (0, 0)$ for some $m$: no solution when $\delta^F_m = 0$, a line of $E^2$ otherwise. At most $q$.
  - If all $\delta$ vanish: by (E2), $\mathrm{ev}^{(j-1)}_{z_m}(U) = \theta_m^{2^{j-1}}y^F_m + y^G_m = v_m$ for all $m$, so $U$ satisfies the carried point claims. If $|\mathcal C \cap \mathcal W| \le \binom n2$ we are done. Otherwise by L2(c) some element of $\mathcal C \cap \mathcal W$ has $U$ as a near tuple, and (b) for that element gives $B(U)$. The hypothesis then gives $\sigma^\ast := \langle W, U\rangle \ne \sigma$. For every $c$, by linearity of $\langle W_\iota, \cdot\rangle$ and $\widehat W(\alpha, \cdot) = (1 + \alpha)W_0 + \alpha W_1$,
  $$\langle\widehat W(\alpha, \cdot), G + \alpha F + \beta XF\rangle = v^\ast_G + \alpha(v^\ast_G + \sigma^\ast) + \alpha^2v^\ast_F + \beta\sigma^\ast_0 + \alpha\beta(\sigma^\ast_0 + \sigma^\ast_1),$$
  with $v^\ast_G = \langle W_0, G\rangle$, $v^\ast_F = \langle W_0 + W_1, F\rangle$, $\sigma^\ast_\iota = \langle W_\iota, XF\rangle$ and $\sigma^\ast = \langle W_0, F\rangle + \langle W_1, G\rangle$ (expand; the coefficient of $\alpha$ is $\langle W_0, G\rangle + \langle W_1, G\rangle + \langle W_0, F\rangle$). The difference of this and the right side of (w) is a polynomial of total degree at most two in $(\alpha, \beta)$ with constant term $\delta_G := v^\ast_G + v_G$ and coefficient of $\alpha$ equal to $\delta_G + \sigma^\ast + \sigma$; they do not both vanish. So it is nonzero and has at most $2q$ zeros (`lem:sz`), and (w) holds for at most $2q$ elements of $\mathcal C$.

So every class holds at most $M = \max(2q, \binom n2)$ elements of $\mathcal W$. By L1(d) at least $K(K-1)(K-M) \ge K_0(K_0-1)(K_0-M)$ ordered triples of $\mathcal W$ are not in one class (the function is increasing for $K \ge K_0 > M$). By L1(b) each has $Q \ne 0$ and by L1(c) each has $\mathrm{ev}^{(j)}_{z_m}(Q) = 0$ for all $m$. So $N(\mathbf z) \ge K_0(K_0-1)(K_0-M)$, contradicting $\mathbf z \notin \mathrm{Exc}_j(O)$. $\square$

Remarks. The only input from the code is $\Lambda$. The weight $W$ enters only through the linear functionals $\langle W_\iota, \cdot\rangle$; that they see only low parts is not used here. $K_0 > 2q$ is necessary for any statement of this kind (note 10, section 2.3: one list member with a false claim wins exactly $2q$ challenges). **[checked]** by note 10's exhaustive runs at $q = 64, 128, 256$, one and two lanes per half, with $\mathrm{eq}$ lane weights; the monomial weights change only (E2) and (E4).

**Lemma P (pinning; note 11 Lemma D5). [proved]** Let $O$ have $\ell$ lane variables and $|\mathrm{List}(O; A, d)| \le L$. For independent uniform points, except with probability at most $\binom L2\epsilon^s$, any two distinct members $U \ne U'$ have $\mathrm{ev}^{(0)}_{z_m}(U) \ne \mathrm{ev}^{(0)}_{z_m}(U')$ for some $m$. Such points are called *separating* for $O$; then for every answer vector at most one member is consistent with all answers. *Proof.* (E4) for $U + U' \ne 0$ of degree at most $d$, independence, a union over pairs. $\square$

**Lemma T (potential for points reused across the rounds of a level; note 11 Lemma D6). [proved]** Fix a level with committed word $O$, write $O^{(k)}$ for $O$ folded by $c_1, \dots, c_k$, and let $\varepsilon_\ast$ bound $\Pr_{\mathbf z}[\mathbf z \in \mathrm{Exc}_j(O')]$ for every $j$ and every word $O'$ of the shape of round $j$. For $0 \le k < j \le \ell$ let
$$\pi^{(k)}_j(\mathbf z; c_1..c_k) := \Pr_{c_{k+1}, \dots, c_{j-1}}\bigl[\mathbf z \in \mathrm{Exc}_j(O^{(j-1)})\bigr], \qquad T_k := \sum_{j=k+1}^{\ell}\tau^{-(j-k-1)}\,\pi^{(k)}_j ,$$
so $\pi^{(j-1)}_j \in \{0, 1\}$ and $T_\ell = 0$. Then (a) $\Pr_{\mathbf z}[T_0 \ge 1] \le \varepsilon_\ast\sum_{j=0}^{\ell-1}\tau^{-j}$; (b) if $T_{k-1} < 1$ then $\mathbf z \notin \mathrm{Exc}_k(O^{(k-1)})$ and $\Pr_{c_k}[T_k \ge 1] < \tau$.

*Proof.* The folds of $O$ are functions of $O$ and the challenges; no prover message enters. (a) $\mathbb E_{\mathbf z}[\pi^{(0)}_j] = \mathbb E_{c}\Pr_{\mathbf z}[\mathbf z \in \mathrm{Exc}_j(O^{(j-1)})] \le \varepsilon_\ast$ by exchanging the two averages (for each fixed $c_1..c_{j-1}$ the word is fixed and $\mathbf z$ is uniform). Sum and apply Markov. (b) The term $j = k$ of $T_{k-1}$ is $\pi^{(k-1)}_k \in \{0,1\}$ with coefficient one, so it is zero. And $\mathbb E_{c_k}[\pi^{(k)}_j] = \pi^{(k-1)}_j$ for $j > k$, so $\mathbb E_{c_k}[T_k] = \tau\sum_{j>k}\tau^{-(j-k)}\pi^{(k-1)}_j = \tau\,(T_{k-1} - \pi^{(k-1)}_k) < \tau$; Markov. $\square$

For $\ell = 1$ there is no $\tau$ at all: $T_0 = \pi^{(0)}_1 \in \{0,1\}$. Note 10's recursive sets $\mathrm{Bad}_j$ give the same two numbers; either can serve as the state.

## 4. Round-by-round soundness

### 4.1 Statement

Let $\epsilon_i := (d^{(i)} + 2^{\ell_i} - 1)/q$.

**Theorem D' (RBR soundness of Protocol D, whole stacked opening). [proved]** Assume (S1) to (S4) and $\mathrm{ListBound}_i(L_i)$ for every level. Call the input claims (the weighted claims $(W_k, c_k)_k$ and the commitment's point claims $(z^{(0)}_m, y^{(0)}_m)_m$) *false* if no $U \in \mathrm{List}(O^{(0)}; A^{(0,0)}, d^{(0)})$ has $\mathrm{ev}^{(0)}_{z^{(0)}_m}(U) = y^{(0)}_m$ for all $m$ and $\langle W_k, g_U\rangle = c_k$ for all $k$. Then the verifier messages have round-by-round errors:

| # | verifier message | error |
| --- | --- | --- |
| M0 | points $z^{(i)}$ after commitment $i$ ($i = 0$: at commit time) | $\varepsilon^{\mathrm{pt}}_i = \Bigl[\binom{L_i}{2} + \dfrac{L_i^3q^6}{K_0(K_0-1)(K_0-2q)}\sum_{j=0}^{\ell_i-1}\tau^{-j}\Bigr]\epsilon_i^{s_i}$ |
| M1 | batching $\lambda_0$ | $(J_0 - 1)/q$; with the sixteen ring-switching scalars in the same message, $(J_0 + 1)/q$ (section 6.3) |
| M2 | fold $(\alpha_{i,j}, \beta_{i,j})$ | $(K_0 - 1)/q^2 + \tau$ for $j < \ell_i$; $(K_0 - 1)/q^2$ for $j = \ell_i$ |
| M3 | queries of level $i < I - 1$ with $\lambda_{i+1}$ | $\bigl((A_i - 1)/n_i\bigr)^{t_i} + (s_i + t_i)/q$ |
| M4 | queries of the last level | $\bigl((A_{I-1} - 1)/n_{I-1}\bigr)^{t_{I-1}}$ |
| M5 | each of the $\nu_I$ tail rounds | $2/q$ |

The Johnson hypothesis and $\varepsilon_{\mathrm{aff}}$ of `thm:rbr` do not appear, and no list size multiplies a term of order $1/q$.

### 4.2 The state function

A tuple $U$ *satisfies* a weighted claim $(W, \sigma)$ if $\langle W, U\rangle = \sigma$ (a property of its low part $g_U$) and a point claim $(z, v)$ at round $j$ if $\mathrm{ev}^{(j)}_z(U) = v$ (a property of the whole tuple). Let $O^{(i,j)}$ be the level-$i$ word folded by its first $j$ challenges, $\mathrm{List}^{(i,j)} := \mathrm{List}(O^{(i,j)}; A^{(i,j)}, d^{(i)})$, of size at most $L_i$. Let $T^{(i)}_k$ be the potential of Lemma T for level $i$, with $\mathrm{Exc}_j$ taken at $A = A^{(i,j)}$, $d = d^{(i)}$, $\Lambda = L_i$, the theorem's $K_0$ and $M = 2q$ (which is $\max(2q, \binom{n_i}{2})$ by (S3)). The points $z^{(i)}$ are *good* for $O^{(i)}$ if they are separating for $O^{(i)}$ at $(A^{(i,0)}, d^{(i)})$ and $T^{(i)}_0 < 1$.

The invariant: some check of $\mathbf V$ has already failed, or the condition attached to the last verifier message holds.

- After the points $z^{(0)}$ (and through the outer protocol up to the opening): $z^{(0)}$ is good for $O^{(0)}$. At the start of the opening, in addition: the input claims are false.
- After $\lambda_i$ ($j = 0$; for $i \ge 1$ this is the query message of level $i - 1$) and after the fold challenge of round $j \ge 1$:
  - $(\mathrm I_{i,j})$: no $U \in \mathrm{List}^{(i,j)}$ satisfies the running claim $(W^{(i,j)}, \sigma^{(i,j)})$ and all point claims $(z^{(i)}_m, v^{(i,j)}_m)_m$ at round $j$;
  - $(\mathrm G_{i,j})$: $T^{(i)}_j < 1$.
- After the points $z^{(i+1)}$: $(\mathrm I_{i,\ell_i})$ holds and $z^{(i+1)}$ is good for $O^{(i+1)}$.
- After the last query message: $f^{(I)}$ (the low part of the polynomial sent) does not satisfy the running claim.
- After each tail round: the running sumcheck claim is false.

Properties (i), (ii), (iv) of Definition `def:rbr`. (i): the start is the definition of false input claims together with goodness, whose failure is charged to M0. (ii): every condition is a function of the transcript up to the last verifier message only. Goodness and $T^{(i)}_j$ depend on the commitment, the points and the challenges. $(\mathrm I_{i,j})$ depends in addition on $\sigma^{(i,j)}$ and $v^{(i,j)}_m$, which are functions of the prover's round message sent before the challenge. The conditions after a point message do not involve the answers. So no prover message breaks the invariant. (iv): at the end either a check failed or the last sumcheck claim is false, and $\mathbf V$, who holds $f^{(I)}$, evaluates it and rejects.

### 4.3 The transitions (property (iii))

**M0, points $z^{(i)}$.** $O^{(i)}$ is committed before the points (step C1 or 2(a) precedes C2 or 2(b)). By Lemma P the points are separating except with probability $\binom{L_i}{2}\epsilon_i^{s_i}$. By Lemma F(1) with $\Lambda = L_i$ (valid for every round and every folded word by $\mathrm{ListBound}_i$), $\varepsilon_\ast := L_i^3q^6\epsilon_i^{s_i}/(K_0(K_0-1)(K_0-2q))$ is as Lemma T requires, so $T^{(i)}_0 \ge 1$ with probability at most $\varepsilon_\ast\sum_{j<\ell_i}\tau^{-j}$. For $i \ge 1$ the condition $(\mathrm I_{i-1,\ell_{i-1}})$ does not involve the new points and stays. Total $\varepsilon^{\mathrm{pt}}_i$.

**M1, batching $\lambda_0$.** The points are separating, so at most one $U^\ast \in \mathrm{List}^{(0,0)}$ satisfies all point claims $(z^{(0)}_m, y^{(0)}_m)$. If there is none, $(\mathrm I_{0,0})$ holds for every $\lambda_0$. Otherwise the input claims are false, so $U^\ast$ violates some weighted claim, and $\sum_k\lambda_0^{k-1}(\langle W_k, U^\ast\rangle - c_k)$ is a nonzero polynomial of degree at most $J_0 - 1$ in $\lambda_0$: it vanishes with probability at most $(J_0 - 1)/q$. Every other list member violates a point claim, which is not batched, so there is no union over the list. $(\mathrm G_{0,0})$ is the goodness of $z^{(0)}$, which $\lambda_0$ does not touch.

**M2, fold challenge $(\alpha_{i,j}, \beta_{i,j})$.** Before it $(\mathrm I_{i,j-1})$ and $(\mathrm G_{i,j-1})$ hold and the prover has sent its $4 + s_i$ scalars. By Lemma T(b), $z^{(i)} \notin \mathrm{Exc}_j(O^{(i,j-1)})$. Apply Lemma F(2) with $O = O^{(i,j-1)}$, $A = A^{(i,j)}$, $(W, \sigma) = (W^{(i,j-1)}, \sigma^{(i,j-1)})$, $v_m = v^{(i,j-1)}_m$ and $B$ true. Its hypothesis is $(\mathrm I_{i,j-1})$ because $A - 1 = A^{(i,j-1)}$. Its conclusion is about $P \in \mathrm{List}(O_c; A^{(i,j)}, d^{(i)}) = \mathrm{List}^{(i,j)}$ with (p), which says $P$ satisfies the point claims $(z^{(i)}_m, v^{(i,j)}_m)$ of step 1(c), and (w), which says $P$ satisfies $(W^{(i,j)}, \sigma^{(i,j)})$. So $(\mathrm I_{i,j})$ fails for fewer than $K_0$ of the $q^2$ challenges. By Lemma T(b), $(\mathrm G_{i,j})$ fails with probability less than $\tau$, and never for $j = \ell_i$ ($T_{\ell_i} = 0$).

**M3, query message of level $i < I - 1$.** Before it the prover has committed $O^{(i+1)}$, sent $\mathbf h^{(i)}$, received $z^{(i+1)}$ and sent $y^{(i+1)}$; $(\mathrm I_{i,\ell_i})$ holds and $z^{(i+1)}$ is good. By separation at most one $U^\ast \in \mathrm{List}^{(i+1,0)}$ satisfies all new point claims, and it is fixed before the queries. If there is none, $(\mathrm I_{i+1,0})$ holds. Otherwise let $g^\ast := g_{U^\ast}$ and $P^\ast := \mathcal P_{g^\ast} + \widehat W_{\kappa_i}H^{(i)}$, a polynomial of degree at most $d^{(i)}$ by (S1), fixed before the queries.

- Case 1: $P^\ast$ agrees with $w^{(i)} = O^{(i,\ell_i)}$ on at least $A_i = A^{(i,\ell_i)}$ columns. Then $P^\ast \in \mathrm{List}^{(i,\ell_i)}$, and by $(\mathrm I_{i,\ell_i})$ either $P^\ast$ violates the running claim, and then $g^\ast$ violates the residual claim (a weighted claim sees only the low part, which is $g^\ast$); or $P^\ast(\zeta^{(i)}_m) \ne v^{(i,\ell_i)}_m$ for some $m$ (the point claim at round $\ell_i$ is plain evaluation), and then $\langle W_{i,\zeta_m}, g^\ast\rangle = \mathcal P_{g^\ast}(\zeta_m) = P^\ast(\zeta_m) + \widehat W_{\kappa_i}(\zeta_m)H^{(i)}(\zeta_m) \ne c'_{i,m}$: $g^\ast$ violates a converted point claim.
- Case 2: otherwise all $t_i$ independent uniform queries land on agreement columns with probability at most $((A_i - 1)/n_i)^{t_i}$. If some query has $P^\ast(x) \ne w^{(i)}(x)$, adding $\widehat W_{\kappa_i}(x)H^{(i)}(x)$ to both sides gives $\langle W_{i,x}, g^\ast\rangle = \mathcal P_{g^\ast}(x) \ne c_{i,q}$: $g^\ast$ violates a query claim.

So except with that probability $U^\ast$ violates one of the $J_{i+1}$ claims of step 2(e), which are fixed by the queries; $\lambda_{i+1}$ is uniform and independent of them, the claims carry the distinct powers $0, \dots, s_i + t_i$, and the batch stays violated except with probability $(s_i + t_i)/q$. Every other member of $\mathrm{List}^{(i+1,0)}$ violates a new point claim. This is $(\mathrm I_{i+1,0})$ with $v^{(i+1,0)} = y^{(i+1)}$. $(\mathrm G_{i+1,0})$ is the goodness of $z^{(i+1)}$.

**M4, last query message.** The prover has sent $P := P^{(I-1,\ell)}$, of degree at most $d^{(I-1)}$ by its coefficient count, with low part $f^{(I)}$. If $P$ agrees with $w^{(I-1)}$ on at least $A_{I-1}$ columns, then $P \in \mathrm{List}^{(I-1,\ell)}$ and by $(\mathrm I_{I-1,\ell})$ either $P(\zeta_m) \ne v_m$ for some $m$, and the point check of step 3 has failed, or $P$, hence $f^{(I)}$, violates the running claim. Otherwise some query has $P(x) \ne w^{(I-1)}(x)$ except with probability $((A_{I-1} - 1)/n_{I-1})^{t_{I-1}}$, and the query check fails.

**M5, tail round.** A degree-two sumcheck round from a false claim leaves a false claim except with probability $2/q$ (Fact `fact:sumcheck`). $\square$

### 4.4 Boundary cases

- **First round of a level** ($j = 1$). The word has all $2^{\ell}$ lanes, Lemma F is applied with halves of $2^{\ell-1}$ lanes, the lists of the folds are bounded by $\mathrm{ListBound}_i$ at $m = \ell - 1$, and the list $\mathrm{List}(O; A^{(i,1)} - 1, d)$ of the lemma is $\mathrm{List}^{(i,0)}$, the list Lemma P pins. The carried values are the answers themselves.
- **Last round of a level** ($j = \ell_i$). The fold is one lane, $\mathrm{ev}^{(\ell)}$ is evaluation at $\zeta$, and there is no $\tau$.
- **A level with one fold** ($\ell_i = 1$): both of the above at once; the point error has no nested factor. Levels with fewer than four folds do not occur on the deployed ladder (`derive_config` gives 6, then 4s), but the theorem covers every $\ell_i \ge 1$.
- **Degree slack.** All lists of level $i$ are at the one degree $d^{(i)}$. Lemma L2 returns halves of degrees $(d - 1, d)$ from folds of degree $d$, so nothing grows going back. The point claims evaluate whole polynomials, so they pin the slack coefficients too; the honest tuple has none at level entry.
- **Agreement loss.** One column per round, in Lemma L2(c) and nowhere else. It cannot be removed by this argument: forcing $|Z| \ge A$ needs classes larger than $nq$, an error of order $n/q$.
- **High-part correction.** Used twice in M3: $P^\ast$ has degree at most $d^{(i)}$ (needs (S1)), and the same correction term converts a query value and a point value into claims on the low part. $\mathbf h^{(i)}$ is sent before the points and the queries, so $P^\ast$ is fixed before the queries.
- **Level 0 is $K$-valued and committed before any outer claim exists.** Members of $\mathrm{List}^{(0,0)}$ are tuples over $E$ agreeing with $K$-valued lanes on at least $A^{(0,0)} \ge d + 1$ columns of $D_0 \subseteq K$, hence over $K$ (Lagrange interpolation on $d + 1$ of those columns has nodes and values in $K$). The points and the answers are in $E$. Goodness of $z^{(0)}$ is a property of $(O^{(0)}, z^{(0)})$ and survives every outer message. The folds $O^{(0,j)}$, $j \ge 1$, are $E$-valued, which is why $\mathrm{ListBound}_0$ is needed for $E$-valued lanes.
- **Final level.** The point check of step 3 is necessary: without it a polynomial of the last list that satisfies the running claim and violates a point claim would be accepted.
- **A single level** ($I = 1$): M3 does not occur; M0 (for $i = 0$), M1, M2, M4, M5 apply as written.
- **Points in $D$, or equal points, or $\theta = 0$.** Nothing special: all are inside the Schwartz-Zippel counts, and completeness does not need the points to avoid anything.

### 4.5 What is taken from Annex B unchanged, and why it applies verbatim

1. *The formula for $\sigma^{(i,j)}$ and its completeness.* The fold, the four scalars and the update are unchanged. Soundness of the update is not taken from `lem:fold-list`; it is re-proved inside Lemma F (the expansion of $\langle\widehat W(\alpha, \cdot), G + a_cF\rangle$).
2. *The tail sumcheck and the terminal check.* After M4 the state is "the low part of a polynomial the verifier holds violates one weighted claim", which is the state of `thm:rbr` at the same place; the weight is a different sum of tensors but the sumcheck argument does not look at the weight.
3. *Queries and Merkle openings.* The queries are i.i.d. uniform in $D_i$ (`sample_queries`), and the verifier's folded column value is a function of the committed word and the challenges, as today.

Everything else (pinning in place of OOD separation, the batching without a list factor, the fold round, the converted claims, the final check) is proved above.

## 5. Knowledge soundness

### 5.1 The relativised invariant

Today's formal proof (`Sound/Spec.lean`, `Descent.lean`) does not prove soundness and extraction separately. It proves one statement relative to a predicate: "every *bad* candidate violates the claims" is preserved by every verifier message, and an accepting run that preserved it has a *good trace*, from which a descent reads a candidate that is not bad. With bad := "does not satisfy the relation", the starting condition is a tautology and the descent's output is a witness. The same structure works for Protocol D.

**Definitions.** For a level, a round $j \ge 1$, the word $Q := O^{(i,j-1)}$, the challenge $c$ of round $j$ and a predicate $B$ on tuples of round $j - 1$, the *pull-back* (`pullT`) is the predicate on tuples $P$ of round $j$
$$(\mathrm{pull}\,B)(P) :\iff \Bigl[\,|\mathrm{agr}(P, Q_c)| \ge A^{(i,j)} \implies \text{every near tuple of } Q \text{ on } \mathrm{agr}(P, Q_c) \text{ satisfies } B\,\Bigr],$$
where $\mathrm{agr}$ is the set of agreement columns and a near tuple of $Q$ on $S$ is a tuple of degree at most $d^{(i)}$ agreeing with $Q$ on all but at most one column of $S$ (`NearT`). Given a predicate $\mathrm{Bad}$ on level-0 tuples, define $B_{0,0} := \mathrm{Bad}$, $B_{i,j} := \mathrm{pull}\,B_{i,j-1}$ along the challenge of round $j$, and across levels $B_{i+1,0}(U) :\iff B_{i,\ell_i}(P^\ast_U)$ with $P^\ast_U := \mathcal P_{g_U} + \widehat W_{\kappa_i}H^{(i)}$ (`nextPred`). Each $B_{i,j}$ is a function of the transcript up to the last message it mentions.

The relativised conditions $(\mathrm I^B_{i,j})$: no $U \in \mathrm{List}^{(i,j)}$ *with $B_{i,j}(U)$* satisfies the running claim and all point claims. $(\mathrm G_{i,j})$ and goodness are unchanged.

**Theorem K (round-by-round knowledge soundness). [proved]** Assume the hypotheses of Theorem D' and $d^{(i)} + 3 \le A^{(i,1)}$ (which is (S2)). Let $\mathrm{Bad}$ be a predicate on level-0 tuples fixed before the opening, such that every $U \in \mathrm{List}^{(0,0)}$ with $\mathrm{Bad}(U)$ that satisfies the commitment's point claims violates one of the input claims. Then every verifier message preserves the relativised invariant except with the error of Theorem D' for that message, and on every accepting run that preserved it the final polynomial $P$ lies in $\mathrm{List}^{(I-1,\ell)}$ and does not satisfy $B_{I-1,\ell}$. From such a $P$ the descent of section 5.2 computes a tuple $U_0 \in \mathrm{List}(O^{(0)}; A^{(0,0)}, d^{(0)})$ with $\neg\mathrm{Bad}(U_0)$.

*Proof.* The transitions of section 4.3 with these changes.

- M0: unchanged (goodness does not involve $B$).
- M1: at most one $U^\ast$ satisfies the point claims. If $\neg\mathrm{Bad}(U^\ast)$ or there is none, $(\mathrm I^B_{0,0})$ holds. Otherwise $U^\ast$ violates an input claim by hypothesis; same count.
- M2: Lemma F(2) with $B := B_{i,j-1}$. Its hypothesis is $(\mathrm I^B_{i,j-1})$. Its clause (b) for a $P \in \mathrm{List}^{(i,j)}$ is exactly $B_{i,j}(P)$, because the premise of the pull-back holds for a list member. So fewer than $K_0$ challenges break $(\mathrm I^B_{i,j})$.
- M3: let $U^\ast$ be the member of $\mathrm{List}^{(i+1,0)}$ satisfying the new point claims. If $\neg B_{i+1,0}(U^\ast)$, $(\mathrm I^B_{i+1,0})$ holds. Otherwise $B_{i,\ell_i}(P^\ast)$, and the two cases apply with $(\mathrm I^B_{i,\ell_i})$ in Case 1. Same counts.
- M4: if $P \notin \mathrm{List}^{(I-1,\ell)}$ a query fails except with the stated probability. If $P$ is in the list and $B_{I-1,\ell}(P)$, then by $(\mathrm I^B_{I-1,\ell})$ the point check fails or $f^{(I)}$ violates the running claim, and the tail rejects except with M5's errors. So an accepting run that escaped no message has $P \in \mathrm{List}^{(I-1,\ell)}$ and $\neg B_{I-1,\ell}(P)$.

*Descent.* $\neg(\mathrm{pull}\,B)(P)$ says: $P$ agrees with the folded word on at least $A^{(i,j)}$ columns, and some near tuple $T$ of the unfolded word on that agreement set has $\neg B(T)$. Such a $T$ has degree at most $d$ and agrees with the unfolded word on at least $A^{(i,j)} - 1 = A^{(i,j-1)}$ columns, so $T \in \mathrm{List}^{(i,j-1)}$. The near tuple on a set of at least $d + 3$ columns is unique (two of them agree on all but two columns of the set, at least $d + 1$; `nearT_unique`), so it is *the* near tuple, and it fails $B$. Going back through the rounds of the last level gives $T \in \mathrm{List}^{(I-1,0)}$ with $\neg B_{I-1,0}(T)$, that is $\neg B_{I-2,\ell}(P^\ast_T)$, which again contains "$P^\ast_T$ is in the list of the previous level", and so on down to level 0. $\square$

### 5.2 The extractor

Input: the accepted transcript (challenges, high parts, final polynomial) and the committed words $O^{(i)}$, which the existing extractor reads off the adversary's hash queries (`Extraction.committedWord`; unchanged). Algorithm (`descendTrace`, unchanged):

1. $T \leftarrow$ the final polynomial.
2. For $i = I - 1$ down to $0$: for $j = \ell_i$ down to $1$: compute $S := \mathrm{agr}(T, O^{(i,j)})$; if $|S| < A^{(i,j)}$ fail; set $T \leftarrow$ the near tuple of $O^{(i,j-1)}$ on $S$, by decoding at most one error on the known set $S$ (`NearDecoder`, `NewtonDecoder.lean`); if none exists fail. Then, if $i > 0$, $T \leftarrow \mathcal P_{g_T} + \widehat W_{\kappa_{i-1}}H^{(i-1)}$.
3. Output the stack whose blocks are the low parts of the lanes of $T$ (`tupleStack`).

- **It never list-decodes.** Every step is unique decoding of one tuple with at most one error on a set it knows. Beyond the Johnson radius no efficient list decoder for these codes is known, and the lists may have $2^{100}$ members; the extractor needs neither. It does not find the candidate from the commitment; it is led to it by the final polynomial, which the accepting prover sent in the clear.
- **Running time.** $\sum_i\ell_i$ decodings, each on a word of $n_i$ columns and at most $2^{\ell_i}$ lanes: polynomial in the size of the committed words (quasi-linear with a fast decoder), independent of every list size. Deterministic and straight-line: no rewinding.
- **What it outputs when the committed word has many close codewords.** One list member: the one the run was played for. It does not see the others. **[checked]** on a toy level (`scripts/14_extractor_toy.py`: $\mathrm{GF}(2^{16})$, $n = 64$, 8 lanes, $d = 18$, three rounds; 6 seeds each): a word with two list members, run honestly for either one, descends to that one (X3); with 31 corrupted columns the descent returns the tuple at every round (X1); with one column whose error a fold challenge cancels, the agreement set contains a column where the tuple is wrong and the one-error decoding still returns it (X2); with two such columns no near tuple exists and the extractor fails (X4), which is the event of probability at most $\binom n2/q^2$ counted inside the fold error; the near tuple was unique in every case (X5).

**Corollary K2 (the extractor returns the pinned candidate). [proved]** Suppose $z^{(0)}$ is good and let $U^\ast$ be the member of $\mathrm{List}^{(0,0)}$ consistent with the commit-phase answers, if there is one. For every opening of every set of input claims, except with the errors of Theorem D': if the run accepts, then $U^\ast$ exists, $g_{U^\ast}$ satisfies every input claim, and the descent outputs $U^\ast$. *Proof.* Theorem K with $\mathrm{Bad}(U) :\iff U \ne U^\ast$ or $g_U$ violates an input claim (everything is bad if there is no $U^\ast$). A bad list member satisfying the point claims is $U^\ast$ by separation, so it violates an input claim: the hypothesis holds. The descent's output is not bad. $\square$

So the commitment is binding in the strong sense the outer protocol needs: the candidate is fixed once the prover has answered the commit-phase points, before any opening claim exists, and every later opening is about that candidate.

### 5.3 What could have failed, and does not

- *Extraction from the commitment alone.* Impossible to do efficiently beyond Johnson, and not needed: neither today's proof nor the outer protocol extracts before the run ends (`extractAS` acts on accepted proofs).
- *A fold round whose conclusion is only about claims, with no correlated agreement.* Today the near pair comes from the affine MCA theorem. Here Lemma F gives it for the tuples that matter: the pair $U$ explaining a large class is a near tuple of all but $\binom n2$ of its members, which is what clause (b) needs. A list member of a fold that has no near tuple at all satisfies the pull-back vacuously, so it counts as bad, and the lemma bounds the challenges for which such a member satisfies the claims.
- *A threshold too small for unique near tuples.* $A^{(i,j)} \ge d + 3$ for $j \ge 1$ is (S2).

**Verdict: round-by-round knowledge soundness holds for Protocol D with the errors of Theorem D', the extractor is today's, and it is efficient at any threshold.**

## 6. The interface with the outer protocol

### 6.1 What the outer protocol consumes

I read the statements of the existing formalization that sit at the interface (`EndToEnd/Candidates.lean`, `Front/CommitDoom.lean`, `Front/OodBind.lean`, `Front/RingSwitch.lean`, `Whir/Sound/Spec.lean` `stackedSpec`, `Sound/AgreementExtractor.lean`). **[inherited]** for their content; the substitutions below are **[proved]** by sections 4 and 5 at the level of the statements, not re-run through the Lean.

Today: (1) after the root, the doom is `CommitDoom`: no candidate stack of the committed word (a $K$-valued stack whose encoding, with free high parts of degree below 6, agrees with the word on at least $A^{(0,0)}$ columns) satisfies the relation. (2) `readOod` charges $\binom{L}{2}\mu/|E|$ and leaves the candidates separated at $z_0$, so that after the answer at most one candidate (`oodCands`) answers the OOD claim. (3) Every front phase (bus, table sumcheck, public input, Keccak, ring switch) is a statement about a set $S$ of candidates and is charged per candidate; the assembly passes `oodCands`, at most one. (4) The OOD claim joins the pooled claims last, so that at the opening every candidate violates one of the pooled claims (`StackedPre`), and `stackedSpec` charges the batching $(J - 1)L_0/|E|$ with $L_0$ a bound on the candidates. (5) An accepted, non-escaped run has a good trace; the descent gives a candidate that is not bad, the extractor's output.

With Protocol D:

| today | Protocol D | status |
| --- | --- | --- |
| `Candidates μ R A W`: $K$-valued stacks, with high parts in $K[X]$ | unchanged. Level-0 list members are over $K$ (section 4.4) | proved |
| `OodBind`: separation of the candidates' multilinears at $z_0$, error $\binom L2\mu/q$ | `PointBind`: $z^{(0)}$ good for $O^{(0)}$ (Lemma P and $T^{(0)}_0 < 1$), error $\varepsilon^{\mathrm{pt}}_0$. It separates tuples, high parts included, hence stacks: two list tuples with different stacks are different tuples | proved |
| `oodCands S z y`: the candidate answering $y$, at most one | `ptCands`: the stack $g_{U}$ of the list tuple $U$ consistent with the $s_0$ answers, at most one | proved |
| front phases, charged per candidate | unchanged statements, applied to `ptCands` | inherited |
| the OOD claim among the pooled claims | removed from the pool. The point claims are handed to the opening as its carried claims, not as weighted claims | protocol |
| `StackedPre`: every (bad) candidate violates a pooled claim | every (bad) list tuple *satisfying the point claims* violates a pooled claim: the hypothesis of Theorem K | proved |
| `stackedSpec` lead $(J - 1)L_0/q$, hypotheses `hfin`, `hL₀` | $(J - 1)/q$; no bound on the candidates is needed at this message | proved |
| `traceGood`, `descendTrace`, `extractAS` | unchanged | section 5 |

### 6.2 The stacked claims

A pooled claim is a weighted claim on the stack $q$ with weight $\mathrm{eq}((\zeta, \mathsf{sel}_i), \cdot)$ or the ring-switched weight; rotated to the committed $f(u, x) = q(x, u)$ it is a weighted claim in the sense of `def:tuple-claim` and sees only low parts. Nothing changes. The commitment's OOD claim was "taken in $q$'s variable order and rotated"; the point claims have no variable order (they are evaluations of the lanes), so that rotation disappears. The prover's work for the points is proportional to the data rows, as for the encoder: a zero lane contributes zero to $\mathrm{ev}$.

### 6.3 The ring switch

Annex A reduces 64 claims $s_i = \widetilde Q_i(r)$ on the bit slices of $q_{\mathrm{keccak}}$ to one weighted claim, and its soundness is: for one fixed $K$-valued stack whose slices do not all match, the weighted claim is false except with probability $2/|E|$ over the sixteen scalars. It uses two properties of the candidate: it is one stack fixed before the scalars, and it is $K$-valued (so that it has bit slices). Protocol D gives both (`ptCands` has at most one element; section 4.4). In `ringSpec` the charge is $L_0\cdot2/|E|$ with $L_0$ the number of candidates passed, which stays one. The sixteen scalars and $\lambda_0$ are one verifier message with no prover message between, so its error is $2/q + (J_0 - 1)/q = (J_0 + 1)/q \le 513/q$, a grind of 7 bits by the rule $\lceil\log_2N\rceil - 3$ instead of today's 13.

### 6.4 The bytecode claim and the recursion

The deferred claim (`sec:deferred-claims`) is an evaluation of the bytecode multilinear, a public polynomial that is not committed with the PCS. It arises in the bus phase, is carried in the node's statement, batched across children by its own sumcheck, and discharged natively at the root. The opening's guarantee is not consumed there, and neither list sizes nor the OOD point enter. **[proved]** by inspection of `sec:e2e-bc`, `sec:deferred-claims` and of where `ood` occurs in `guests/lean_ethereum.py` and `crates/verifier/src/lib.rs` (only `read_ood` and the opening's glue).

The recursion consumes each child proof through the guest's in-circuit verifier, which must be Protocol D's verifier: $2s_i$ squeezes and $s_i$ reads per commitment, the update of step 1(c), the conversions, the final point checks, the point weights at the terminal check. No hint is needed (there is no division), so no new hinted value has to be pinned. `aggregate` only replays children to build the witness; the new stream fields would be read in both modes and the final point check would sit behind `Transcript::checked`, like every check today. The formal statement about the guest is for one node, not across recursion levels; that is unchanged, and Protocol D neither helps nor hurts it (the extractor is straight-line, as today).

### 6.5 Everything that used the Johnson list size or the OOD point

| where | use | fate |
| --- | --- | --- |
| `Front/OodBind.lean`, `ToArkLib/Whir/Ood.lean` | OOD separation with $L$ the Johnson list | replaced by pinning and the potential (M0) |
| `Whir/Sound/Spec.lean` `stackedSpec`, `eBatch` | $(J-1)L_0/q$ | $(J - 1)/q$ |
| `Whir/Sound/LevelMid.lean` (`eLam`, `eOod`, `MidOK.gap`) | $(J_{i+1} - 1)L_{i+1}/q$ and $\binom{L_i}{2}\nu_i/q$ | $(s_i + t_i)/q$ and $\varepsilon^{\mathrm{pt}}_{i+1}$ |
| `Whir/Sound/FoldRound.lean`, `FoldRoundCwyz.lean`, `ToArkLib/Whir/AffineCombiner*.lean` | $\varepsilon_{\mathrm{aff}} + 2\,\mathrm{jl}/q$ | Lemma F |
| `Whir/Params/{Check, Deployed}.lean` | the Johnson gap and the fold-round certificate table | the inequalities of the theorem card; with Johnson lists `ListBound` is discharged by the existing `card_tlist_le_jl` (`Sound/Tuple.lean`) |
| `Front/RingSwitch.lean` | $2L_0/q$ with $L_0$ the number of candidates passed, at most one (`oodCands`) | the same with `ptCands` |
| `crates/verifier` (`read_ood`, `verify_whir`, `verify_keccak_batch`), the two provers, `guests/lean_ethereum.py` (`ood_z`, `ood_scalars`, `eq_prefix_chain`), `formal/Statement/LeanVmVerifier.lean`, the wire encoding | the OOD sample and its glued claim | the point messages; a protocol change in all three verifiers, both provers and `formal/` |

Nothing else in the outer protocol mentions the list or the OOD point: in `doc/leanvm/body`, sections `01` to `07`, `09` and `10` and annexes A, C and D contain neither, section `08` mentions the OOD sample twice (the commitment step, and its place last among the pooled claims), and `formal/Statement/` has neither outside the transcription of the verifier. One consequence for the trusted statement: at a threshold beyond Johnson the end theorem acquires $\mathrm{ListBound}$ as a named hypothesis; with Johnson and counting lists it stays unconditional.

## 7. The hypothesis in its weakest sufficient form

Write $\Lambda_\Sigma(A)$ for the largest list at agreement $A$ and degree $d$ over words $D \to \Sigma$, for $\Sigma$ a finite-dimensional $K$-vector space ($K$, $E = K^2$, $E^h = K^{2h}$). Since $D \subseteq K$, evaluation at a point of $D$ is $K$-linear in the coefficients, so an $h$-lane $E$-valued word is a $2h$-lane $K$-valued word with the same list (note 00, section 4). $\mathrm{ListBound}_i(L_i)$ is the statement $\Lambda_{K^{m}}(A^{(i,0)}) \le L_i$ for all $m$.

### 7.1 The tree bound

**Theorem I (interleaving, any number of lanes). [proved]** Let $\mathcal C \subseteq \Sigma^n$ be a code in which two distinct codewords agree on at most $d$ coordinates, let $d < A \le n$ and $g := A - d$, and suppose every word of $\Sigma^n$ has at most $L$ codewords agreeing with it on at least $A$ coordinates. Define $N = N_{L,g}$ on integers by
$$N(\Phi) := 1 \ \text{ for } \Phi < 2g, \qquad N(\Phi) := N(\Phi - g) + (L - 1)\,N(\lfloor\Phi/2\rfloor) \ \text{ for } \Phi \ge 2g .$$
Then for every $m \ge 1$, every word of the $m$-fold interleaved code has at most $N(n - d)$ tuples of codewords agreeing with it on at least $A$ columns. Moreover
$$N(n - d) \le \sum_{k=0}^{\min(b, r)}\binom bk(L-1)^k \le \binom{b+r}{r}L^r, \qquad b := \Bigl\lfloor\frac{n - A}{A - d}\Bigr\rfloor, \quad r := \Bigl\lfloor\log_2\frac{n - d}{A - d}\Bigr\rfloor .$$
In particular the list is at most $1$ for $A > (n + d)/2$, at most $L$ for $A > (n + 2d)/3$, at most $2L - 1$ for $A > (n + 3d)/4$, and at most $L^2 + L - 1$ for $A > (n + 4d)/5$.

*Proof.* Let $w = (w_1, \dots, w_m)$ be the word. Build a tree: a node of depth $i$ is a sequence $(a_1, \dots, a_i)$ of codewords with $T := \bigcap_{k \le i}\mathrm{agr}(a_k, w_k)$ of size at least $A$ (the root has $T = [n]$). The leaves of depth $m$ are exactly the list members, with $T$ their agreement set. For a node put $\Phi := |T| - d \ge g$. A child by $a$ has $T' = T \cap \mathrm{agr}(a, w_{i+1})$ and *shrink* $s(a) := |T| - |T'| \le |T| - A$.

*Fact 1.* Two distinct children $a \ne a'$ of one node have $s(a) + s(a') \ge |T| - d = \Phi$: a column of $T$ where both agree with $w_{i+1}$ is a column where $a = a'$, and there are at most $d$ of those.

*Fact 2.* A node has at most $L$ children: each agrees with $w_{i+1}$ on at least $A$ coordinates.

*Fact 3.* If a node has two or more children, every child has $s(a) \ge g$: by Fact 1 and $s(a') \le |T| - A$, $s(a) \ge A - d$. So $\Phi' \le \Phi - g$ for every child, and $\Phi \ge 2g$ (a child has $\Phi' \ge g$).

*Fact 4.* If a node has two or more children, fix one of least shrink (the *heavy* child). Every other child has $2s(a) \ge \Phi$ by Fact 1, so $\Phi' \le \lfloor\Phi/2\rfloor$.

$N$ is non-decreasing (induction). Claim: the number of leaves of depth $m$ below a node is at most $N(\Phi)$. By induction on $m$ minus the depth. At depth $m$ it is $1$. A node with at most one child: the child has $\Phi' \le \Phi$. A node with two or more children: $\Phi \ge 2g$, the heavy child contributes at most $N(\Phi - g)$ and each of the at most $L - 1$ others at most $N(\lfloor\Phi/2\rfloor)$. At the root $\Phi = n - d$.

Closed form: along a root-to-leaf path every branching node costs $g$ of $\Phi$ (Fact 3), so there are at most $b = \lfloor(n - A)/g\rfloor$ of them, and every non-heavy edge halves $\Phi$ (Fact 4), which must stay at least $g$, so there are at most $r$ of them. A leaf is determined by its choices at the branching nodes of its path (heavy, or one of $L - 1$ others); padding these words with "heavy" to length $b$ is injective, because a path that has run out of branching nodes has one continuation. The number of words of length $b$ with at most $r$ non-heavy letters is the sum, which therefore bounds the list. The same count applies verbatim to the recursion tree of $N$ (a node $\Phi \ge 2g$ has one child $\Phi - g$ and $L - 1$ children $\lfloor\Phi/2\rfloor \le \Phi - g$, a node $\Phi < 2g$ is a leaf, and $N(\Phi)$ is its number of leaves), so the sum also bounds $N(n - d)$. The last inequality is $\sum_{k \le r}\binom bk \le \binom{b+r}{r}$ (Vandermonde). The special cases: $\Phi_0/g = (n-d)/(A-d)$ is below $2, 3, 4, 5$ respectively, and $N$ on $[g, 2g), [2g, 3g), [3g, 4g), [4g, 5g)$ is $1, L, 2L - 1, L^2 + L - 1$. $\square$

The theorem uses nothing about the code but the agreement bound $d$ (no linearity, any alphabet), like the Johnson bound. This is the argument of Gopalan, Guruswami and Raghavendra [GGR11] for interleaved codes, re-derived. The form transcribed in the brief from [ABF26, Lemma 2.10] ($\binom{b+r}{r}L^r$ with $b = \lceil\delta/\eta\rceil$, $r = \lceil\log_2(\delta_C/\eta)\rceil$) follows from Theorem I, since floors are at most ceilings and the sum is at most $\binom{b+r}{r}L^r$. Theorem I is strictly stronger where it matters here: at rate 1/2 and $A = 0.64n$ it gives $2L - 1$ where the transcribed form gives $10L^2$ ($b = 3$, $r = 2$ with ceilings). I could not compare with the ArkLib statement `InterleavedCode.lambda_interleaved_le_choose_mul_pow`: ArkLib is not vendored in this tree.

**[checked]** exhaustively (`scripts/14_interleave.c`, `scripts/14_run.sh`): for every word (one per coset of the code) of Reed-Solomon codes on subspace domains, the complete list was computed, then the exact maximum two-lane list over all pairs of words, and the exact three-lane maximum where the number of list profiles allowed it. Cases $(n, d, A)$: over $\mathrm{GF}(8)$, $(8,1,3)$, $(8,1,4)$, $(8,2,4)$, $(8,2,5)$, $(8,3,4)$, $(8,3,5)$, $(8,4,5)$, $(8,4,6)$, $(8,5,6)$; over $\mathrm{GF}(16)$, $(8,1,3)$, $(8,2,4)$, $(8,2,5)$, $(8,3,4)$, $(8,3,5)$, $(8,4,5)$, $(8,4,6)$, $(16,11,13)$, $(16,12,14)$, $(16,13,15)$. The bound holds in every case, and Fact 1 at the root held on all $2 \cdot 10^8$ pairs of members of one list. In every case the interleaved maximum *equals* the single-lane maximum ($7, 2, 14, 2, 70, 7, 56, 4, 28$ for the nine shapes at $n = 8$, the same over both fields; $35, 8, 1$ at $n = 16$). So where the bound is $L$ it is attained, and where it is $2L - 1$ or more it is not attained at these sizes. I do not know whether $2L - 1$ is ever attained.

### 7.2 The projection bound

**Proposition R2' (note 13, Proposition 3.4, verified and sharpened). [proved]** Let $D \subseteq K$, $s \ge 1$, and suppose $\Lambda_{K^s}(A) \le L$ with $L \le |K|^s/4$. Then for every finite-dimensional $K$-vector space $V$ (every extension of $K$, every lane count over $K$ or $E$), $\Lambda_V(A) \le L/(1 - L/|K|^s)$. In particular a bound $L \le 2^{62}$ for single $K$-valued words gives $L/(1 - L/2^{64}) \le \tfrac43L$ for all lanes and extensions, and a bound $L \le 2^{126}$ for single $E$-valued words gives $L/(1 - L/2^{128})$.

*Proof.* Take $L'$ list members $c_i \in V[X]$ of a word $w : D \to V$ with agreement sets $S_i$, and a uniformly random $K$-linear $\lambda : V \to K^s$, applied coefficientwise. For $x \in D \subseteq K$, $(\lambda c_i)(x) = \lambda(c_i(x))$, so $\lambda c_i$ has degree at most $d$ and agrees with $\lambda\circ w$ on $S_i$. For $i \ne j$ some coefficient $\gamma$ of $c_i - c_j$ is nonzero and $\Pr[\lambda\gamma = 0] = |K|^{-s}$. So some $\lambda$ has at most $\binom{L'}{2}/|K|^s$ colliding pairs, and the number of distinct $\lambda c_i$, all members of one list over $K^s$, is at least $L' - \binom{L'}{2}/|K|^s$. Hence $\ell' - \binom{\ell'}{2}|K|^{-s} \le L$ for every $\ell' \le L'$. If $L' \ge 2L$, take $\ell' = 2L$: $2L - L(2L - 1)|K|^{-s} \le L$ forces $|K|^s \le 2L - 1$, contradicting $L \le |K|^s/4$. So $L' < 2L$, and then $L'(1 - L|K|^{-s}) < L'(1 - (L' - 1)|K|^{-s}/2) \le L$. $\square$

I checked note 13's proof of its Proposition 3.4 (random projection, counting collisions): it is correct. Its factor 2 is what the same argument gives at the edge $L = |K|^s/4$; below the edge the loss is $1 + L/|K|^s$. The collision-free cases are note 10's Proposition 2.4 ($\binom{L+1}{2} < |\mathbb F|$, so $L < 2^{64}$ over $E$ and $L < 2^{32}$ over $K$) and note 04's Proposition 1.1; Proposition R2' doubles their range in the exponent by allowing collisions.

I also checked note 13's Proposition 3.5, $\Lambda_{K^2}(A) \le \Lambda_K(A)\,(1 + \Lambda_K(2A - d))$: correct (group the pairs by first component; a shared first component agrees with its lane on at least $2A - d$ columns; each first component carries at most $\Lambda_K(A)$ second components). Its special case "$\le 2\Lambda_K(A)$ for $A > (n + 3d)/4$" is the case $m = 2$, $\Phi_0 < 4g$ of Theorem I, which gives $2L - 1$ for every $m$.

### 7.3 Which reduction where

Let $L$ bound the lists of single $K$-valued words at $(A, d)$ and $\phi := (n - d)/(A - d)$.

| range | best bound for all lanes and extensions | by |
| --- | --- | --- |
| $\phi < 3$, that is $A > (n + 2d)/3$ | $L$ | Theorem I; no loss, no cap |
| $3 \le \phi < 4$, that is $(n + 3d)/4 < A \le (n + 2d)/3$ | $\min(2L - 1,\ L/(1 - L/2^{64}))$ | R2' if $L \le 2^{62}$, Theorem I otherwise |
| $\phi \ge 4$ and $L \le 2^{62}$ | $L/(1 - L/2^{64})$ | R2' |
| $\phi \ge 4$ and $L > 2^{62}$ | from $K$-valued words alone: $N_{L,g}(n - d)$, of order $L^r$ ($L^2 + L - 1$ for $\phi < 5$, at most $6L^2$ for $\phi < 8$, about $L^3$ at $\phi = 8$, about $26L^3$ at $\phi = 15$). Better: state the hypothesis for single $E$-valued words, $L_E \le 2^{126}$, and get $L_E/(1 - L_E/2^{128})$ by R2' with $s = 2$. With a second number, $\Lambda_K(2A - d)$: $L_E \le L(1 + \Lambda_K(2A - d))$ (note 13, Proposition 3.5) | Theorem I, or R2' with $s = 2$ |

At rate 1/2 the first two rows are $A > 2n/3$ and $A > 5n/8$ (up to the slack $\ell$): in the whole window between the known lists and Johnson, single $K$-valued words suffice with a factor at most 2 and no restriction on $L$.

**The final hypothesis.** For each level $i$ whose threshold is beyond Johnson:

> $\mathrm{H}_K(i; L)$: every word $D_i \to K$ has at most $L$ polynomials of $K[X]$ of degree at most $d^{(i)} = 2^{\kappa_i} - 1 + \ell_i$ agreeing with it on at least $A^{(i,0)}$ points.

It implies $\mathrm{ListBound}_i(L')$ with $L' = \min\bigl(N_{L,g}(n_i - d^{(i)}),\ L/(1 - L/2^{64})\ \text{if } L \le 2^{62}\bigr)$. Where both $\phi \ge 4$ and $L > 2^{62}$, use instead $\mathrm{H}_E(i; L)$, the same statement for words $D_i \to E$ and polynomials of $E[X]$, $L \le 2^{126}$, which implies $\mathrm{ListBound}_i(L/(1 - L/2^{128}))$. The code in the hypothesis is the Reed-Solomon code of dimension $2^{\kappa_i} + \ell_i$ on $D_i$: the degree slack is part of it. (Removing the slack costs a factor $|K|^{\ell_i}$ in $L$, which is 11 more points at level 0; I do not recommend it.)

### 7.4 Numbers

Level 0 of the $\mu = 30$ ladder ($\kappa = 24$, $\ell = 6$, $n = 2^{24+R}$, $d = 2^{24} + 5$), the bound assumed at $A^{(0,0)} = \lceil\tau n\rceil$, the queries seeing $A_0 - 1 = A^{(0,0)} + 5$; deployed grinds, $K_0 = 2^9q$, $\tau = 2^{-119}$. $\log_2$ of the interleaved bound from a single-lane $K$-valued bound $2^b$, then the points $s_0$ it requires and the queries $t_0$. **[checked]** exact arithmetic, `scripts/14_params.py` table T1.

| rate | $\tau$ | $\phi$ | tree bound $N$ | $b = 10$ | $b = 40$ | $b = 70$ | $b = 100$ | $s_0$ for $b = 10, 40, 70, 100$ | $t_0$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | $0.66$ | 3.13 | $2L - 1$ | 10 | 40 | 71 | 101 | 11, 12, 13, 14 | 181 |
| 1/2 | $0.64$ | 3.57 | $2L - 1$ | 10 | 40 | 71 | 101 | 11, 12, 13, 14 | 168 |
| 1/2 | $5/8$ | 4.00 | $L^2 + L - 1$ | 10 | 40 | 140 | 200 | 11, 12, 15, 16 | 160 |
| 1/2 | $9/16$ | 8.00 | $L^3 + 6L^2 - 8L + 2$ | 10 | 40 | 210 | 300 | 11, 12, 17, 19 | 131 |
| 1/4 | $7/16$ | 4.00 | $L^2 + L - 1$ | 10 | 40 | 140 | 200 | 11, 12, 15, 16 | 91 |
| 1/4 | $3/8$ | 6.00 | $4L^2 - 3L$ | 10 | 40 | 142 | 202 | 11, 12, 15, 17 | 77 |
| 1/4 | $5/16$ | 12.0 | about $10L^3$ | 10 | 40 | 213.3 | 303.3 | 11, 12, 17, 19 | 65 |
| 1/8 | $5/16$ | 4.67 | $L^2 + L - 1$ | 10 | 40 | 140 | 200 | 11, 12, 15, 16 | 65 |
| 1/8 | $1/4$ | 7.00 | $6L^2 - 6L + 1$ | 10 | 40 | 142.6 | 202.6 | 11, 12, 15, 17 | 55 |
| 1/8 | $3/16$ | 14.0 | about $20L^3$ | 10 | 40 | 214.3 | 304.3 | 11, 12, 17, 19 | 45 |
| 1/16 | $3/16$ | 7.50 | $6L^2 - 6L + 1$ | 10 | 40 | 142.6 | 202.6 | 11, 12, 15, 17 | 45 |
| 1/16 | $1/8$ | 15.0 | about $26L^3$ | 10 | 40 | 214.7 | 304.7 | 11, 12, 17, 20 | 37 |
| 1/16 | $3/32$ | 30.0 | about $140L^4$ | 10 | 40 | 287.1 | 407.1 | 11, 12, 19, 22 | 32 |

For $b \le 62$ the entry is R2' (no loss). For $b = 70, 100$ it is the tree bound: one bit at rate 1/2 above $5n/8$, a power below. With an $E$-valued or directly interleaved hypothesis the last two columns of $s_0$ are 13, 14 in every row.

At the lists note 13 predicts on the real domain (its final table; the list sizes are **[conjectured]** there, the arithmetic is **[checked]**, table T2):

| rate | threshold $A^{(0,0)}/n$ | predicted $\log_2\Lambda_K$ | interleaved bound ($\log_2$) and route | $s_0$ | $t_0$ |
| --- | --- | --- | --- | --- | --- |
| 1/2 | $0.64$ | 10 | 10, R2' (tree: 11) | 11 | 168 |
| 1/2 | $0.632$ | 10 | 10, R2' | 11 | 164 |
| 1/2 | $5/8$ | 30.8 | 30.8, R2' (tree: 61.6) | 12 | 160 |
| 1/2 | just above $9/16$ | 38.7 | 38.7, R2' | 12 | 131 |
| 1/2 | $9/16$ | 102.7 | from $K$ alone: 308.1 (tree), $s_0 = 20$. Proposition 3.5 gives two $K$-lanes $\le 2^{133.5}$, above the cap of the two-lane projection. With note 13's finer estimate $2^{113}$ for all lanes, or a direct hypothesis: | 14 | 131 |
| 1/4 | just above $3/8$ | 27 | 27, R2' | 11 | 77 |
| 1/4 | $3/8$ | 34.5 | 34.5, R2' | 12 | 77 |
| 1/8 | $17/64$ | 5 | 5, R2' | 11 | 57 |
| 1/8 | $1/4$ | 53.4 | 53.4, R2' | 12 | 55 |
| 1/16 | $0.153$ | 6 | 6, R2' | 11 | 40 |
| 1/16 | just above $1/8$ | 15.6 | 15.6, R2' | 11 | 37 |
| 1/16 | $1/8$ | 79.6 | from $K$ alone: 243.5 (tree), $s_0 = 18$. With $\Lambda_K(2A - d) \le 2^6$ (predicted): 85.6 by Proposition 3.5 and R2' with $s = 2$: | 13 | 37 |

("Just above" is $+2^{-10}n$. My $t_0$ counts the degree slack and the exact batching term, so it is one above note 13's at $n/4$ and $n/8$ exactly.) Reading: on the predicted lists the reduction to single $K$-valued words is free everywhere except at the two dyadic thresholds whose lists exceed $2^{62}$, where the natural hypothesis is on $E$-valued words.

Points per level against the interleaved list bound $2^b$ (table T3): the requirement is $s_i\log_2(1/\epsilon_i) \ge 3b + 357 + 119(\ell_i - 1) + 110$ up to rounding, that is $3b + 1062$ at level 0 and $3b + 824$ for $\ell = 4$.

| $\kappa$ | $\ell$ | $\log_2(1/\epsilon)$ | $s$ for $b = 7, 10, 40, 70, 100, 130, 340$ |
| --- | --- | --- | --- |
| 24 | 6 | 104.0 | 11, 11, 12, 13, 14, 14, 21 |
| 20 | 4 | 108.0 | 8, 8, 9, 10, 11, 12, 18 |
| 16 | 4 | 112.0 | 8, 8, 9, 10, 11, 11, 17 |
| 12 | 4 | 116.0 | 8, 8, 9, 9, 10, 11, 16 |
| 8 | 4 | 119.9 | 8, 8, 8, 9, 10, 11, 16 |
| 4 | 4 | 122.9 | 7, 7, 8, 9, 10, 10, 16 |
| 2 | 4 | 123.5 | 7, 7, 8, 9, 10, 10, 15 |

These agree with notes 10 and 11 to within one point at one level (the constant and $\epsilon$ differ slightly).

## 8. Theorem card

**Protocol.** Protocol D of section 1.3: Annex B's WHIR with affine folds, where after each commitment $i$ the verifier sends $s_i$ points $(\theta_m, \zeta_m) \in E^2$ in one message and the prover answers $\mathrm{ev}_{z_m}(P^{(i,0)}) = \sum_u\theta_m^{e(u)}P^{(i,0)}_u(\zeta_m)$; in each fold round the prover adds one scalar per point, $\mathrm{ev}_{z_m}$ of the first half, before the challenge; the carried values are updated by $v_m \leftarrow v_m + (\theta_m^{2^{j-1}} + \alpha + \beta\zeta_m)\varphi_m$; at a level's end each carried claim $P(\zeta_m) = v_m$ is converted to a low-part claim and batched with the queries; at the last level it is checked on the polynomial sent. There is no multilinear OOD claim.

**Parameters.** Per level: $\kappa_i, \ell_i, R_i, n_i = 2^{\kappa_i + R_i}$, a threshold $A_i$, queries $t_i$, points $s_i$. $d^{(i)} = 2^{\kappa_i} - 1 + \ell_i$, $A^{(i,j)} = A_i - (\ell_i - j)$, $\epsilon_i = (d^{(i)} + 2^{\ell_i} - 1)/q$. Free analysis constants: an integer $K_0 > 2q$ and $0 < \tau < 1$. Assumptions: $1 \le \ell_i \le 2^{\kappa_i}$, $d^{(i)} + 2 \le A^{(i,0)}$, $A_i \le n_i$, $\binom{n_i}{2} \le 2q$, $D_i \subseteq K$.

**Hypothesis.** $\mathrm{ListBound}_i(L_i)$ for every level: every interleaved word on $D_i$ with $2^m$ lanes over $E$, $0 \le m \le \ell_i$, has at most $L_i$ tuples of degree at most $d^{(i)}$ agreeing on at least $A^{(i,0)}$ columns. Sufficient: Johnson, when $(A^{(i,0)})^2 > n_id^{(i)}$; counting; or, for single-lane words over $K$ with at most $L$ polynomials of $K[X]$ at the same $(A^{(i,0)}, d^{(i)})$: $L_i = L$ if $A^{(i,0)} > (n_i + 2d^{(i)})/3$; $L_i = 2L - 1$ if $A^{(i,0)} > (n_i + 3d^{(i)})/4$; $L_i = \lfloor L/(1 - L/2^{64})\rfloor$ if $L \le 2^{62}$; $L_i = N_{L,g}(n_i - d^{(i)})$ in general; and for single-lane words over $E$ with at most $L \le 2^{126}$: $L_i = \lfloor L/(1 - L/2^{128})\rfloor$.

**Statement.** Protocol D is round-by-round sound, and round-by-round knowledge sound with the straight-line agreement-set extractor (one-error decoding on known sets, no list decoding, polynomial time), against the relation "the tuple $U^\ast$ of the level-0 list that matches the commit-phase answers satisfies every input claim", with per-message errors

| message | error | deployed grind | value at the deployed choice |
| --- | --- | --- | --- |
| points after commitment $i$ | $\bigl[\binom{L_i}{2} + \frac{L_i^3q^6}{K_0(K_0-1)(K_0-2q)}\sum_{j<\ell_i}\tau^{-j}\bigr]\epsilon_i^{s_i}$ | 15 | $\le 2^{-110}$ by the choice of $s_i$ |
| ring switch and $\lambda_0$ | $(J_0 + 1)/q$ (the PCS's share: $(J_0 - 1)/q$) | 7 (today 13) | $\le 513/q$, below $2^{-125.99}$ after the grind |
| fold round $j$ of level $i$ | $(K_0 - 1)/q^2 + \tau$; no $\tau$ at $j = \ell_i$ | 7 | $< 2^{-118}$ at $K_0 = 2^9q$, $\tau = 2^{-119}$ |
| queries of level $i$ and $\lambda_{i+1}$ | $((A_i - 1)/n_i)^{t_i} + (s_i + t_i)/q$; no second term at the last level | 17 | $\le 2^{-108}$ by the choice of $t_i$ |
| tail round | $2/q$ | 0 | $2^{-127}$ |

**Security level.** Every verifier message is at most $2^{-125}$ after its grind, the target of `SECURITY_BITS`, at any thresholds for which the hypothesis holds, with $s_i$ the least integer making the first row at most $2^{-110}$: 11 to 14 points at level 0 and 7 to 11 later for lists of $2^{7}$ to $2^{100}$, and $t_i = \lceil108/\log_2(n_i/(A_i - 1))\rceil$ up to one. The compilation to a non-interactive argument in the random-permutation model is the existing one.

**What it buys.** With Johnson lists everywhere: an unconditional theorem with one query fewer on most levels and no affine MCA theorem in the proof. With $\mathrm{H}_K$ at level 0 at the thresholds of section 7.4: 168 queries at $0.64n$ (rate 1/2), 77 just above $3n/8$ (rate 1/4), 55 at $n/4$ (rate 1/8), 37 just above $n/8$ (rate 1/16), against 218, 109, 73, 55 deployed.

## 9. What is not proved to my own standard

1. **The hypothesis.** $\mathrm{ListBound}$ beyond Johnson and counting is conjectural on every domain. This note only changes its form (section 7).
2. **Nothing is machine-checked.** Lemmas E, L1, L2, F, P, T, Theorems D', K, I and Proposition R2' are hand proofs. I wrote each in full and found no gap, and they agree with two independent derivations (notes 10 and 11) of the central lemma. Numerical evidence: note 10's exhaustive runs for Lemma F ($q \le 256$, $n \le 32$, at most two lanes per half, $\mathrm{eq}$ weights, one or two rounds); completeness and the extractor on toys; Theorem I exhaustively at $n \le 16$. The monomial-weight form of Lemma F with more than two lanes and the probability bound at real sizes are not reachable by brute force. What is needed: the formalization. Section 5 of note 11 gives Lean shapes; the corrections to them are the constant of `card_deepExc_le` ($K_0(K_0-1)(K_0-M)$ with `hK : M < K₀` in place of the $0.74$ conditions and the factor 4), $(d + 2^{j+1+m} - 1)$ in the count, and a lead of $(J + 1)/|E|$ for the stacked opening's first message.
3. **Fiat-Shamir and grinding.** Inherited from the existing framework. I checked that the state function has the shape the formal `Spec` expects (a doom predicate on histories; the point message is one group of $2s_i$ samples with no prover move inside, like today's OOD point; the potential $T_k$ is part of the doom, not of `Spec`'s own potential `V`), but nobody has instantiated it.
4. **The outer phases.** I read their statements and checked that each consumes only "a set of at most one $K$-valued candidate"; I did not re-prove them, and the claim that they go through with `ptCands` is at the level of statements.
5. **Recursion across levels.** The formal statement about the guest is for one node. Protocol D does not change that status.
6. **Whether the losses are real.** The proof pays $q^3$ for unexplained close codewords and $\tau^{-(\ell-1)}$ for reusing points: 952 of the 1062 bits at level 0. Note 10's evidence says both are artifacts (2 or 3 points might suffice). No proof, no approach. A variant with fresh points every round (note 10, G10) is not covered by anything here.
7. **Tightness of Theorem I** below $(n + 2d)/3$: unknown. At toy sizes interleaving did not enlarge any list. If $\Lambda_{K^m} \le \Lambda_K$ held in general, the $E$-valued form of the hypothesis would never be needed.
8. **The source of the interleaving bound.** I re-derived it and did not check [ABF26] or ArkLib against my statement (neither is available in this tree).
9. **Costs.** Not re-measured: prover time for the points (note 11's count: $2s_02^\mu$ carry-less multiplications at commit time), guest cycles.
10. **The two cells above $2^{62}$** (rate 1/2 at $9n/16$, rate 1/16 at $n/8$) have no lossless reduction to $K$-valued words; they need $\mathrm{H}_E$ or a second list number.

## 10. Reproduction

- `python3 doc/whir_soundness_gap_notes/scripts/14_params.py`: tables T1 to T4 (the reduction, the points, one budget) and self-tests. Under a second.
- `sh doc/whir_soundness_gap_notes/scripts/14_run.sh` builds `14_interleave.c` into `$TMPDIR` and runs every case of section 7.1 (about a minute and a half in all; `4 3 1 3` takes 40 s, `4 4 11 13` 11 s, `4 3 3 4` 8 s, `4 3 2 4` 7 s). One case by hand: `./interleave14 m N d A` for $\mathrm{GF}(2^m)$, $n = 2^N$. Do not use $A = d + 1$ at $n = 16$: the lists exceed the profile capacity and the program reports `OVERFLOW`.
- `python3 doc/whir_soundness_gap_notes/scripts/14_extractor_toy.py [seed]`: the extractor checks X1 to X5. Under a second.
- `python3 doc/whir_soundness_gap_notes/scripts/11_protocol_toy.py`: completeness of the protocol of section 1.3 (note 11's script, unchanged).

## References

- [ABF26] G. Arnon, D. Boneh, G. Fenzi. Open Problems in List Decoding and Correlated Agreement. 2026.
- [CWYZ26] A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng. Affine Combiners for Reed-Solomon Proximity Gaps. Cryptology ePrint Archive, Paper 2026/2863.
- [GGR11] P. Gopalan, V. Guruswami, P. Raghavendra. List decoding tensor products and interleaved codes. SIAM J. Comput. 40(5), 2011.
