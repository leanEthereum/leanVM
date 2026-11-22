# 81. Hypothesis KH for the mixed tree code (researcher 81, round 19)

Status line (updated as work proceeds): IN PROGRESS. Nothing below is final until the summary paragraph is rewritten.

## 0. Summary (placeholder, rewritten at the end)

In progress. No statement proved yet.

## 1. Setup, and what KH is for three members (L = 2, d = 1)

Notation of note 79. Plain T2 tree code, rate 1/2, $k = 2^v$, $n = 2k$, rows $g_y$, $\delta_y = M g_y \in K^2$ for $M \in K^{2 \times k}$ (rows $d_1, d_2$). One partner map $\pi$ (a permutation of the leaves), windows $W_x = \{x, \pi(x)\}$. $\mathcal K(\Lambda) = q^{-2k} \sum_{M \in \mathcal L} q^{w_{\rm free}(M)}$.

**Colouring of a rank-two $M$ (definition).** $Y_0(M) = \{y : \delta_y = 0\}$; for $y \notin Y_0$ the colour $\xi_M(y) \in \mathbb P^1(K)$ is the unique direction $c$ with $c^T \delta_y = 0$. So every rank-two $M$ partitions the leaves outside $Y_0$ into at most $q + 1$ colour classes $A_c$, and $v_c = c^T M$ (a nonzero codeword) vanishes exactly on $Z_c = A_c \cup Y_0$. A window is *mono* if its two leaves have the same colour, or one of them lies in $Y_0$. For a triple leaf $x$: $\dim \Phi_x(M) = [x \in Y_0] + [\pi x \in Y_0] + [\xi(x) = \xi(\pi x),\ \text{both} \notin Y_0]$; for a pair leaf with functional $\lambda_x$: $\dim \Phi_x = [W_x \subseteq Z_{\lambda_x}]$. Hence $w_{\rm free}$ is monotone in the pattern and the all-triple pattern is the worst: it is enough to bound the single number $\mathcal K_2 := q^{-2k} \sum_{\mathrm{rank}\, M = 2} \prod_x q^{2 - \mathrm{rank}[\delta_x, \delta_{\pi x}]}$ (**proved**, elementary). $\mathcal K_2$ is invariant under $M \mapsto gM$, $g \in \mathrm{GL}_2(K)$, so it is $q^{-2k} |\mathrm{GL}_2(K)| \sum_{V \in \mathrm{Gr}(2, k)} q^{w(V)}$: a sum over two-dimensional subspaces of the plain code.

**Erratum to note 79, Theorem 6.2 (proved; found here).** KH as written there (sum over all lists $M \in \mathcal L$) is **false** for every pattern with more than $k + n \log_2 C / 64$ triple leaves, for any code and any windows: a collinear list $M = (d, a d)$, $a \notin \{0, 1\}$, has $(-a, 1) \in \Phi_x(M)$ at every triple leaf, so $\mathcal K \ge q^{-2k} \cdot q^{k+1} \cdot q^{t_3} = q^{t_3 + 1 - k}$. The conclusion of Theorem 6.2 survives only after stratifying by the rank of $M$: rank-two lists need $\mathcal K_2 \le C^n$ (the statement studied here), and collinear lists are a statement about ONE codeword of V1: three collinear codewords at agreement $\tau n$ with a word force a nonzero codeword of V1 with at least $(3\tau - 1) n / 2$ zeros (all three agree wherever two do). So the three-member threshold is $\max\big(\tau_{\rm KH},\ (1 + 2(\rho + \sigma_1))/3\big)$ with $\sigma_1$ the proved excess of zeros of V1 over $\rho n$: below Johnson at rate 1/2 needs $\sigma_1 < 0.0607 = 3.88/64$. Note 79's pair statement gives $\sigma_1 = 2\varepsilon_0 + 2/64 \ge 8/64$, which is NOT enough: see Section 7 for what can be saved.

## 2. Scratchpad (in progress)

- Plan: (a) exact $\mathcal K_2$ at $(4, 8)$ by enumeration of $\mathrm{Gr}(2,4)$ over GF($2^4$), GF($2^6$), GF($2^8$), for cross-tree cycles, uniform cycles, the sibling map; (b) theory: first moment over twiddles, one level at a time.
