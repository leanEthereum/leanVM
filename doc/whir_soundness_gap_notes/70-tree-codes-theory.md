# 70. Random tree codes: theory from first principles

Researcher 70, round 15, 2026-11-21. Status tags on every statement: **proved** (complete proof on this page), **sketched**, **conjectured**, **false**. Not refereed.

## Summary (first paragraph, rewritten at the end)

Work in progress. This paragraph is replaced when the note is finished.

## 0. Notation

$K = \mathrm{GF}(2^{64})$, $q = |K|$, $E = \mathrm{GF}(2^{128})$. Message table $m \in K^{2^v}$, $k = 2^v$, rate $\rho = 2^{-r}$, $n = 2^{v+r}$ leaves, $R = 2^r$ trees. Leaf $j = (j_{v+r-1}, \dots, j_0)$; a node at depth $d$ below a root (level $i = v - d$) is a prefix $p$ with $r + d$ bits and owns the block of $2^{v-d}$ leaves below it. The node $p$ at level $i+1$ carries the twiddle pair $(t_i(p,0), t_i(p,1))$ used by its two children. T1: $t_i(p,1) = t_i(p,0) + 1$, $t_i(p,0)$ uniform. T2: $t_i(p,0)$, $t_i(p,1)$ independent uniform (we do not condition on them being distinct; the event that they coincide is charged in the failure probability).
