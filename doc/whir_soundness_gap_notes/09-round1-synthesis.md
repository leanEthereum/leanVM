# Round 1 synthesis (lead)

Entry point for round 2. It supersedes `00-lead-notes.md` and sections 3 to 5 of `doc/whir_soundness_gap.md` where they disagree. Notation: $K = \mathrm{GF}(2^{64})$, $E = \mathrm{GF}(2^{128})$, $D$ the $\mathbb{F}_2$-span of $1, x, \dots, x^{N-1}$, $n = 2^N$, rate $\rho = 2^{-R}$, $k = \rho n$, $\Lambda(T)$ the largest list at agreement $T$, $t = \lceil 108/\log_2(n/A)\rceil$ queries at threshold $A$. The rules of `00-lead-notes.md` section 5 still apply to every agent.

## 1. Where the gap stands (level 0, $\mu = 30$)

| rate | proven (Johnson), deployed $t$ | attack: lists $\ge 2^{10}$ up to $T/n$ | attack floor $t$ | status |
| --- | --- | --- | --- | --- |
| 1/2 | 218 | $5/8$ ($2^{30.8}$ members), $0.629$ ($2^{10}$, padded) | 160 | open on the proof side only |
| 1/4 | 109 | $1/2$ (flats, $2^{26}$) | 108 | closed on subspace domains |
| 1/8 | 73 | $1/4$ (flats, $2^{51}$) | 54 | open |
| 1/16 | 55 | $1/8$ (flats, $2^{77}$) | 36 | open |

Attack side: notes 01, 02, 05 agree independently (three derivations of the $5n/8$ family at rate 1/2; exact count $56n - 392$, the full list of its word at $n = 32$). Nothing above $0.629n$ at rate 1/2 is known on any binary domain.

## 2. What round 1 established

1. **The list attack is real** (note 03): flats at rate 1/4 break the protocol as soon as $t_0 \le 107$. Pole pairs are never a real attack, only a constraint on the current state function. Path cost is between the max and the sum of per-message costs.
2. **Grinding cannot pay for big lists** (note 03): a list budget of $2^{16}$ costs 1.24 times today's grinding, $2^{20}$ costs 8 times, $2^{26}$ about 450 times.
3. **DEEP fold** (note 07, Theorem 3; proved on paper, toy-checked, NOT independently verified): if the prover answers $s$ univariate out-of-domain evaluations of the two halves before the fold challenge, and these claims are carried unbatched, the fold round's error is $K_0/|E|^2$ with $K_0 \approx 2.72|E|$, with no list factor, no pole-pair factor and no Johnson hypothesis. Then the only thing needed to lower a threshold is $\mathrm{ListBound}$: $\Lambda(A) \le 2^b$ with $b$ up to 40 to 100 (about 35 bits of list per extra point). A protocol change.
4. **Higher-degree combiners, larger challenge fields, folded Reed-Solomon, multiplicity codes do not help** (notes 06, 07). Capacity at rate $\rho$ equals Johnson at rate $\rho^2$, so squaring the level-0 rate dominates any capacity code with bundled symbols.
5. **Rigidity on generic domains** (notes 02, 04, 05, three independent proofs): for families of sets whose locators share their top ("strict common top"), on a domain whose basis is algebraically independent, lists above $5n/8$ at rate 1/2 have at most $1/(2\tau - 1)^2$ members ($\tau = T/n$), and similarly small bounds hold in the windows at rates 1/8 and 1/16. Characterization: two sets share $e_1..e_{2^{a+1}-1}$ iff their Walsh spectra agree mod $2^{a+2}$. Note 04 extends it to words with up to about $\sqrt{n}$ extra roots.
6. **Nothing is proved for all words on the real domain** (note 04). The real domain is not generic: at toy sizes most common-top pairs are accidents of the embedding, class sizes exceed the generic ones by a small factor, and note 01 predicts non-generic "Gold" families of about $2^{30}$ at rate 1/4, $T = 3n/8$.
7. **Domain change** (note 06 section 6.2): at $R \ge 2$ a union of cosets of the message subspace with additively independent representatives costs the same NTT, keeps the Annex B proof, and cuts the flats family from $2^{26}$ to 3. It reopens rate 1/4 (floor about 65) without proving anything.
8. **Re-tuning inside today's proof** (note 08, validated model): 5 to 12% smaller openings from constants and a 32-lane level 0.

## 3. The problem, restated

After round 1 the open problem is a statement about the code alone:

> **ListBound$(\rho, \tau, b)$:** for every word $w: D \to E$ (any number of interleaved lanes), at most $2^b$ polynomial tuples of degree at most $d$ agree with $w$ on at least $\tau n$ points.

With the DEEP fold, ListBound$(1/2, 0.64, 40)$ would give about 168 queries instead of 218, and ListBound$(1/2, 9/16 + \epsilon, 100)$ about 131. Conjecture C of note 04 says ListBound$(1/2, 0.64, 10)$ holds. No approach to a proof on the real domain exists yet.

## 4. Round 2 assignments

- **10, red team on the DEEP fold:** try to break Theorem 3 of note 07 and its use in the protocol; independent re-derivation and larger brute-force checks.
- **11, DEEP-fold WHIR written out:** the full protocol, exact error terms and parameters, the round-by-round theorem conditional on ListBound, costs.
- **12, ListBound for all words on generic domains:** steps 1, 2 and 4 of note 04 section 6.
- **13, the real domain:** decisive experiments on real-shape domains, the pigeonhole-corrected conjecture, and any provable handle, including domains chosen to make a bound checkable.
