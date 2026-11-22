# Round 5 brief: the list bound in the DEEP-fold framework (lead)

Read this first, then `09-round1-synthesis.md` for the history. The rules of `00-lead-notes.md` section 5 apply (write only in `doc/whir_soundness_gap_notes/`, your report and scripts; no git writes; no installs; label every statement proved, checked numerically, or conjectured; no em or en dashes; no hard-wrapped prose; computations under about ten minutes and four cores). The paper `doc/deep_fold/` and its Lean development are committed and must not be edited.

## The one statement to prove

For the Reed-Solomon code of degree $< k = \rho n$ over $K = \mathrm{GF}(2^{64})$ evaluated on an evaluation set $D \subset K$ of $n$ points ($n = 2^{25}$ to $2^{28}$, $\rho \in \{1/2, 1/4, 1/8, 1/16\}$ at level 0, lower at later levels):

> **H_K$(\tau, b)$:** every word $w : D \to K$ has at most $2^b$ polynomials of $K[X]$ of degree $< k$ (in fact $\le k - 1 + \ell$, $\ell \le 6$) agreeing with it on at least $\tau n$ points,

for some $\tau$ strictly below the Johnson radius $\sqrt\rho$. Today $D$ is the $\mathbb{F}_2$-span of $1, x, \dots, x^{N-1}$.

## What the new framework changes (facts established in rounds 2 to 4, machine-checked where it matters)

1. **Only a list bound is needed.** With the DEEP fold (paper, Lemma 4.10 and Theorem 5.2), soundness at a threshold needs H_K at that threshold and nothing else: no correlated agreement.
2. **The budget is enormous.** The protocol with $s$ points per level tolerates lists up to about $2^{35(s - 10)}$; each extra point costs about 0.2 percent of proving time and 112 bytes. So $b = 100$ is free, $b = 1000$ costs about 40 points, and a bound like $n^{40}$ or $2^{O(N^2)}$ would be entirely usable. Polynomial or even mildly quasi-polynomial bounds are fine. Exponential bounds $2^{cn}$ are useless.
3. **Single lane, small field.** Interleaved words over $E$ reduce to single words over $K$ with a loss of at most a factor 2 (machine-checked for $L \le 2^{63}$ or above the $(n+3d)/4$ threshold).
4. **The evaluation set is free.** leanVM's WHIR folds lanes, not the domain, and the DEEP-fold lemma holds for any evaluation set. So $D$ may be changed to anything on which the prover can encode fast enough and the verifier can evaluate a tensor-structured basis: another subspace, a union of cosets with arbitrary representatives, a subset of a larger subspace, even points in $E$ (but points outside $K$ double the level-0 leaf size, since level-0 lanes are $K$-valued).
5. **Large lists are not attacks any more.** Under the DEEP fold the cheapest known attack costs $2^{134}$ regardless of list sizes. The list bound is needed by the proof. So the "attack side" in the new framework is only: where do lists provably exceed any affordable budget (pigeonhole near capacity, about $\tau < \rho + 1/64$ on a 64-bit field).

## What is known about H_K

- Proved for all words on every domain: Johnson only ($\tau > \sqrt\rho$).
- Proved lower bounds on every subspace domain: $n - 1$ at $\tau = 1/2$ for $\rho = 1/4$; $56n - 392$ at $5/8$, $105n - 965$ at $9/16$, and about $1/(64\epsilon^2)$ at $5/8 + \epsilon$ for $\rho = 1/2$. All are polynomial in $n$ in the windows: nothing known contradicts H_K$(\tau, 100)$ down to $9/16$ at rate 1/2.
- Proved upper bounds in the formal model (basis algebraically independent) for top-type words; on every domain for strict tops inside one structural class (`12`, `19`, `21`).
- For arbitrary words: nothing beyond Johnson, on any domain. Reductions to conjectures P (three members, partial: `17`, `26`), Q/H4 (four members: `27`), S3 (`30`). Exhaustive truth at $n = 16$ (`18`). Failed attack (`25`).
- Dead ends, do not repeat: `04` section 4, `13` section 6, `30` (direct GM-MDS induction), character sums at $n < \sqrt{|K|}$, pinning points plus Johnson, restricted Guruswami-Sudan, recursion through $x \mapsto x^2 + ax$ without invariance (agreement drops to $2\tau - 1$).

## Round 5 assignments

- **35:** transfer the large-characteristic beyond-Johnson list proofs (2026 literature, and the Proximity Prize KoalaBear proofs) to characteristic 2, using the translation structure of subspace domains.
- **36:** evaluation sets with PROVEN list bounds (generic, random, punctured), with explicit constants at our sizes and budgets, and their encoding cost.
- **37:** a dimension induction with a large budget: structure versus randomness in $\mathbb{F}_2^N$, aiming at any bound $2^{\mathrm{poly}(N)}$.
