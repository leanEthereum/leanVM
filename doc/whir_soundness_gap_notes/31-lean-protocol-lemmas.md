# 31. The lemmas around the DEEP fold lemma, machine-checked in Lean 4

Researcher 31. This note says exactly which of the lemmas that surround Lemma F in the protocol-side soundness chain are now checked by Lean 4 with Mathlib: Lemma P (pinning) and Lemma T (the potential) of note 14, Lemma S (the ladder potential) of note 15, the exponent maps $e_j$ of Definition E, the link between $\mathrm{List}(O; A, d)$ and the candidate set $\mathcal T$, and the arithmetic of the parameter claim at level 0. The sources are the library `Protocol` of the project in `lean/` (seven files, about 1800 lines, `lean/Protocol/README.md`). It imports the library `DeepFold` of note 22 and is imported by the library `Rounds` of researcher 32 (the per-message transitions and the extractor step, which are not in this note). Tags: **[machine-checked]** means a Lean theorem that compiles with no `sorry` and depends on Lean's three axioms only; **[not formalized]** means no Lean statement exists.

## 0. Summary

1. **Lemma P, Lemma T and Lemma S are machine-checked**, each abstractly and for the objects of `DeepFold`, with the quantifier order the protocol needs: the points first, the challenges one at a time, no prover message anywhere. The end statements are `lemmaP`, `pinned_unique` (Lemma P), `levelPot_init`, `levelPot_step` (Lemma T (a), (b)), `dens_not_good_le` (the point message's error $\varepsilon^{\mathrm{pt}}_i$ of Theorem D'), `ladderPot_init`, `ladderPot_step` (Lemma S (a), (b), (c)) and `dens_not_goodS_le` (the first point message of Theorem D$_S$).
2. **The exponent map is no longer an assumption.** `exL` is the $e_j$ of Definition E, proved injective (`exL_injective`) with largest value $2^{j+r} - 2^j$ (`exL_add_le`) and with (E2) in its concrete form (`evL_exL_halves`). Note 22 listed this as assumed. So the $\epsilon$ of every statement here is literally $(d + 2^\ell - 1)/q$.
3. **The parameter claim is machine-checked** as rational arithmetic on explicit numerals and as a statement about a field of $2^{128}$ elements: with $L = 2^{40}$, $K_0 = 2^9q$, $\tau = 2^{-119}$, $d = 2^{24} + 5$, $\ell = 6$, twelve points are good except with probability at most $2^{-110}$ (`level0_point_error`), eleven do not meet the bound (`point_error_level0_arith_11`), the ladder $6{+}1{+}1{+}2{+}1{+}1$ meets it (`level0_ladder_error`), and the fold message's error is at most $2^{-118}$, $2^{-119}$ in the last round (`fold_error_arith`, `fold_error_last_arith`).
4. **No error and no missing hypothesis was found in the hand proofs.** Section 4 lists what the formalization shows: three hypotheses are not used ($\tau < 1$, $K_0 > M$ and any relation between $A$, $d$, $n$, in these lemmas), and one sentence of note 15 is loose (the potential of Lemma S with one batch is not Lemma D6's potential word for word; it dominates it and has the same bounds).
5. **Checked on `h4`** with Lean 4.36.0 and Mathlib `v4.36.0`, twice: every module from an empty output directory against the Mathlib already built on the host, and a real `lake build DeepFold Protocol` in a private copy of the project. Section 1.
6. **Not formalized here**: the transitions M0 to M5 and the extractor (library `Rounds`, researcher 32), the hypothesis $\mathrm{ListBound}$ itself, the Fiat-Shamir compilation, and the items of section 5.

## 1. How it was checked

Host `h4`, scratch directory `/data/whir_lean_scratch_31` (created for this; safe to delete). Lean `leanprover/lean4:v4.36.0`, Mathlib tag `v4.36.0` (revision `fc4f59e577`), the toolchain and manifest of `lean/`, which this work did not edit. Nothing was installed or built on the Mac.

- Run 1: every module of `DeepFold` and `Protocol` compiled in dependency order with `lean -o`, with `warningAsError`, from an empty output directory, against the Mathlib already built in `/data/lean436/formal/Statement/.lake/packages` (read only, through `LEAN_PATH`). No output: no error, no warning.
- Run 2: a copy of the whole project in `/data/whir_lean_scratch_31/lakeproj` with the Mathlib packages of note 22's scratch project copied in (same manifest, same revisions), then `lake build DeepFold Protocol` on 8 threads: `Build completed successfully (18289 jobs)`. The only messages are Lake's advisory that `DeepFold/Basic.lean`, `DeepFold/Counting.lean` and `Protocol/Potential.lean` import `Mathlib` without the module system, which is not a Lean warning.
- No `sorry`, `admit`, `axiom` or `native_decide` occurs in the sources. `Protocol/Axioms.lean` runs `#print axioms` under `#guard_msgs` on all 99 theorems of the library: 96 depend on `propext`, `Classical.choice`, `Quot.sound`, three on a subset (`exL_succ`, `two_pow_dvd_exL`, `foldW_apply`), and the build fails if that changes.
- `Protocol/Axioms.lean` instantiates `level0_point_error`, `level0_ladder_error`, `levelPot_step` and `ladderPot_step` at `GaloisField 2 128`, with the hypothesis $|K| = 2^{128}$ proved (`card_galoisField_two_128`).
- The SHA-256 of every file of `lean/Protocol/`, `lean/Protocol.lean`, `lean/DeepFold/`, `lean/DeepFold.lean`, the lakefile, the toolchain file and the manifest is the same in the repository and in both directories built on `h4`. For the record, the first eight hex digits for the `Protocol` sources as checked: `Potential.lean` ebf3431c, `Lists.lean` 4dd6f1bc, `Pinning.lean` f3665460, `Level.lean` 3e96aa23, `Ladder.lean` aa1d3101, `Params.lean` 8aee005a, `Axioms.lean` c9607d1c, `Protocol.lean` 58d8ede0.
- The library `Rounds` as it stood at the time of the check (it imports `Protocol.Pinning`) also builds against these files in the same Lake project (`lake build Rounds`, green).
- The numbers of section 2.6 were also recomputed in exact rational arithmetic outside Lean: the one-batch bound is $2^{-175.99}$ at 12 points and $2^{-71.99}$ at 11, the ladder bound $2^{-116.99}$, the fold bounds $2^{-118.0}$ and $2^{-119.0}$ from below.

## 2. What is stated and checked

Notation of the Lean. `K` is a finite field. A point is `z : K × K`, $z = (\theta, \zeta)$, and `evL ex z U` is $\mathrm{ev}_z(U)$ of `DeepFold`. `dens p` is the number of elements of a finite type that satisfy `p` over the size of the type (a probability under the uniform distribution) and `avg f` the mean of `f`, both in $\mathbb Q$. A state of a level is indexed by `k`, the number of fold rounds played, and `r`, the number still to come; note 14's round $j$ is `k + 1 = j`, and $\ell =$ `k + r`.

### 2.1 Lists and the candidate set

| Lean statement | content | hand statement | status |
| --- | --- | --- | --- |
| `listW D O d A`, `mem_listW` | the finite set $\mathrm{List}(O; A, d)$: tuples of degree at most $d$ agreeing with $O$ on at least $A$ columns of $D$ | note 14 section 2 | **[machine-checked]** |
| `listW_anti`, `card_listW_le` | lists at a larger agreement are subsets | note 14, after $\mathrm{ListBound}$ | **[machine-checked]** |
| `mem_fullT_iff_mem_listW`, `card_fullT_fiber` | $(c, P) \in \mathcal T$ iff $P \in \mathrm{List}(O_c; A, d)$; the fibre of $\mathcal T$ over $c$ has the size of that list | note 14 section 3, the definition of $\mathcal T$ | **[machine-checked]** |
| `fullT_fiber_le` | a bound on the lists of all folds is the $\Lambda$ that `lemmaF_exc` takes | "$\Lambda \ge \max_c\lvert\mathrm{List}(O_c; A, d)\rvert$" | **[machine-checked]** |
| `agrL_eq_agrW`, `agrPairL_eq_agrW` | the agreement sets of `DeepFold` (of a candidate with the fold, of a pair with the two halves) are agreement sets of a tuple with a word | | **[machine-checked]** |
| `listBound_level` | $\mathrm{ListBound}_i(L)$ in note 14's form (every word with at most $\ell$ lane variables, at the agreement $A^{(i,0)}$) gives the form the statements below take (every word folded $k$ times, at its own threshold) | note 14 section 2 | **[machine-checked]** |

### 2.2 The exponents $e_j$ (Definition E)

| Lean statement | content | hand statement | status |
| --- | --- | --- | --- |
| `Lane r`, `exL j r` | lanes $\{0,1\}^r$ as an iterated sum, the first summand the half with folded variable $0$; $e_j(u) = \sum_k (1 - u_k)2^{k-1}$ on the $r$ variables $u_{j+1}, \dots, u_{j+r}$ | Definition E | definition |
| `exL_injective` | the exponents are pairwise distinct | "(binary digits)" in the proof of (E4) | **[machine-checked]** |
| `exL_add_le` | $e_j(u) + 2^j \le 2^{j+r}$: the largest exponent is $2^\ell - 2^j$ | the proof of (E4) | **[machine-checked]** |
| `two_pow_dvd_exL` | every exponent of $e_j$ is a multiple of $2^j$ | | **[machine-checked]** |
| `evL_exL_halves` | $\mathrm{ev}^{(j)}_z(U) = \theta^{2^j}\mathrm{ev}^{(j+1)}_z(F) + \mathrm{ev}^{(j+1)}_z(G)$ | Lemma E (E2) | **[machine-checked]** |

### 2.3 Lemma P (pinning)

Hand statement (note 14): let $|\mathrm{List}(O; A, d)| \le L$; for independent uniform points, except with probability at most $\binom L2\epsilon^s$, any two distinct members have different evaluations at some point; then for every answer vector at most one member is consistent with all answers.

| Lean statement | content | status |
| --- | --- | --- |
| `card_evL_eq_le` | two distinct tuples of degree at most $d$ agree at no more than $(d + E)q$ of the $q^2$ points: probability at most $\epsilon = (d + E)/q$ at one uniform point | **[machine-checked]** |
| `card_evL_eq_all_le` | they agree at all of $s$ points for at most $((d + E)q)^s$ of the $q^{2s}$ vectors | **[machine-checked]** |
| `NonSep S ex s` | the vectors of $s$ points at which two distinct members of $S$ have equal evaluations at ALL $s$ points | definition |
| `card_nonSep_le` | $\lvert\mathrm{NonSep}\rvert \le \binom{\lvert S\rvert}{2}((d + E)q)^s$ | **[machine-checked]** |
| `dens_nonSep_le` | for $\lvert S\rvert \le L$: density at most $\binom L2\epsilon^s$ | **[machine-checked]** |
| `lemmaP` | the same for $S = \mathrm{List}(O; A, d)$: Lemma P | **[machine-checked]** |
| `pinned_unique`, `card_pinned_le_one` | outside `NonSep`, for every answer vector at most one member of $S$ matches all answers | **[machine-checked]** |

The union is over the $\binom{\lvert S\rvert}{2}$ unordered pairs (the two-element subsets of $S$), so the constant is exactly the note's. `NonSep` depends on the set and the exponents only; the answer vector `y` of `pinned_unique` is quantified after the points.

### 2.4 Lemma T (the potential)

Hand statement (note 14). $O^{(k)}$ is $O$ folded by $c_1, \dots, c_k$; $\varepsilon_\ast$ bounds $\Pr_{\mathbf z}[\mathbf z \in \mathrm{Exc}_j(O')]$ for every $j$ and every word $O'$ of the shape of round $j$; $\pi^{(k)}_j := \Pr_{c_{k+1}, \dots, c_{j-1}}[\mathbf z \in \mathrm{Exc}_j(O^{(j-1)})]$ and $T_k := \sum_{j=k+1}^{\ell}\tau^{-(j-k-1)}\pi^{(k)}_j$. Then (a) $\Pr_{\mathbf z}[T_0 \ge 1] \le \varepsilon_\ast\sum_{j<\ell}\tau^{-j}$; (b) if $T_{k-1} < 1$ then $\mathbf z \notin \mathrm{Exc}_k(O^{(k-1)})$ and $\Pr_{c_k}[T_k \ge 1] < \tau$.

The Lean is in two layers. The abstract layer (`Protocol/Potential.lean`) knows nothing of polynomials: `A k r` is the type of words after `k` rounds with `r` to come, `fold k r : A k (r+1) → C k r → A (k+1) r`, `Z` the type of point vectors, and `bad k r a z` the event "$z$ is exceptional for the round played from $a$".

| Lean statement | content | hand statement | status |
| --- | --- | --- | --- |
| `pot`, `potT` | the potential by recursion on the rounds to come: $T = 0$ when none is left, and otherwise $T(a) = \mathbf 1[\mathrm{bad}(a, z)] + \tau^{-1}\,\mathbb E_c[T(\mathrm{fold}(a, c))]$ | $T_k$ (see `potT_eq_sum`) | definition |
| `probBad`, `potT_eq_sum` | $T = \sum_{j < r}\tau^{-j}\pi_j$, where $\pi_0$ is the indicator for the current word and $\pi_{j+1}(a) = \mathbb E_c[\pi_j(\mathrm{fold}(a, c))]$ | the definition of $T_k$ and $\pi^{(k)}_j$ | **[machine-checked]** |
| `badSeqs`, `probBad_eq_card` | $\pi_j$ is the number of sequences of $j$ challenges that lead to a word for which $z$ is exceptional, over $\lvert C\rvert^j$ | "$\Pr_{c_{k+1}, \dots, c_{j-1}}$" | **[machine-checked]** |
| `potT_zero`, `potT_one` | $T_\ell = 0$; in the last round $T$ is the indicator, with no $\tau$ | "$T_\ell = 0$", "for $\ell = 1$ there is no $\tau$" | **[machine-checked]** |
| `avg_pot_step` | $\mathbb E_c[T_{\text{next}}] = \tau\,(T - \text{cost of the current round})$ | "$\mathbb E_{c_k}[T_k] = \tau(T_{k-1} - \pi^{(k-1)}_k)$" | **[machine-checked]** |
| `potT_step` | if $T(a) < 1$ then $z$ is not bad for $a$, and $\{c : T(\mathrm{fold}(a, c)) \ge 1\}$ has density less than $\tau$ | Lemma T (b) | **[machine-checked]** |
| `potT_init` | if round $(k, r)$ is bad with probability at most $e_{k,r}$ over $z$ for every word of its shape, then $\Pr_z[T \ge 1] \le \sum_j\tau^{-j}e_j$ | Lemma T (a), with a bound per round | **[machine-checked]** |
| `potT_init_const` | with one bound $\varepsilon_\ast$ for all rounds to come: $\Pr_z[T \ge 1] \le \varepsilon_\ast\sum_{j<r}\tau^{-j}$ | Lemma T (a) | **[machine-checked]** |

The instance for a level (`Protocol/Level.lean`): words are `Word K r = K → Lane r → K`, the fold is `foldW O c` $= O_1 + (\alpha + \beta x)O_0$, the points are `z : Fin s → K × K`, and "bad" is membership in `excW`, which unfolds to `ExcL (fullT D (half₀ O) (half₁ O) d (thr (k+1))) (exL (k+1) r) s B`: the $\mathrm{Exc}_{k+1}(O)$ of Lemma F at the agreement $A^{(i,k+1)}$ with the exponents $e_{k+1}$ and the threshold $B$ (in the notes $B = K_0(K_0-1)(K_0-M)$).

| Lean statement | content | hand statement | status |
| --- | --- | --- | --- |
| `levelPot τ D d thr s B z k r O` | $T_k$ for the word $O = O^{(k)}$ and the points $z$ | $T^{(i)}_k$ of section 4.2 | definition |
| `levelPot_succ`, `levelPot_eq_sum`, `levelPot_eq_sum_card` | the recursion, and $T_k = \sum_j\tau^{-j}\pi_j$ with $\pi_j$ a count of challenge sequences over $q^{2j}$ | the definition of $T_k$ | **[machine-checked]** |
| `levelPot_step` | if $T_k < 1$ then $z \notin \mathrm{Exc}_{k+1}(O^{(k)})$, in the very form `lemmaF_round` takes as hypothesis, and $\Pr_c[T_{k+1} \ge 1] < \tau$ | Lemma T (b) as used in M2 | **[machine-checked]** |
| `dens_excW_le` | $\Pr_z[z \in \mathrm{Exc}] \le L^3q^6\epsilon^s/B$ for a word of the level whose folds have lists of at most $L$ | Lemma F (1) with $\Lambda = L_i$ | **[machine-checked]** |
| `levelPot_init` | under the list bound for every word folded more than $k$ times: $\Pr_z[T_k \ge 1] \le (L^3q^6\epsilon^s/B)\sum_{j<r}\tau^{-j}$ | Lemma T (a) with the $\varepsilon_\ast$ of M0 | **[machine-checked]** |
| `Good`, `dens_not_good_le` | $z$ is good for $O$ if it separates $\mathrm{List}(O; A^{(i,0)}, d)$ and $T_0 < 1$; the points are not good with probability at most $\bigl[\binom L2 + \frac{L^3q^6}{B}\sum_{j<\ell}\tau^{-j}\bigr]\epsilon^s$, $\epsilon = (d + 2^\ell - 1)/q$ | goodness (section 4.2) and $\varepsilon^{\mathrm{pt}}_i$ (Theorem D', M0) | **[machine-checked]** |

### 2.5 Lemma S (the ladder)

Hand statement (note 15, with the threshold $\Theta$ of note 14 as in note 20 section 4). $\sigma_j$ is the number of points held at round $j$, $N_j$ the triple count of round $j$ for the word $O^{(j-1)}$ and all $\sigma_j$ points, $T(t) := \sum_j \mathbb E[N_j \mid \text{messages up to } t]/(\Theta\,\tau^{n_j(t)})$ over the rounds not yet started. (a) $\Pr[T \ge 1$ after batch 1$] \le \sum_j e_j\tau^{-(j-1)}$, $e_j = (L^3q^6/\Theta)\epsilon^{\sigma_j}$; (b) if $T < 1$ before the message $(c_j, \text{batch } j{+}1)$ then $T \ge 1$ after it with probability less than $\tau$; (c) if $T < 1$ before round $j$ then $N_j < \Theta$: the points held are not exceptional.

In the Lean the state is the pair (word, list of all points sampled so far), the verifier message of round `k + 1` is a pair (challenge, vector of `bt k` fresh points), and the cost of a round is $N/B$. The potential is the same `pot` as for Lemma T, for this process, so (b) and (c) are one lemma (`pot_step`) for both.

| Lean statement | content | hand statement | status |
| --- | --- | --- | --- |
| `potS`, `potS_succ` | $T(a, \mathrm{pts}) = \mathrm{cost}(a, \mathrm{pts}) + \tau^{-1}\,\mathbb E_{(c, p)}[T(\mathrm{fold}(a, c), \mathrm{pts} \mathbin{+\!\!+} p)]$ | $T(t)$ | definition |
| `potS_step` | $T < 1$ gives cost $< 1$ and $\Pr_{(c,p)}[T_{\text{next}} \ge 1] < \tau$ | Lemma S (b), (c) | **[machine-checked]** |
| `avg_ofFn_append` | two independent uniform batches of $n$ and $m$ points are one uniform batch of $n + m$ | "all $\sigma_j$ points are uniform and independent, whatever message they were drawn in" | **[machine-checked]** |
| `held`, `potS_init` | with $\sigma_j$ = `held bt k n j`: $\Pr[T \ge 1] \le \sum_j\tau^{-j}e_j(\sigma_j)$ when the mean cost of every round with $n'$ uniform points is at most $e(n')$ | Lemma S (a) | **[machine-checked]** |
| `NcountL`, `not_mem_ExcL_iff`, `NcountL_ofFn` | $N$ for a list of points; the list is outside `ExcL` iff $N < B$ | $N_j$ | **[machine-checked]** |
| `avg_NcountL_le` | $\mathbb E[N] \le L^3q^6\epsilon^n$ over $n$ uniform points | "by Lemma D4(1)'s count" | **[machine-checked]** |
| `ladderPot`, `ladderPot_step` | for a level: if $T < 1$ then the points held are outside `ExcL` for the current word, in the form `lemmaF_round` takes, and the next message makes $T \ge 1$ with probability less than $\tau$ | Lemma S (b), (c) | **[machine-checked]** |
| `ladderPot_init` | $\Pr[T \ge 1$ after batch 1$] \le (L^3q^6/B)\sum_j\tau^{-j}\epsilon^{\sigma_{j+1}}$ | Lemma S (a) | **[machine-checked]** |
| `GoodS`, `dens_not_goodS_le` | the first batch is not good with probability at most $\binom L2\epsilon^{\sigma_1} + \frac{L^3q^6}{B}\sum_{j<\ell}\tau^{-j}\epsilon^{\sigma_{j+1}}$ | the point message of Theorem D$_S$ | **[machine-checked]** |

### 2.6 The parameter claim

All by `norm_num` on explicit numerals (no `decide`, no `native_decide`). $q = 2^{128}$, $L = 2^{40}$, $K_0 = 2^{137}$, $M = 2^{129}$, $B = K_0(K_0-1)(K_0-M)$, $\tau = 2^{-119}$, $\epsilon = (2^{24} + 5 + 2^6 - 1)/q$.

| Lean statement | content | status |
| --- | --- | --- |
| `point_error_level0_arith` | $\bigl[\binom L2 + \frac{L^3q^6}{B}\sum_{j<6}\tau^{-j}\bigr]\epsilon^{12} \le 2^{-110}$ | **[machine-checked]** |
| `point_error_level0_arith_11` | the same expression with $\epsilon^{11}$ exceeds $2^{-110}$: 12 is the least number of points for which the bound is met (note 14 section 7.4, the entry 12) | **[machine-checked]** |
| `held_ladder0`, `ladder_error_level0_arith` | the schedule $6{+}1{+}1{+}2{+}1{+}1$ holds 6, 7, 8, 10, 11, 12 points at the six rounds, and $\binom L2\epsilon^6 + \frac{L^3q^6}{B}\sum_{j<6}\tau^{-j}\epsilon^{\sigma_{j+1}} \le 2^{-110}$ | **[machine-checked]** |
| `fold_error_arith`, `fold_error_last_arith` | $(K_0 - 1)/q^2 + \tau \le 2^{-118}$ and $(K_0 - 1)/q^2 \le 2^{-119}$ | **[machine-checked]** |
| `level0_point_error` | over a field with $2^{128}$ elements, for a level with 6 lane variables and degree bound $2^{24} + 5$ whose words all have at most $2^{40}$ list members: 12 uniform points are not good with probability at most $2^{-110}$ | **[machine-checked]** |
| `level0_ladder_error` | the same for the 6 points of the first batch of the ladder | **[machine-checked]** |

### 2.7 The main statements, as Lean checks them

```lean
theorem lemmaP (D : Finset K) (O : K → ι → K) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {E : ℕ} (hE : ∀ u, ex u ≤ E) {L : ℕ}
    (hL : (listW D O d A).card ≤ L) (s : ℕ) :
    dens (fun z : Fin s → K × K => z ∈ NonSep (listW D O d A) ex s) ≤
      (L.choose 2 : ℚ) * (((d + E : ℕ) : ℚ) / Fintype.card K) ^ s

theorem pinned_unique {S : Finset (ι → K[X])} {ex : ι → ℕ} {s : ℕ} {z : Fin s → K × K}
    (hz : z ∉ NonSep S ex s) (y : Fin s → K) {U U' : ι → K[X]} (hU : U ∈ S) (hU' : U' ∈ S)
    (h : ∀ i, evL ex (z i) U = y i) (h' : ∀ i, evL ex (z i) U' = y i) : U = U'

theorem levelPot_step (hτ : 0 < τ) {z : Fin s → K × K} {k r : ℕ} {O : Word K (r + 1)}
    (h : levelPot τ D d thr s B z k (r + 1) O < 1) :
    z ∉ ExcL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) s B ∧
      dens (fun c : K × K => 1 ≤ levelPot τ D d thr s B z (k + 1) r (foldW O c)) < τ

theorem levelPot_init (hτ : 0 ≤ τ) (hB : 0 < B) {L : ℕ} (k r : ℕ)
    (hL : ∀ k' r', k' + r' = k + r → k < k' → ∀ O' : Word K r',
      (listW D O' d (thr k')).card ≤ L) (O : Word K r) :
    dens (fun z : Fin s → K × K => 1 ≤ levelPot τ D d thr s B z k r O) ≤
      (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + (2 ^ (k + r) - 2 ^ (k + 1)) : ℕ) : ℚ) / Fintype.card K) ^ s / B *
          ∑ j ∈ range r, τ⁻¹ ^ j

theorem dens_not_good_le (hτ : 0 ≤ τ) (hB : 0 < B) {L ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hL : ∀ k r, k + r = ℓ → ∀ O' : Word K r, (listW D O' d (thr k)).card ≤ L)
    (O : Word K ℓ) :
    dens (fun z : Fin s → K × K => ¬ Good τ D d thr s B ℓ O z) ≤
      ((L.choose 2 : ℚ) + (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 / B *
          ∑ j ∈ range ℓ, τ⁻¹ ^ j) * (((d + 2 ^ ℓ - 1 : ℕ) : ℚ) / Fintype.card K) ^ s

theorem ladderPot_step (hτ : 0 < τ) (hB : 0 < B) {k r : ℕ} {O : Word K (r + 1)}
    {pts : List (K × K)} (h : ladderPot τ D d thr bt B k (r + 1) (O, pts) < 1) :
    (fun i : Fin pts.length => pts.get i) ∉
        ExcL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) pts.length B ∧
      dens (fun m : (K × K) × (Fin (bt k) → K × K) =>
        1 ≤ ladderPot τ D d thr bt B (k + 1) r (foldW O m.1, pts ++ List.ofFn m.2)) < τ

theorem level0_point_error (hq : Fintype.card K = 2 ^ 128) (D : Finset K) (thr : ℕ → ℕ)
    (hL : ∀ k r, k + r = 6 → ∀ O' : Word K r,
      (listW D O' (2 ^ 24 + 5) (thr k)).card ≤ 2 ^ 40) (O : Word K 6) :
    dens (fun z : Fin 12 → K × K => ¬ Good (1 / 2 ^ 119) D (2 ^ 24 + 5) thr 12
      (2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129)) 6 O z) ≤ 1 / 2 ^ 110
```

Reading. In `levelPot_step` the binder order is the protocol's: `z` and the current word `O` are given, the hypothesis is about them only, and the conclusion quantifies the next challenge `c`. The arguments of `levelPot` are the constants of the level, the points, the indices and the word: there is no place where a prover message could enter, and the next word is `foldW O c`. The first conjunct is, verbatim, the hypothesis `hz` of `DeepFold.lemmaF_round` (and of `Rounds.fold_transition`) for the halves of `O`, with `ex = exL (k+1) r` and `w = 2^k`. In `levelPot_init` and `dens_not_good_le` the hypothesis `hL` is $\mathrm{ListBound}$ for the words the level can reach, and `listBound_level` derives it from note 14's form.

## 3. Where the Lean statements differ from the notes

None of these weakens what is proved.

1. **The potential is defined by its recursion, and the notes' sum is a theorem.** `pot` is $T(a) = \text{cost}(a) + \tau^{-1}\mathbb E_c[T(\mathrm{fold}(a, c))]$, and `potT_eq_sum`, `levelPot_eq_sum` show $T = \sum_j\tau^{-j}\pi_j$. The probabilities $\pi_j$ are iterated means over one challenge at a time; `probBad_eq_card` and `levelPot_eq_sum_card` show that $\pi_j$ is the number of sequences of $j$ challenges leading to an exceptional word over $q^{2j}$. I did not state $\pi_j$ as the cardinality of a subset of $(K^2)^j$ with an explicit "fold by a vector of challenges", because the word types change with the round; the recursive count `badSeqs` is that cardinality organised by the first challenge.
2. **Indices.** The Lean uses `k` (rounds played) and `r` (rounds to come) in place of $k$ and $\ell$; note 14's $\pi^{(k)}_j$ is `probBad … (j - k - 1) k (ℓ - k)`. The exponent of $\tau$ is the number of challenges between the state and the round, as in the note.
3. **The bound of Lemma T (a) is asked only where it is used.** The hypothesis of `potT_init_const` ranges over the rounds still to come (`k ≤ k'` and `k' + r' + 1 = k + r`) and, in `levelPot_init`, over the folds of words folded more than `k` times. The note asks it "for every $j$ and every word of the shape of round $j$", which is the same thing for $k = 0$.
4. **A bound per round.** `potT_init` and `potS_init` take a bound that may depend on the round; the notes' constant $\varepsilon_\ast$ is the corollary `potT_init_const`.
5. **Any threshold $B > 0$.** The statements hold for every threshold `B` of the triple count, with the constant $L^3q^6/B$. The notes' $B = K_0(K_0 - 1)(K_0 - M)$ is used only in `Params.lean`. Lemma S is therefore checked with note 14's constant (as the referee restated it) and with note 15's $\lceil K_0^3/4\rceil$ alike.
6. **Abstract exponents in Lemma P.** `lemmaP` takes any injective exponent map bounded by `E`, with $\epsilon = (d + E)/q$; `dens_not_good_le` instantiates it at $e_0$, where $E = 2^\ell - 1$. For the rounds, $E = 2^\ell - 2$ and `DeepFold`'s $(d + 1 + E)/q$ is the same $\epsilon$.
7. **Points on the ladder are a list.** The points held are `pts : List (K × K)` and a fresh batch is appended; `ExcL` is taken at the vector `fun i : Fin pts.length => pts.get i`. `NcountL_ofFn` and `avg_ofFn_append` connect this with vectors `Fin n → K × K`.
8. **The batch that rides with the last fold challenge is ignored.** After the last round the potential is zero whatever was sampled, so `bt (ℓ - 1)` plays no role; note 15 sends no batch there.
9. **Counting statements.** Probabilities are `dens` (a cardinality over the size of the type). Lemma P also has an integer form (`card_nonSep_le`).

## 4. What formalizing showed about the hand proofs

No error and no missing hypothesis. Lemmas P, T and S go through as written, and the referee's reading of the potential as a legitimate state (note 20 section 3.2) is now a checked fact: the potential is a function of the committed word, the points and the challenges so far. The observations, in decreasing order of interest:

1. **Lemma S with one batch is not Lemma D6 "word for word"** (note 15, the sentence after Lemma S). The potential of Lemma S sums $\mathbb E[N_j]/\Theta$ and that of Lemma D6 and Lemma T sums $\Pr[N_j \ge \Theta]$. They are different functions; the first dominates the second by Markov, and both satisfy the same three statements with the same bounds, because Lemma F (1) bounds the probability by that very expectation. Nothing depends on the sentence. In the Lean they are the same `pot` with two different costs (`potT` with the indicator, `potS` with $N/B$).
2. **Hypotheses that are never used in these lemmas.** $\tau < 1$: (a) needs $\tau \ge 0$ and (b) needs $\tau > 0$, nothing else. $K_0 > M$: Lemma T (a) and Lemma S (a), (c) need only that the threshold of the count is positive; $K_0 > M$ matters in Lemma F (2), not here. Any relation between $A$, $d$ and $n$: Lemma P uses only the degree bound and the size of the list. The size of the challenge space is not used in (b) either.
3. **The Markov step is an identity followed by one inequality.** `avg_pot_step`: $\mathbb E_c[T_{k}] = \tau\,(T_{k-1} - \pi^{(k-1)}_k)$ exactly, as the note writes, and strictness of "$< \tau$" comes from $T_{k-1} < 1$ and $\tau > 0$.
4. **(b) and (c) of Lemma S and (b) of Lemma T are one statement** about a nonnegative cost and its potential (`pot_step`), and the martingale language of note 15 is not needed: the proof is the recursion and Markov. The only place where independence of the batches is used is (a), through `avg_ofFn_append`.
5. **Lemma T (a) needs the bound for every word of each shape**, as the note says and the referee stresses: the exchange of the two means (`avg_comm`) applies the bound to the folded word for each fixed challenge prefix, and the induction in `avg_potT_le` cannot be run with a bound for the committed word alone. This is the reason $\mathrm{ListBound}$ is stated for every lane count.
6. **$\epsilon$ is tight at its two uses.** With $E = 2^\ell - 1$ for $e_0$ and degree $d$ (Lemma P), and $E = 2^\ell - 2$ for $e_1$ and degree $d + 1$ (round 1), both give exactly $(d + 2^\ell - 1)/q$; later rounds have smaller exponents and the Lean bounds them by the same number.
7. **The number 12 at level 0 is exact for the stated bound**: the bound is $2^{-176}$ at 12 points and $2^{-72}$ at 11, so the requirement "at most $2^{-110}$" is met with 66 bits to spare and fails by 38 bits one point lower.

## 5. What is not machine-checked here

- **The transitions M0 to M5, the state function, Theorem D', Theorem K and the extractor**: library `Rounds` (researcher 32), which uses `NonSep`, `listW` and `pinned_unique` from here. That M0 is "Lemma P and Lemma T (a), and the old condition does not involve the new points" is `dens_not_good_le` for the first half; composing it with the rest of the state is not in this note. **[not formalized here]**
- **$\mathrm{ListBound}$** is a hypothesis (`hL`) of `levelPot_init`, `dens_not_good_le`, `ladderPot_init`, `level0_point_error`. Its instances (Johnson, counting, the interleaving reductions of the library `Interleave`) are not connected to `hL` here. **[not formalized here]**
- **$\pi_j$ as the cardinality of a set of challenge vectors** with an explicit fold by a vector (item 1 of section 3). **[not formalized]**
- **The comparison of the two potentials** (`levelPot` at most `ladderPot` with empty later batches). True by Markov, not stated. **[not formalized]**
- **The general schedule of note 15 section 6.3** (batches with their own verifier message and allowance $\delta'$) and the optimality of the ladder. **[not formalized]**
- **Theorem D$_S$ beyond its point message**: the claim part of the ladder (new answers only shrink the set the invariant quantifies over) and the level exit with $\sigma_\ell$ converted claims. **[not formalized]**
- **Other levels and other list budgets** of the tables of note 14 section 7.4 and note 20 section 6.3: only level 0 at $L = 2^{40}$ (one batch and ladder) is checked. The statements `dens_not_good_le` and `dens_not_goodS_le` are general; each further row is one `norm_num`. **[not formalized]**
- **The query, batching and tail terms**, the grinds, and the Fiat-Shamir compilation. **[not formalized here]**

## 6. Reproduction

`lean/Protocol/README.md`. On a build host: `cd doc/whir_soundness_gap_notes/lean && lake exe cache get && lake build DeepFold Protocol`. The directories that were checked are `h4:/data/whir_lean_scratch_31/proj` (module by module, script `r31_final_check.sh` one directory up) and `h4:/data/whir_lean_scratch_31/lakeproj` (Lake, log `lake-build.log` one directory up).
