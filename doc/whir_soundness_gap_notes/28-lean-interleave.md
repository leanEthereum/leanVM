# 28. The interleaving reductions, machine-checked in Lean 4

Researcher 28. This note says exactly what of the interleaving reductions (note 14 section 7: Theorem I and Proposition R2'; note 13 sections 3.4 and 3.5: Propositions 3.4 and 3.5) is now checked by Lean 4 with Mathlib, what is not, and how to reproduce the check. The sources are the library `Interleave` in `lean/` (about 1800 lines of Lean in nine files, `lean/Interleave/README.md` for the build), beside the library `DeepFold` of note 22 and with its conventions. Tags: **[machine-checked]** means the statement is a Lean theorem that compiles with no `sorry` and depends on Lean's three axioms only; **[not formalized]** means no Lean statement exists.

## 0. Summary

1. **Theorem I of note 14 is machine-checked in full**: the general recursion $N(\Phi) = N(\Phi - g) + (L-1)N(\lfloor\Phi/2\rfloor)$ for any code with an agreement bound, any alphabet, any finite number of lanes (`interleave_listBound`); the four special cases $1$, $L$, $2L - 1$, $L^2 + L - 1$ with hypotheses free of division (`interleave_listBound_one`, `_same`, `_two_mul`, `_sq`); and both closed forms $\sum_{k \le \min(b,r)}\binom bk(L-1)^k$ and $\binom{b+r}{r}L^r$ (`interleave_listBound_closed`, `interleave_listBound_choose`).
2. **Proposition R2' of note 14 is machine-checked with its exact constant** $L/(1 - L/|K|^s)$, for any code given by a generator matrix over $K$ and values in any finite $K$-vector space (`descent`, `descent_div`), and for Reed-Solomon codes in the words of the notes: lists of tuples of polynomials over an extension, from the single-lane hypothesis $\mathrm H_K$ (`rs_descent₁`, `rs_descent₁_div`) or from a hypothesis on $F_0^{s}$-valued words (`rs_descent`). Proposition 3.4 of note 13 is the first half of its conclusion.
3. **Proposition 3.5 of note 13 is machine-checked** in a slightly sharper form (`listBound_prod`, `listBound_prod_self`, `listBound_prod_two_mul`).
4. **The reductions are composed and linked to the DEEP fold lemma.** `rs_interleave` and its special cases are Theorem I for Reed-Solomon codes with lanes and values in an extension, from $\mathrm H_K$ alone (this includes the remark of section 7 that an $h$-lane $E$-valued word is a $2h$-lane $K$-valued word with the same list). `rs_listBound_min` is the reduction of section 7.3. `card_fullT_filter_le` derives the hypothesis `hΛ` of `DeepFold.lemmaF_exc` from the list bound, and `lemmaF_exc_of_HK` is Lemma F (1) of note 14 with $\Lambda = 2L - 1$ from $\mathrm H_K$.
5. **No error was found in the hand proofs.** Two things worth knowing came out (section 5): the hypothesis $L \le |K|^s/4$ of Proposition R2' can be weakened to $L \le |K|^s/2$ (so the caps $2^{62}$ and $2^{126}$ of section 7.3 can be $2^{63}$ and $2^{127}$), and Theorem I as written needs $L \ge 1$ (for $L = 0$ its integer recursion goes negative; this never happens for a nonempty code with $A \le n$).
6. **Checked on `h4`** with Lean 4.36.0 and Mathlib `v4.36.0` (revision `fc4f59e577`), twice: file by file against the Mathlib already built on the host, and as a Lake build of the library. Nothing was installed or built on the Mac.
7. **Not formalized**: the numbers of section 7.4, the per-level statement $\mathrm{ListBound}_i$ with the protocol's degrees and thresholds, the tightness remarks, and the comparison with [ABF26] and ArkLib. Section 6.

## 1. How it was checked

Host `h4`, scratch directory `/data/whir_lean_scratch_28` (created for this, safe to delete). Lean `leanprover/lean4:v4.36.0`, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, Lake `5.0.0-src+611c117`; Mathlib tag `v4.36.0`, revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, as in `lean/lake-manifest.json`.

- Run 1: each module compiled in dependency order with `lean -o` and `-DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false`, from an empty output directory, against the Mathlib already built in `/data/lean436/formal/Statement/.lake/packages` (read only). No output: no error, no warning. `Interleave/Bridge.lean` imports `DeepFold.Main`, so the nine `DeepFold` modules it needs were compiled the same way in the same scratch directory, from the repository's sources.
- Run 2: the whole of `lean/` copied to `/data/whir_lean_scratch_28/lakeproj`, with `.lake/packages` copied from the Lake project of note 22 (`/data/whir_deepfold_lean_scratch/lakeproj`, same `lake-manifest.json` and toolchain, so nothing was downloaded), then `lake build Interleave` on 8 cores at nice 10: `Build completed successfully (18288 jobs)`. `lakefile.toml` sets `warningAsError`. The only messages are Lake's advisory that `Interleave/Basic.lean`, `DeepFold/Basic.lean` and `DeepFold/Counting.lean` import `Mathlib` without the module system. The log is `/data/whir_lean_scratch_28/lake-build.log`.
- No `sorry`, `admit`, `axiom` or `native_decide` occurs in the sources. `Interleave/Axioms.lean` runs `#print axioms` under `#guard_msgs` on 62 statements and `Interleave/Bridge.lean` on its 3, which covers every statement named in section 3: each depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else (five statements about the recursion alone need only `propext` and `Quot.sound`), and the build fails if that changes.
- The files in the repository and the files built on `h4` are identical (SHA-256 of every file of `lean/Interleave/` and of `lean/Interleave.lean`, compared after the last build).

One incident. The session scratchpad on the Mac is shared by the researchers of the swarm, and my helper script there (`chk.sh`) was overwritten by researcher 32's script of the same name while I worked. One invocation of mine therefore ran their script: it synced `lean/Rounds` and `lean/Rounds.lean` to `/data/whir_lean_scratch_32/proj` (what their script does), compiled the nine `DeepFold` modules into `/data/whir_lean_scratch_32/proj/build/DeepFold` from the `DeepFold` sources already there, and created an empty directory `/data/whir_lean_scratch_32/proj/build/Interleave`. I did nothing else there and did not clean up, so as not to write to that directory again. My own runs above were redone from an empty output directory with a script under a private name.

## 2. Definitions

All in `Interleave/Basic.lean`, `Interleave/Projection.lean` and `Interleave/ReedSolomon.lean`.

| Lean | meaning |
| --- | --- |
| `agr D w c` | for words `w c : ι → α` and a finite set `D` of coordinates: the coordinates of `D` where `w` and `c` agree. `ι` is any type; take `D = Finset.univ` for a finite index type |
| `AgreeLE D C d` | two distinct words of the code `C : Set (ι → α)` agree on at most `d` coordinates of `D` |
| `ListBound D C a L` | for every word `w`, every finite set of codewords each agreeing with `w` on at least `a` coordinates of `D` has at most `L` elements |
| `interleave m C` | the interleaved code with lanes `m`: the words `ι → m → α` all of whose lanes are in `C`. Its alphabet is `m → α`, so `agr` for it is the set of coordinates where all lanes agree, and `ListBound D (interleave m C) a L` is the interleaved list bound |
| `treeN L g P` | the recursion $N_{L,g}(P)$ of Theorem I, with $L - 1$ truncated at $0$ |
| `enc G m` | the word of a message `m : κ → V` under a generator `G : ι → κ → K`: `enc G m i = ∑ k, G i k • m k`, for any `K`-module `V` |
| `GenListBound G D V a L` | every `V`-valued word has at most `L` messages whose words agree with it on at least `a` coordinates of `D` |
| `RSListBound₁ D d a L` | $\mathrm H_K$ of note 14 section 7.3: for `D : Finset K`, every word `K → K` has at most `L` polynomials of `K[X]` of degree at most `d` agreeing with it on at least `a` points of `D` |
| `RSListBound D F lanes d a L` | $\mathrm{ListBound}$ of the notes: for a `K`-algebra `F` and a type `lanes`, every word `K → lanes → F` has at most `L` tuples `lanes → F[X]` of degree at most `d` agreeing with it, in all lanes, on at least `a` points of `D` (the tuple is evaluated at `algebraMap K F x`) |

Lists are finite sets of codewords, of messages or of polynomials, and "at most $L$" is said of every such finite set; this avoids any finiteness assumption on the alphabet. For Reed-Solomon codes lists are lists of polynomials, as in the notes, not of their words.

## 3. What is stated and checked

### 3.1 Theorem I (note 14, section 7.1)

Hand statement: $\mathcal C \subseteq \Sigma^n$ with two distinct codewords agreeing on at most $d$ coordinates, $d < A \le n$, $g = A - d$, every word has at most $L$ codewords within agreement $A$. Then for every $m \ge 1$ every word of the $m$-fold interleaved code has at most $N(n - d)$ tuples within agreement $A$, with $N(\Phi) = 1$ for $\Phi < 2g$ and $N(\Phi) = N(\Phi - g) + (L-1)N(\lfloor\Phi/2\rfloor)$ otherwise; $N(n - d) \le \sum_{k \le \min(b,r)}\binom bk(L-1)^k \le \binom{b+r}{r}L^r$; in particular $1$, $L$, $2L - 1$, $L^2 + L - 1$ for $A$ above $(n+d)/2$, $(n+2d)/3$, $(n+3d)/4$, $(n+4d)/5$.

| Lean statement | content | status |
| --- | --- | --- |
| `treeN_mono`, `treeN_pos` | $N$ is non-decreasing and positive | **[machine-checked]** |
| `treeN_eq_L`, `treeN_eq_two_mul`, `treeN_eq_sq` | for $L \ge 1$: $N = L$ on $[2g, 3g)$, $2L - 1$ on $[3g, 4g)$, $L^2 + L - 1$ on $[4g, 5g)$ | **[machine-checked]** |
| `tree_core` | the claim of the proof: below a node with agreement set $T$ there are at most $N(\lvert T\rvert - d)$ leaves (Facts 1 to 4 are steps of its proof) | **[machine-checked]** |
| `interleave_listBound` | **Theorem I**: `AgreeLE D C d → d < a → ListBound D C a L → ∀ m [Finite m], ListBound D (interleave m C) a (treeN L (a - d) (D.card - d))` | **[machine-checked]** |
| `interleave_listBound_one` | if $n + d < 2a$ the interleaved list has at most one element (no list hypothesis, any lanes) | **[machine-checked]** |
| `interleave_listBound_same` | if $n + 2d < 3a$: `ListBound D (interleave m C) a L` | **[machine-checked]** |
| `interleave_listBound_two_mul` | if $n + 3d < 4a$: bound $2L - 1$ | **[machine-checked]** |
| `interleave_listBound_sq` | if $n + 4d < 5a$: bound $L^2 + L - 1$ | **[machine-checked]** |
| `ListBound.of_interleave`, `interleave_listBound_iff` | interleaving cannot shrink lists, so for $n + 2d < 3a$ the interleaved and single-lane list bounds are equivalent | **[machine-checked]** (not in the note) |
| `AgreeLE.interleave`, `AgreeLE.listBound_one` | the interleaved code has the same agreement bound; unique decoding | **[machine-checked]** |
| `treeSum_eq_min`, `treeN_le_treeSum`, `treeN_le_closed` | $N(n - d) \le \sum_{k \le \min(b,r)}\binom bk(L-1)^k$ with $b = \lfloor(n-a)/(a-d)\rfloor$, $r = \lfloor\log_2\lfloor(n-d)/(a-d)\rfloor\rfloor$ | **[machine-checked]** |
| `sum_choose_le`, `treeSum_le_choose_mul_pow`, `treeN_le_choose_mul_pow` | for $L \ge 1$ the sum is at most $\binom{b+r}{r}L^r$ | **[machine-checked]** |
| `interleave_listBound_closed`, `interleave_listBound_choose` | Theorem I with each closed form as the bound | **[machine-checked]** |

Here $n$ is `D.card`, and the three special cases after the first assume at least one lane (`[Nonempty m]`), which is used only when $L = 0$.

### 3.2 Proposition R2' (note 14, section 7.2) and Proposition 3.4 (note 13)

Hand statement: $D \subseteq K$, $s \ge 1$, $\Lambda_{K^s}(A) \le L$ with $L \le |K|^s/4$. Then for every finite-dimensional $K$-vector space $V$, $\Lambda_V(A) \le L/(1 - L/|K|^s)$.

| Lean statement | content | status |
| --- | --- | --- |
| `two_mul_card_le_image_add_collisions` | for a map $f$ on a finite set $S$: $2\lvert S\rvert \le 2\lvert f(S)\rvert + \#\{$ordered pairs of distinct elements with the same image$\}$ | **[machine-checked]** |
| `card_vanish_mul_le` | a nonzero vector of $V$ is killed by at most a fraction $1/\lvert W\rvert$ of the linear maps $V \to W$ | **[machine-checked]** |
| `exists_linearMap_collisions`, `exists_linearMap_image` | some linear map $V \to W$ identifies at most $\lvert S\rvert(\lvert S\rvert - 1)/\lvert W\rvert$ ordered pairs of a finite set $S$ of $V$-valued functions | **[machine-checked]** |
| `map_enc` | a $K$-linear map on the values commutes with the encoding | **[machine-checked]** |
| `descent_ineq` | for every list $S$ of a $V$-valued word: $2q\lvert S\rvert \le 2qL + \lvert S\rvert(\lvert S\rvert - 1)$, $q = \lvert W\rvert$ (the note's $\ell' - \binom{\ell'}2/q \le L$) | **[machine-checked]** |
| `descent_arith` | the arithmetic: if this holds for every subset of $S$ and $2L \le q$, then $\lvert S\rvert \le 2L - 1$ and $\lvert S\rvert(q - L) \le Lq$ | **[machine-checked]** |
| `descent` | **Proposition R2'** for a generated code: `GenListBound G D W a L → 2 * L ≤ Fintype.card W →` every list `S` of a word with values in a finite `K`-module `V` has `S.card ≤ 2 * L - 1 ∧ S.card * (Fintype.card W - L) ≤ L * Fintype.card W` | **[machine-checked]** |
| `descent_div` | the same as $\lvert S\rvert \le L/(1 - L/\lvert W\rvert)$ in $\mathbb Q$ | **[machine-checked]** |

The first conjunct, $\lvert S\rvert \le 2L - 1 < 2L$, is Proposition 3.4 of note 13 (with $L = 2^b$: fewer than $2^{b+1}$), under the weaker condition $b \le 64s - 1$.

### 3.3 The same for values in a finite-dimensional space, and for Reed-Solomon codes

| Lean statement | content | status |
| --- | --- | --- |
| `gen_interleave` | Theorem I for a generated code: if the words of two distinct $K$-valued messages agree on at most $d$ coordinates, $d < a$ and `GenListBound G D K a L`, then `GenListBound G D V a (treeN L (a - d) (D.card - d))` for every finite-dimensional $K$-vector space $V$ ($K$ any field). The proof takes a basis of $V$: a $V$-valued word is an interleaved $K$-valued word with one lane for each basis vector, with the same list (section 7, first paragraph) | **[machine-checked]** |
| `gen_interleave_same`, `gen_interleave_two_mul`, `gen_interleave_sq`, `gen_unique` | its special cases, and unique decoding | **[machine-checked]** |
| `rs_agree_le` | two distinct polynomials of degree at most $d$ agree on at most $d$ points | **[machine-checked]** |
| `rsListBound₁_iff`, `rsListBound_iff` | $\mathrm H_K$ and $\mathrm{ListBound}$ are the list bounds of the code generated by $G(x, k) = x^k$, for values in $K$ and in $F^{\mathrm{lanes}}$ | **[machine-checked]** |
| `rs_interleave` | **Theorem I for Reed-Solomon codes**: `RSListBound₁ D d a L → d < a → RSListBound D F lanes d a (treeN L (a - d) (D.card - d))`, for a `K`-algebra `F` finite as a `K`-module and finitely many lanes | **[machine-checked]** |
| `rs_interleave_same`, `rs_interleave_two_mul`, `rs_interleave_sq`, `rs_interleave_closed` | bounds $L$, $2L - 1$, $L^2 + L - 1$ under $n + 2d < 3a$, $n + 3d < 4a$, $n + 4d < 5a$, and the closed form | **[machine-checked]** |
| `rs_descent₁`, `rs_descent₁_div`, `rs_descent₁_listBound` | **Proposition R2' from $\mathrm H_K$** ($s = 1$): if $2L \le \lvert K\rvert$, every list $S$ of a word with values in $F^{\mathrm{lanes}}$, $F$ a finite `K`-algebra, has $\lvert S\rvert \le 2L - 1$ and $\lvert S\rvert(\lvert K\rvert - L) \le L\lvert K\rvert$ | **[machine-checked]** |
| `rs_descent`, `rs_descent_div` | **Proposition R2', general**: the hypothesis is `RSListBound D F₀ lanes₀ d a L` with $2L \le q = \lvert F_0\rvert^{\lvert\mathrm{lanes}_0\rvert}$ (for $F_0 = K$ and $s$ lanes this is $\Lambda_{K^s}$; for $F_0 = E$ and one lane it is $\mathrm H_E$) | **[machine-checked]** |
| `rs_listBound_min` | section 7.3: from $\mathrm H_K$ with $2L \le \lvert K\rvert$ and $d < a$, the bound $\min(N(n - d),\, 2L - 1)$ for all lanes and extensions | **[machine-checked]** |
| `rsListBound₁_one` | $\mathrm H_K$ holds with $L = 1$ when $n + d < 2a$ | **[machine-checked]** |
| `RSListBound.image` | the same bound with the points and the word in $F$: points `D.image (algebraMap K F)`, word `F → lanes → F` (the shape of `DeepFold.agrL`) | **[machine-checked]** |

### 3.4 Proposition 3.5 of note 13 (two lanes against one)

Hand statement: $\Lambda_{K^2}(T) \le \Lambda_K(T)(1 + \Lambda_K(2T - d))$, and $\Lambda_{K^2}(T) \le 2\Lambda_K(T)$ for $T > (n + 3d)/4$.

| Lean statement | content | status |
| --- | --- | --- |
| `listBound_prod` | for two codes $C_1, C_2$ (one for each lane), $C_2$ with agreement bound $d$: `ListBound D C₁ a L₁ → ListBound D C₁ (2 * a - d) L₁' → ListBound D C₂ a L₂ → ListBound D (prodCode C₁ C₂) a (L₁ + L₁' * (L₂ - 1))` | **[machine-checked]** |
| `listBound_prod_self` | $C_1 = C_2$: the bound $L(1 + L')$ of the note | **[machine-checked]** |
| `listBound_prod_two_mul` | for $n + 3d < 4a$: $2L - 1$ | **[machine-checked]** |

### 3.5 The link with the DEEP fold lemma (`Interleave/Bridge.lean`)

| Lean statement | content | status |
| --- | --- | --- |
| `card_fullT_filter_le` | `RSListBound D₀ E ι d A Λ` implies the hypothesis `hΛ` of `DeepFold.lemmaF_exc` for the points `D₀.image (algebraMap K E)`: for every challenge `c`, at most `Λ` candidates `(c, P)` in `DeepFold.fullT` | **[machine-checked]** |
| `lemmaF_exc_of_rsListBound` | Lemma F (1) of note 14 with `hΛ` replaced by `RSListBound D₀ E ι d A Λ` | **[machine-checked]** |
| `lemmaF_exc_of_HK` | Lemma F (1) from `RSListBound₁ D₀ d A L` (single words with values in the small field), `d < A` and $n + 3d < 4A$: the bound $(2L - 1)^3q^6\epsilon^s/B$ | **[machine-checked]** |

This is the composition the paper needs: the only list hypothesis left in the bound on the exceptional set is $\mathrm H_K$.

### 3.6 Instantiation (`Interleave/Axioms.lean`)

`K64` is `GaloisField 2 64` and `E128` is Mathlib's `FiniteField.Extension K64 2 2`, a quadratic extension of it with its `K64`-algebra structure; `natCard_E128` proves it has $2^{128}$ elements. Four lanes.

| Lean statement | content | status |
| --- | --- | --- |
| `deployed_unique` | unconditional: for every `D : Finset K64` and $d < a$ with $n + d < 2a$, `RSListBound D E128 (Fin 4) d a 1`. It is `rs_interleave_same` applied to `rsListBound₁_one`, so every hypothesis of the reduction, the list hypothesis included, is satisfiable at the deployed fields | **[machine-checked]** |
| `deployed_two_mul` | from `RSListBound₁ D d a L`, $d < a$, $n + 3d < 4a$: `RSListBound D E128 (Fin 4) d a (2 * L - 1)` | **[machine-checked]** |
| `deployed_descent` | from `RSListBound₁ D d a L` and $L \le 2^{63}$: every list `S` of a word `K64 → Fin 4 → E128` has `S.card ≤ 2 * L - 1 ∧ S.card * (2 ^ 64 - L) ≤ L * 2 ^ 64` | **[machine-checked]** |

## 4. The end statements, as Lean checks them

```lean
theorem interleave_listBound (hC : AgreeLE D C d) (hda : d < a) (hL : ListBound D C a L)
    (m : Type*) [Finite m] :
    ListBound D (interleave m C) a (treeN L (a - d) (D.card - d))

theorem interleave_listBound_same (hC : AgreeLE D C d) (hda : d < a) (hL : ListBound D C a L)
    (h3 : D.card + 2 * d < 3 * a) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a L

theorem interleave_listBound_two_mul (hC : AgreeLE D C d) (hda : d < a)
    (hL : ListBound D C a L) (h4 : D.card + 3 * d < 4 * a) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a (2 * L - 1)

theorem descent [Finite V] [Fintype W] {G : ι → κ → K} {D : Finset ι} {a L : ℕ}
    (hL : GenListBound G D W a L) (h2 : 2 * L ≤ Fintype.card W) (w : ι → V)
    (S : Finset (κ → V)) (hS : ∀ m ∈ S, a ≤ (agr D w (enc G m)).card) :
    S.card ≤ 2 * L - 1 ∧ S.card * (Fintype.card W - L) ≤ L * Fintype.card W

theorem rs_interleave (hL : RSListBound₁ D d a L) (hda : d < a) :
    RSListBound D F lanes d a (treeN L (a - d) (D.card - d))

theorem rs_descent₁ (hL : RSListBound₁ D d a L) (h2 : 2 * L ≤ Fintype.card K)
    (w : K → lanes → F) (S : Finset (lanes → F[X]))
    (hS : ∀ P ∈ S, (∀ u, (P u).natDegree ≤ d) ∧
      a ≤ (agr D w (fun x u => (P u).eval (algebraMap K F x))).card) :
    S.card ≤ 2 * L - 1 ∧ S.card * (Fintype.card K - L) ≤ L * Fintype.card K
```

In `interleave_listBound`, `ι` and `α` are arbitrary types, `D : Finset ι`, `C : Set (ι → α)`. In `descent`, `K` is a field, `V` and `W` are `K`-modules, `κ` a finite type. In `rs_interleave`, `K` is any field, `D : Finset K`, `F` a commutative ring and `K`-algebra with `Module.Finite K F`, `lanes` a finite type. In `rs_descent₁`, `K` is a finite field and `F` a finite `K`-algebra.

## 5. What formalizing showed about the hand proofs

No error and no gap in the arguments. In decreasing order of interest:

1. **Proposition R2' holds under $L \le |K|^s/2$, not only $L \le |K|^s/4$.** The proof's contradiction at $\ell' = 2L$ is $|K|^s \le 2L - 1$, which contradicts $2L \le |K|^s$ already. The Lean statement assumes `2 * L ≤ Fintype.card W` and gives both $\lvert S\rvert \le 2L - 1$ and $\lvert S\rvert \le L/(1 - L/q)$. So in section 7.3 the caps $L \le 2^{62}$ (from $K$-valued words) and $L \le 2^{126}$ (from $E$-valued words) can be $2^{63}$ and $2^{127}$, and Proposition 3.4 of note 13 holds for $b \le 64s - 1$. At the new edge $L = |K|^s/2$ the factor is 2; at $L = |K|^s/4$ it is $4/3$.
2. **Theorem I needs $L \ge 1$ as written.** Over the integers the recursion with $L = 0$ gives $N = 0$ on $[2g, 3g)$ and $N = -1$ on $[3g, 4g)$, and "the number of leaves below a node is at most $N(\Phi)$" is then false ($0 \not\le -1$); "N is non-decreasing" also needs $L \ge 1$. This is harmless: $L = 0$ means no word has a codeword within agreement $A$, which for a nonempty code forces $A > n$. In the Lean, `treeN` truncates $L - 1$ at $0$, the general theorem holds for every $L$, and the special cases treat $L = 0$ separately (all lists are then empty if there is at least one lane). For Reed-Solomon codes no case distinction is visible: the zero polynomial is in the list of the zero word, so $L \ge 1$ or $a > n$ (`GenListBound.pos_or`).
3. **$A \le n$ is not used**, and the general bound $N(n - d)$ holds with zero lanes too. The condition $m \ge 1$ is used only in the special cases, and only at $L = 0$.
4. **Theorem I uses nothing but the agreement bound**, as the note says: the Lean code is an arbitrary set of words over an arbitrary alphabet, the index type need not be finite (a finite set `D` of coordinates is given), and the lanes are any finite type. The induction is on a finite set of lanes, with a node represented by the set of list members below it; the heavy child is the one with the largest agreement set.
5. **Proposition R2' uses nothing of the code but a generator with entries in $K$.** The note's "some coefficient of $c_i - c_j$ is nonzero" is "the two messages differ at some coordinate", and "$\lambda$ commutes with evaluation on $D$ because $D \subset K$" is `map_enc`. The Lean statement is for any $K$-linear code given by a matrix, lists being lists of messages; `W` is any finite $K$-module (the note's $K^s$ is one), and `K` is not assumed finite (a nonzero finite `V` forces it).
6. **Proposition 3.5 of note 13 gives $L_1 + L_1'(L_2 - 1)$**, since each shared first component accounts for at most $L_2 - 1$ extra members. With $L_1' = 1$ this is the $2L - 1$ of Theorem I (note 13 states $2L$; note 14 already remarks that Theorem I gives $2L - 1$).
7. **The closed form is proved by induction on the recursion**, through Pascal's rule for $M(b, r) = \sum_{k \le r}\binom bk x^k$, not by the path-counting argument of the note; the statement is the note's, with $b$ and $r$ as floors. The step $\sum_{k \le r}\binom bk \le \binom{b+r}{r}$ is Vandermonde, as in the note, and the last inequality needs $L \ge 1$.
8. **"An $h$-lane $E$-valued word is a $2h$-lane $K$-valued word with the same list"** is checked inside `gen_interleave` for any finite-dimensional space of values: one must also see that distinct messages give distinct tuples of codewords, which follows from $d < a$ (two messages with the same words would force $n \le d$).

## 6. What is not machine-checked

- **The numbers of note 14 section 7.4** and the table of section 7.3 as a table: the Lean has the bounds, not their evaluation at the ladder's parameters. **[not formalized]**
- **$\mathrm{ListBound}_i$ for the protocol's levels**: that the code at level $i$ is the Reed-Solomon code of degree at most $2^{\kappa_i} - 1 + \ell_i$ on $D_i$, with $D_i$ in $K$, and the thresholds $A^{(i,0)}$. The Lean statements are for an arbitrary finite set of points of the small field, an arbitrary degree bound and an arbitrary agreement. **[not formalized]**
- **$\mathrm H_E$ at the deployed fields.** `rs_descent` covers it (take `F₀` the extension and one lane), but only $\mathrm H_K$ is instantiated in `Axioms.lean`. **[not formalized as an instance]**
- **Lemma F (2) from $\mathrm H_K$.** `Bridge.lean` feeds the list bound into `DeepFold.lemmaF_exc` only; `DeepFold.lemmaF_round` has no list hypothesis. That the words $O_0, O_1$ of the protocol are functions on $D$ and that $D$ is in the small field is taken as the form of the statement (`D₀.image (algebraMap K E)`). **[not formalized beyond this]**
- **Tightness.** Whether $2L - 1$ is attained, and the exhaustive checks of note 14 section 7.1. Only the trivial converse `ListBound.of_interleave` is proved. **[not formalized]**
- **The comparison with [GGR11], [ABF26, Lemma 2.10] and ArkLib**: `interleave_listBound_choose` is the form $\binom{b+r}{r}L^r$ with floors, which implies the form with ceilings by monotonicity; that implication is not stated. **[not formalized]**
- **The identification of leanVM's $E = K[y]/(y^2 + xy + 1)$ with `E128`.** `E128` is Mathlib's chosen quadratic extension of `GaloisField 2 64`; the theorems hold for every finite `K`-algebra, so nothing depends on the choice, but no isomorphism with the tree's field is stated. **[not formalized]**

## 7. Reproduction

`lean/Interleave/README.md`. In short, on a build host: `cd doc/whir_soundness_gap_notes/lean && lake exe cache get && lake build Interleave`. The scratch project that was checked is `h4:/data/whir_lean_scratch_28/lakeproj`, with its log `lake-build.log` one directory up; the file-by-file run used `h4:/data/whir_lean_scratch_28/check.sh`.
