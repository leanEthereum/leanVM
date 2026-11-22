# 32. The transitions of Theorem D' and the extractor step, machine-checked in Lean 4

Researcher 32. This note says exactly which transitions of the round-by-round theorem of note 14 (Theorem D', section 4.3) and which parts of its knowledge-soundness theorem (Theorem K and Corollary K2, sections 5.1 and 5.2) are now checked by Lean 4 with Mathlib, in what form, and what is not. The sources are the library `Rounds` of the project in `lean/` (eight files, about 1300 lines, `lean/Rounds/README.md`), built on the library `DeepFold` of note 22 (Lemma F) and, in one file, on researcher 31's library `Protocol` (Lemma P). Tags: **[machine-checked]** means the statement is a Lean theorem that compiles with no `sorry` and depends on Lean's three axioms only; **[not formalized]** means no Lean statement exists.

## 0. Summary

1. **Every transition M1 to M5 of Theorem D' is machine-checked as a standalone counting statement**, in the relativised form that Theorem K needs (a predicate `B` on tuples; `B` true is plain soundness): the batching challenge (`batch_transition`, at most `J - 1` values of `λ`), the fold challenge (`fold_transition`, fewer than `K₀` challenges, derived from `lemmaF_round`), the query message of a level with its batching (`query_transition`, at most `(A - 1)^t q + n^t (s + t)` of the `n^t q` messages), the last query message with the point check of step 3 (`final_transition`, at most `(A - 1)^t` position vectors), and a tail sumcheck round (`tail_round_transition`, at most 2 values). Each has a density form with exactly the error of Theorem D'. M0 (the points) is researcher 31's part.
2. **The extractor step of Theorem K is machine-checked**: uniqueness of the near tuple on a set of at least `d + 3` columns (`nearT_unique`), the descent step (`descent_step`: a tuple that fails the pull-back of `B` is a list member of the fold, and the unfolded word has exactly one near tuple on its agreement set, which lies in the list of the previous round and fails `B`), and two facts the note does not state: the near tuple folds back to the tuple it was decoded from (`NearT.fold_eq`), and its first half has degree less than `d` when `β ≠ 0` (`NearT.degree_lt`).
3. **No error and no missing hypothesis was found in the hand proofs** of section 4.3, 5.1 and 5.2 of note 14. Section 4 lists what the formalization shows: which standing assumptions each transition really uses, where characteristic two enters, and that M3 uses of the novel basis only that `U ↦ 𝒫_{g_U}` is linear.
4. **Not machine-checked**: the composition of the transitions over the rounds and levels of a run (no transcript or protocol object is defined), the potential part `(G_{i,j})` of the state and M0 (researcher 31), the identities of Annex B that make the protocol's checks instances of the abstract data (`lem:colweight` at a point outside the domain, the low part and the high part, the shape of the real weights), completeness, the Fiat-Shamir compilation and the outer protocol. Section 5.
5. **Checked on `h4`** with Lean 4.36.0 and Mathlib `v4.36.0`, twice (each module against the prebuilt Mathlib, and a real `lake build DeepFold Rounds` from an empty output directory: `Build completed successfully (18297 jobs)`). Nothing was installed or built on the Mac. All 57 files of `lean/` in the repository and in the project built on `h4` had identical SHA-256 at the time of the final build.

## 1. How it was checked

Host `h4`, scratch directory `/data/whir_lean_scratch_32` (created for this, safe to delete). Lean `leanprover/lean4:v4.36.0`, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, Lake `5.0.0-src+611c117`; Mathlib tag `v4.36.0`, the revision of `lean/lake-manifest.json`.

- Run 1: each module of `DeepFold`, `Protocol` (the three files `Rounds` imports) and `Rounds` compiled in dependency order with `lean -o`, with `warningAsError`, against the Mathlib already built in `/data/lean436/formal/Statement/.lake/packages` (read only). No output: no error, no warning.
- Run 2: a fresh copy of the whole project `lean/` in `/data/whir_lean_scratch_32/lakeproj`, its `.lake/packages` copied from note 22's scratch project (same `lake-manifest.json`, compared by hash; nothing was downloaded), then `lake build DeepFold Rounds` from an empty build directory, on 8 cores at nice 10: `Build completed successfully (18297 jobs)`. `lakefile.toml` sets `warningAsError`. The only messages are Lake's advisory that `DeepFold/Basic.lean`, `DeepFold/Counting.lean` and `Protocol/Potential.lean` import `Mathlib` without the module system. The log is `/data/whir_lean_scratch_32/lake-build.log`.
- No `sorry`, `admit`, `axiom` or `native_decide` occurs in the sources. `Rounds/Axioms.lean` runs `#print axioms` under `#guard_msgs` on 39 statements, all those named in this note: each depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else, and the build fails if that changes. A control file with one `sorry` was rejected by the same command line.
- `Rounds/Axioms.lean` also instantiates `fold_transition`, `batch_transition`, `query_transition`, `final_transition`, `tail_round_transition` and `descent_step` at `GaloisField 2 128`, so the typeclass hypotheses are satisfiable at the deployed size.
- `Rounds/Pinned.lean` imports `Protocol.Pinning`, which researcher 31 was still extending while this was built. The final build used `Protocol/Lists.lean` (SHA-256 `4dd6f1bc...`), `Protocol/Pinning.lean` (`f3665460...`) and `Protocol/Potential.lean` (`ebf3431c...`); an earlier build against the previous versions of the first and third was also green. `Pinned.lean` uses of `Protocol` only `listW`, `mem_listW`, `NonSep` and `pinned_unique`. The other seven files of `Rounds` import `DeepFold` only.

## 2. What is stated and checked

### 2.1 The state

Notation of the Lean. `K` is a field (finite where counting is involved, of characteristic two only where said), `D : Finset K` the domain, a word is `O : K → ι → K` with lane type `ι`, a tuple is `U : ι → K[X]`. A word before a fold has lanes `ι ⊕ ι`: `Sum.inl` is the half `O₀` (folded variable 0), `Sum.inr` the half `O₁`. `evL ex z U` is `DeepFold`'s $\mathrm{ev}_z(U) = \sum_u\theta^{\mathrm{ex}(u)}U_u(\zeta)$.

| Lean definition | meaning | note 14 |
| --- | --- | --- |
| `agr D O U` | the agreement columns of `U` with `O` | `def:interleaved` |
| `InList D O d A U` | $U \in \mathrm{List}(O; A, d)$ | section 2 |
| `NearT D O d S U` | `U` is a near tuple of `O` on `S`: degree at most `d`, agrees with `O` on all but at most one column of `S` | 5.1, `NearT` |
| `foldWord c O` | the affine fold $O_c = O_1 + (\alpha + \beta x)O_0$ | `def:affine-fold` |
| `foldTuple c U` | $G + (\alpha + \beta X)F$ for $U = (F, G)$ | step 1(c) |
| `pull D O d A c B` | the pull-back of a predicate along the challenge `c` | 5.1, `pullT` |
| `foldWeight W c` | $\widehat W(\alpha, \cdot) = (1 + \alpha)W_0 + \alpha W_1$, with $W_0$, $W_1$ the restrictions of the functional `W` to the halves | step 1(c) |
| `foldClaim σ vG vF σ₀ σ₁ c` | $v_G + \alpha(v_G + \sigma) + \alpha^2v_F + \beta\sigma_0 + \alpha\beta(\sigma_0 + \sigma_1)$ | Annex B, step 1(c) |
| `foldVal w z v φ c` | $v_m + (\theta_m^w + \alpha + \beta\zeta_m)\varphi_m$, $w = 2^{j-1}$ | step 1(c) |
| `exHalves w ex` | the exponents before the fold: $w + \mathrm{ex}(u)$ on the first half, $\mathrm{ex}(u)$ on the second | Lemma E (E2) |
| `Doomed D O d A ex z v W σ B` | no $U \in \mathrm{List}(O; A, d)$ with $B(U)$ satisfies $(W, \sigma)$ and all point claims $(z_m, v_m)$ | $(\mathrm I_{i,j})$ of 4.2, $(\mathrm I^B_{i,j})$ of 5.1 |
| `Doomed₁ D w d A ζ v W σ B` | the same for a one-lane word, a point claim being $P(\zeta_m) = v_m$ | $(\mathrm I^B_{i,\ell_i})$ |
| `nextW`, `nextC` | the batched weight and value of step 2(e), with the conversions of step 2(d) | steps 2(d), 2(e) |

A weighted claim is an arbitrary $K$-linear functional on tuples with a value, as in `lemmaF_round`. `Doomed.one_lane` **[machine-checked]** turns `Doomed` for a one-element lane type and exponent zero into `Doomed₁`, so the state that the last fold of a level leaves is the state M3 and M4 start from.

### 2.2 M2, the fold challenge (priority 1)

```lean
theorem fold_transition [CharP K 2] (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (ex : ι → ℕ)
    (w : ℕ) {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K}
    (hz : z ∉ ExcL (fullT D (half₀ O) (half₁ O) d A) ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W : (ι ⊕ ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K) (B : (ι ⊕ ι → K[X]) → Prop)
    (hI : Doomed D O d (A - 1) (exHalves w ex) z v W σ B)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K =>
      ¬ Doomed D (foldWord c O) d A ex z (foldVal w z v φm c) (foldWeight W c)
        (foldClaim σ vG vF σ₀ σ₁ c) (pull D O d A c B))).card < K₀
```

Reading, against the paragraph "M2" of note 14. `O` is $O^{(i,j-1)}$, `A` is $A^{(i,j)}$, so `A - 1` is $A^{(i,j-1)}$ and `hI` is $(\mathrm I^B_{i,j-1})$, with the point claims evaluated with the exponents of round $j - 1$. `hz` is $z^{(i)} \notin \mathrm{Exc}_j(O^{(i,j-1)})$, which Lemma T(b) provides. The prover message is quantified after `hI`. The state after the challenge is $(\mathrm I^{\mathrm{pull}\,B}_{i,j})$: the list of the fold at $A^{(i,j)}$, the claim $(W^{(i,j)}, \sigma^{(i,j)})$, the carried values of step 1(c), and the predicate $B_{i,j} = \mathrm{pull}\,B_{i,j-1}$.

| Lean statement | content | status |
| --- | --- | --- |
| `fold_transition` | M2 of Theorem K: fewer than `K₀` challenges leave a state that is not doomed | **[machine-checked]** |
| `fold_transition_plain` | M2 of Theorem D': the same with `B` true before and after | **[machine-checked]** |
| `fold_transition_density` | the density is at most $(K_0 - 1)/q^2$ | **[machine-checked]** |
| `pull_true`, `Doomed.mono`, `evL_exHalves`, `agr_foldWord`, `agr_elim`, `weight_elim` | the pull-back of the trivial predicate is trivial; monotonicity in `B`; (E2) for `exHalves`; the links with `agrL`, `agrPairL` and with $\langle W, U\rangle = \langle W_0, F\rangle + \langle W_1, G\rangle$ | **[machine-checked]** |

### 2.3 M1, the batching challenge (priority 2)

```lean
theorem batch_transition (D : Finset K) (O : K → ι → K) (d A : ℕ) (ex : ι → ℕ) {s : ℕ}
    (z : Fin s → K × K) (y : Fin s → K) {J : ℕ} (Wk : Fin J → (ι → K[X]) →ₗ[K] K)
    (ck : Fin J → K) (B : (ι → K[X]) → Prop)
    (hsep : ∀ U U' : ι → K[X], InList D O d A U → InList D O d A U' →
      (∀ m, evL ex (z m) U = y m) → (∀ m, evL ex (z m) U' = y m) → U = U')
    (hfalse : ∀ U : ι → K[X], InList D O d A U → B U → (∀ m, evL ex (z m) U = y m) →
      ∃ k, Wk k U ≠ ck k) :
    (univ.filter (fun l : K =>
      ¬ Doomed D O d A ex z y (batchW Wk l) (batchC ck l) B)).card ≤ J - 1
```

`hsep` is "the points are separating" as M1 uses it (at most one list member matches all answers). `hfalse` with `B` true is the definition of false input claims of Theorem D', and with `B = Bad` the hypothesis of Theorem K. `batchW`, `batchC` are $\sum_k\lambda^{k}W_k$, $\sum_k\lambda^kc_k$ with $k$ from 0. There is no list factor: the proof uses the one pinned candidate, as the note says.

| Lean statement | content | status |
| --- | --- | --- |
| `card_powsum_zero_le` | $\sum_k\lambda^{e(k)}\delta_k$ with pairwise distinct exponents at most $N$ and some $\delta_k \ne 0$ has at most $N$ roots | **[machine-checked]** |
| `card_batch_zero_le` | the case of the powers $0, \dots, J - 1$: at most $J - 1$ roots | **[machine-checked]** |
| `batch_transition`, `batch_transition_density` | M1 of Theorems D' and K; density at most $(J - 1)/q$ | **[machine-checked]** |
| `k2_hfalse` | Corollary K2: the predicate "$U \ne U^\ast$ or $U$ violates an input claim" satisfies `hfalse` for any claims | **[machine-checked]** |
| `sep_of_not_mem_nonSep`, `batch_transition_pinned` | `hsep` follows from $z \notin$ `Protocol.NonSep (Protocol.listW D O d A)`, the conclusion of researcher 31's Lemma P; M1 with that hypothesis | **[machine-checked]** |

The ring-switching scalars that share the message ($+2/q$, section 6.3 of note 14) are the outer protocol and are not in the statement.

### 2.4 M3, the query message of a level (priority 3)

```lean
theorem query_transition [CharP K 2] (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ}
    (ζ v : Fin s → K) (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop)
    (hI : Doomed₁ D w d A ζ v W σ B)
    (D' : Finset K) (O' : K → ι' → K) (d' A' : ℕ) (ex' : ι' → ℕ) {s' : ℕ}
    (z' : Fin s' → K × K) (y' : Fin s' → K)
    (hsep : ∀ U U' : ι' → K[X], InList D' O' d' A' U → InList D' O' d' A' U' →
      (∀ m, evL ex' (z' m) U = y' m) → (∀ m, evL ex' (z' m) U' = y' m) → U = U')
    (low : (ι' → K[X]) →ₗ[K] K[X]) (C : K[X])
    (hdeg : ∀ U : ι' → K[X], InList D' O' d' A' U → (low U + C).natDegree ≤ d)
    (hWC : W C = 0) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
      (fun xl : (Fin t → K) × K =>
        ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
          (fun U => B (low U + C)))).card ≤
      (A - 1) ^ t * Fintype.card K + D.card ^ t * (s + t)
```

Reading, against the paragraph "M3". The level that ends: `w` is $w^{(i)} = O^{(i,\ell_i)}$, `A` is $A_i$, `ζ`, `v` the carried claims at round $\ell_i$, `hI` is $(\mathrm I^B_{i,\ell_i})$. The next level: `O'` with its list at $(A^{(i+1,0)}, d^{(i+1)})$, the new points `z'` and answers `y'`, separating (`hsep`). The link is abstract: `low U` stands for $\mathcal P_{g_U}$, of which only linearity is used, and `C` for $\widehat W_{\kappa_i}H^{(i)}$, so `low U + C` is $P^\ast_U$; `hdeg` is "degree at most $d^{(i)}$ by (S1)" and `hWC` is "a weighted claim sees only the low part". The claims of step 2(e) are then, by definition (`nextW`, `nextC`): the residual $U \mapsto \langle W, \mathrm{low}\,U\rangle$ with value $\sigma$ and power $\lambda^0$; for each carried point the functional $U \mapsto (\mathrm{low}\,U)(\zeta_m)$, which is $\langle W_{i,\zeta_m}, g_U\rangle$, with value $c'_m = v_m + C(\zeta_m)$ and power $\lambda^m$; for each query the functional $U \mapsto (\mathrm{low}\,U)(x_q)$ with value $c_q = w(x_q) + C(x_q)$ and power $\lambda^{s+q}$. The predicate after is $B_{i+1,0}(U) = B(P^\ast_U)$ (`nextPred`). The message is the pair (position vector in $D^t$, $\lambda$), and the bound divided by $n^tq$ is $((A_i - 1)/n_i)^{t_i} + (s_i + t_i)/q$.

| Lean statement | content | status |
| --- | --- | --- |
| `card_queries_agree_le`, `density_queries_agree_le` | a polynomial agreeing with `w` on fewer than `A` columns passes all `t` queries for at most $(A - 1)^t$ of the $n^t$ position vectors: density at most $((A - 1)/n)^t$ | **[machine-checked]** |
| `card_batch3_zero_le` | the root count for the powers $0$; $1..s$; $s + 1..s + t$: at most $s + t$ | **[machine-checked]** |
| `query_transition`, `query_transition_density` | M3 of Theorems D' and K, both cases of the note and the batching in one count | **[machine-checked]** |
| `query_transition_pinned` | M3 with `hsep` replaced by $z' \notin$ `Protocol.NonSep (Protocol.listW D' O' d' A')` | **[machine-checked]** |

### 2.5 M4 and M5, the last level (priority 4)

```lean
theorem final_transition (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ} (ζ v : Fin s → K)
    (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop) (hI : Doomed₁ D w d A ζ v W σ B)
    (P : K[X]) (hP : P.natDegree ≤ d) (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
      (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ ∧
        ¬ (A ≤ (D.filter (fun x => P.eval x = w x)).card ∧ ¬ B P))).card ≤ (A - 1) ^ t

theorem tail_round_transition {Y : Type*} [Fintype Y] (W₀ W₁ f₀ f₁ : Y → K) (σ : K)
    (hfalse : ∑ x, (W₀ x * f₀ x + W₁ x * f₁ x) ≠ σ) (h : K[X]) (hh : h.natDegree ≤ 2) :
    (univ.filter (fun r : K => h.eval 0 + h.eval 1 = σ ∧
      ∑ x, ((1 - r) * W₀ x + r * W₁ x) * ((1 - r) * f₀ x + r * f₁ x) = h.eval r)).card ≤ 2
```

`final_transition`: `P` is the polynomial sent in the clear. The filter is the set of position vectors for which the point check of step 3 passes, every query check passes, `P` satisfies the running claim (so the state "the low part of the polynomial sent does not satisfy the running claim" fails), and it is not the case that `P` is in the last list with $\neg B(P)$. So outside at most $(A - 1)^t$ vectors: a check failed, or the running claim is false for `P`, or $P \in \mathrm{List}^{(I-1,\ell)}$ and $\neg B_{I-1,\ell}(P)$, which is the conclusion of Theorem K for an accepting run that escaped no message. With `B` true the last alternative is empty and this is M4 of Theorem D' (`final_transition_plain`). The point check is used in the proof: it is the condition under which the invariant applies to `P`, in line with section 4.4 of the note ("the point check of step 3 is necessary"); that the statement fails without it is not formalized.

`tail_round_transition`: the claim before the round is $\sum_{b,x}W(b,x)f(b,x) = \sigma$ over $\{0,1\} \times Y$, false; the prover sends `h` of degree at most two; the verifier checks $h(0) + h(1) = \sigma$; the claim after the challenge `r` is $\sum_xW(r,x)f(r,x) = h(r)$ with the multilinear extensions in the first variable. At most two values of `r` pass the check and leave a true claim. It is stated over any field, with $1 - r$ (which is $1 + r$ in characteristic two).

| Lean statement | content | status |
| --- | --- | --- |
| `final_core` | the count behind M4 for one polynomial | **[machine-checked]** |
| `final_transition`, `final_transition_plain`, `final_transition_density` | M4 of Theorems K and D'; density at most $((A - 1)/n)^t$ | **[machine-checked]** |
| `tail_round_transition`, `tail_round_transition_density` | M5; density at most $2/q$ | **[machine-checked]** |

### 2.6 The extractor step (priority 5)

```lean
theorem nearT_unique {D : Finset K} {O : K → ι → K} {d : ℕ} {S : Finset K}
    (hS : d + 3 ≤ S.card) {U U' : ι → K[X]} (hU : NearT D O d S U) (hU' : NearT D O d S U') :
    U = U'

theorem descent_step (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (c : K × K)
    (B : (ι ⊕ ι → K[X]) → Prop) (hdA : d + 3 ≤ A) {P : ι → K[X]}
    (hP : ∀ u, (P u).natDegree ≤ d) (hnb : ¬ pull D O d A c B P) :
    InList D (foldWord c O) d A P ∧
      ∃ T : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) T ∧ InList D O d (A - 1) T ∧
        ¬ B T ∧ P = foldTuple c T ∧
        ∀ T' : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) T' → T' = T
```

| Lean statement | content | note 14 | status |
| --- | --- | --- | --- |
| `nearT_unique` | two near tuples on a set of at least $d + 3$ columns are equal | 5.1, `nearT_unique` | **[machine-checked]** |
| `NearT.inList` | a near tuple on a set of at least $A$ columns is in $\mathrm{List}(O; A - 1, d)$ | 5.1 Descent | **[machine-checked]** |
| `NearT.fold_eq` | if `P` has degree at most `d` and agrees with $O_c$ on at least $d + 3$ columns, a near tuple $T = (F, G)$ of $O$ on that agreement set has $P = G + (\alpha + \beta X)F$ | not in the note | **[machine-checked]** |
| `NearT.degree_lt` | then $\deg F < d$ when $\beta \ne 0$: the degree bounds $(d - 1, d)$ of the unfolded pair | 4.4 "degree slack" | **[machine-checked]** |
| `descent_step` | the step of the descent: from $\neg(\mathrm{pull}\,B)(P)$, the list membership of `P`, and the unique near tuple `T`, in the previous list, with $\neg B(T)$, folding to `P` | 5.1 Descent, 5.2 step 2 | **[machine-checked]** |
| `existsUnique_nearT` | existence and uniqueness of the near tuple, given one exists | 5.2 | **[machine-checked]** |

Computability is stated as existence and uniqueness: the near tuple is determined by `P`, `c` and the columns of the unfolded word on a set the extractor can compute. That it is found by solving a linear system (one-error decoding, `NearDecoder`) is not formalized. Across a level boundary the predicate of the next level is by definition $B(P^\ast_U)$ (the last argument of `Doomed` in `query_transition`), so the descent continues with `descent_step` at the last round of the previous level applied to the one-lane tuple $P^\ast_T$.

## 3. Where the Lean statements differ from the note

None of these weakens what is proved.

1. **Counting statements.** A probability is the cardinality of a set of verifier messages; each transition also has a density form in $\mathbb Q$ with the error of Theorem D'. A query message is a vector in $D^t$ (`Fintype.piFinset`), so the queries are independent and uniform in $D$ by construction; how the verifier derives them from the sponge (`sample_queries`) is outside.
2. **The alternative "some check has already failed" is not part of `Doomed`.** The transitions are stated for the non-trivial alternative. In M4 the two checks of step 3 are explicit conjuncts.
3. **Weighted claims are arbitrary linear functionals on tuples**, as in `lemmaF_round`. That the protocol's weights see only low parts is used once, as the hypothesis `hWC` of M3.
4. **M3 is abstract in the encoding.** `low` is any linear map and `C` any polynomial with `hdeg` and `hWC`. The column weights, the converted claims and the residual are defined from `low`. So the statement covers the protocol given the identity $\mathcal P_g(x) = \langle W_{i,x}, g\rangle$ for every $x \in E$ and the split of $P^\ast$ into low and high part, which are Annex B's and are not formalized here.
5. **Indices from zero.** Claims carry $\lambda^k$, $k = 0, \dots, J - 1$; in step 2(e) the residual carries $\lambda^0$, point $m \in \{0..s-1\}$ carries $\lambda^{m+1}$, query $q \in \{0..t-1\}$ carries $\lambda^{s+1+q}$: the note's powers.
6. **$M$ is any integer with $M \ge \max(2q, \binom n2)$** (inherited from `lemmaF_round`).
7. **The relativised form is the primary one.** Each transition takes a predicate `B`; Theorem D' is `B` true, and M2 and M4 have a separate plain statement.
8. **Lane types.** A word before a fold has lanes `ι ⊕ ι` for an arbitrary finite `ι`; the exponents are an arbitrary map `ex` with `exHalves w ex` before the fold. That the note's $e_j$ has this form with $w = 2^{j-1}$ is (E2) and is not re-proved for the concrete $e_j$.

## 4. What formalizing showed about the hand proofs

No error and no missing hypothesis in M1 to M5, in the descent, or in the proof of Corollary K2. The observations, in decreasing order of interest:

1. **The descent inverts the fold** (`NearT.fold_eq`). Theorem K says the near tuple is in the previous list and fails the predicate; it does not say that it folds back to the tuple it came from. It does, whenever $A^{(i,j)} \ge d + 3$: the fold of the near tuple has degree at most $d + 1$ and agrees with `P` on at least $d + 2$ columns. So the chain of tuples the extractor computes is consistent with the challenges of the transcript, and for $\beta \ne 0$ its first halves have degree at most $d - 1$ (`NearT.degree_lt`), which is the "nothing grows going back" of section 4.4 as a statement about the extractor's output and not only about Lemma L2.
2. **Which standing assumptions are used where.** (S2) is used only in the descent, as $d + 3 \le A^{(i,j)}$ for $j \ge 1$. None of M1 to M5 uses any relation between $A$, $d$ and $n$; M3 and M4 hold in truncated arithmetic even for $A = 0$ or $t = 0$. (S1) enters only as `hdeg` of M3, and only for the pinned candidate. (S3) enters only through $M \ge \binom n2$ in M2. The density form of M3 needs $n \ge 1$.
3. **Characteristic two** is used in M2 (through Lemma F, one line, note 22) and in M3 for the sign of the conversions $c' = v + \widehat WH$, $c_q = w + \widehat WH$. M1, M4, M5 and the whole descent hold over every field.
4. **M3 uses of the novel basis only linearity.** Nothing about $\mathcal P_g$ beyond "$U \mapsto \mathcal P_{g_U}$ is linear, $P^\ast_U$ has degree at most $d$, and the running weight vanishes on the high part" enters the count. In particular a tuple $U^\ast$ with a nonzero high part needs no separate argument, as the referee noted (note 20, section 3.4).
5. **The order of quantifiers is as claimed.** In M2 the prover message is quantified after the invariant and the exceptional set; in M1 the claims are arbitrary given the points and the answers; in M3 the pinned candidate and $P^\ast$ are determined by data that does not depend on the queries or on $\lambda$ (they are fixed inside the proof before the message is introduced). Lean's binder order makes these checked facts.
6. **M3's two cases and the batching give one count**, $(A - 1)^tq + n^t(s + t)$, with no cross term: for each position vector that sees a disagreement, or in Case 1 for every position vector, at most $s + t$ values of $\lambda$ are roots.
7. **Corollary K2 needs no assumption on the claims** for its predicate to satisfy the hypothesis of Theorem K (`k2_hfalse`): separation alone.

## 5. What of Theorem D' and Theorem K is machine-checked, and what is not

Machine-checked, with this note and notes 22 and 31's library:

- **Theorem D', property (iii)**, message by message, for the part $(\mathrm I_{i,j})$ of the state: rows M1 (first term), M2 (the term $(K_0 - 1)/q^2$), M3, M4, M5 of the table of section 4.1. The hypotheses each transition takes from the other part of the state are explicit: `hz` (points outside $\mathrm{Exc}_j$, from Lemma T(b)) in M2, `hsep` (separating points, from Lemma P) in M1 and M3; the second is discharged from `Protocol.NonSep` in `Rounds/Pinned.lean`.
- **Theorem K**: the relativised transitions M1 to M4 with the same counts, the conclusion "an accepting run that escaped no message has $P \in \mathrm{List}^{(I-1,\ell)}$ and $\neg B_{I-1,\ell}(P)$" in the form of `final_transition`, and one step of the descent with uniqueness. **Corollary K2**: that its predicate is admissible.

Not machine-checked:

- **The composition.** No protocol, transcript or state function over a whole run is defined; the transitions are not chained over the rounds of a level, the levels, or the tail. In particular: that the after-state of one transition is the before-state of the next (true by inspection of the statements, with `Doomed.one_lane` at the end of a level, but not a Lean theorem about a run), properties (i), (ii), (iv) of `def:rbr`, and the iteration of `descent_step` down to level 0. **[not formalized]**
- **The potential part of the state**: $(\mathrm G_{i,j})$, the terms $\tau$ of M2 and the whole of M0 are researcher 31's (`Protocol/`); `fold_transition` takes `hz` as a hypothesis and is not yet joined to Lemma T(b). **[not formalized here]**
- **Annex B's identities behind the abstract data**: the novel basis, $\mathcal P_g(x) = \langle W_{i,x}, g\rangle$ at every $x \in E$ (`lem:colweight`), the low and high parts and (S1), that the real weights are functionals of the low part, that $e_j$ has the form `exHalves`, and that the verifier's folded column value is the folded word. **[not formalized]**
- **Completeness** (section 1.4), the last check of the tail (the verifier evaluates $f^{(I)}$), and the terminal weight. **[not formalized]**
- **Fiat-Shamir, grinding, Merkle commitments and extraction of the committed words, the ring switch and the outer protocol**: inherited in note 14 from the existing formalization in `formal/`, which this standalone project does not import. **[not formalized]**
- **The decoder**: that the near tuple is computed by one-error decoding in polynomial time. Only existence and uniqueness are checked. **[not formalized]**

## 6. Reproduction

`lean/Rounds/README.md`. On a build host: `cd doc/whir_soundness_gap_notes/lean && lake exe cache get && lake build DeepFold Rounds`. The project that was checked is `h4:/data/whir_lean_scratch_32/lakeproj`, with its log `lake-build.log` one directory up; `proj/` beside it is the per-module check of run 1.
