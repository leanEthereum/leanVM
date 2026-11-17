# An agreement-set knowledge extractor

The knowledge extractor (`lean_vm/LeanVM/Protocol/Extraction/Extractor.lean`) list-decodes level 0's word at the Johnson threshold with Guruswami–Sudan and runs every candidate; that list decoding is the `2^max(80, 2μ+25)` term of the statement's budget. This note shows that an extractor that decodes uniquely, on agreement sets the transcript pins down, is correct with the same per-message errors, and says what proving it in Lean takes. The idea is scaraven's (github.com/scaraven), from the lvm2 write-up's "advice decoding" annex.

## The extractor

Notation is Annex B's (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`): levels `i < M`, fold rounds `j ≤ ℓ_i`, words `ω^(i,j)` (level `i`'s oracle folded by its first `j` challenges, `ω^(i,ℓ_i) = w^(i)`), degree `d_i = 2^κ_i − 1 + ℓ_i`, thresholds `A^(i,j) = A_i − (ℓ_i − j)`, high parts `φ^(i)`, final polynomial `P^fin`.

For a polynomial tuple `U` and a word `ω` let `S(U, ω)` be the set of columns where they agree. Define, for a level `i` and round `j ≥ 1`, the one-round step `Dec_{i,j}(U)`: decode the two halves of `ω^(i,j−1)` on the columns `S(U, ω^(i,j))` with at most one error, giving a tuple of degree at most `d_i` (or nothing). At a level boundary, `Up_i(U) := mpoly(g_U) + Ŵ_{κ_{i−1}} Σ_s φ^(i−1)_s X_s`, the polynomial of level `i−1`'s last round with the message of `U` as low part and the proof's high part. The extractor computes `T := P^fin`, then for `i = M−1` down to `0`, `j = ℓ_i` down to `1`, `T := Dec_{i,j}(T)`, and `T := Up_i(T)` between levels; the last `T` is a tuple of level 0, and its low parts are the stack, run as now (`candidateExecutionIn`). Write `Back_{i,j}` for the composition of the remaining steps from round `(i,j)`, so the output is `Back_{M−1,ℓ}(P^fin)`.

Each step is one unique decoding of a lane with one error (Berlekamp–Welch, or Guruswami–Sudan at multiplicity one and `Y`-degree one) on a set of at least `A^(i,j)` columns, `2^(ℓ_i − j + 1)` lanes per round: at level 0, `126` lanes of length at most `2^26`. Unique decoding with one error needs two tuples that each agree with the word on all but one column of `S` to agree on more than `d_i` columns, `|S| ≥ d_i + 3`; `|S| ≥ A^(i,j) ≥ A^(i,0) + 1` and `(A^(i,0))² > n_i d_i` give it at every admissible shape (a parameter check, decided over the table like the others).

## Correctness, with the same errors

Replace the opening's invariant (Annex B, proof of `thm:rbr`) by a **bad set** that is empty at the start:

`Bad_(i,j) := { U ∈ lst^(i,j) : U satisfies (W^(i,j), σ^(i,j)) and Back_(i,j)(U) is not a member of lst^(0,0) satisfying all input claims }`,

the invariant `(I'_(i,j))` being `Bad_(i,j) = ∅` (with the batching, OOD and query states as in Annex B). At the start of the opening `Back` is the identity and `Bad` is empty by definition. Each verifier message breaks the invariant with at most Annex B's probability, by the same events used forwards:

* **Fold `(α, β)` of round `(i,j)`.** Outside `B_1` (the MCA event of `thm:mca-affine` for the halves of `ω^(i,j−1)`, `excSet`), every `U ∈ lst^(i,j)` has a witness `(F, G)` with `U = G + (α + βX)F`, agreeing with the halves on all of `S(U, ω^(i,j))` but one column, so `(F, G) ∈ lst^(i,j−1)` and `Dec_{i,j}(U) = (F, G)` by uniqueness. Outside `B_2` (`lem:fold-list`: no pair of the list that violates the old claim satisfies the new one), if `U` satisfies the new claim then `(F, G)` satisfies the old one. So `U ∈ Bad_(i,j)` gives `(F, G) ∈ Bad_(i,j−1) = ∅`. Error `ε_aff + 2 jl(A^(i,j) − 1, d_i)/|E|`, as now.
* **Query message and `λ_(i+1)`.** By OOD separation at most one message `g*` of `lst^(i+1,0)` answers `y_(i+1)`. Outside the batching event, a `U ∈ Bad_(i+1,0)` satisfies all `J_(i+1)` claims, so `g_U = g*` and `Up_(i+1)(U)` matches `c_(i,q)` at every query. If it agrees with `w^(i)` on fewer than `A^(i,ℓ_i)` columns, every query landed in that set (probability `((A^(i,ℓ_i) − 1)/n_i)^(t_i)`, for the one `g*` fixed before the queries); otherwise `Up_(i+1)(U) ∈ lst^(i,ℓ_i)` satisfies the residual claim, so it is in `Bad_(i,ℓ_i) = ∅`. Error as now.
* **Final query message and tail.** If `P^fin` agrees with `w^(M−1)` on at least `A^(M−1,ℓ)` columns it is in the last list, and with the invariant `Back(P^fin)` satisfies the input claims unless `P^fin` violates the last claim, which the tail sumcheck catches (`2/|E|` a round). Otherwise the queries catch it, as now.
* **Batching `λ_0`, OOD points.** Unchanged.

So, on an accepted proof outside the escape events, `C := Back(P^fin)` is a member of level 0's list satisfying every input claim of the opening, the commitment's OOD claim among them, so `C` is the one candidate the commitment's OOD answer leaves (`oodCands`). The front phases are analysed on that one candidate already (`Assemble.lean`, item 4); their doom must become "`C*` is valid, or `C*` violates the current claims", which holds at the root unconditionally and escapes exactly when the current doom does (a case split: validity of `C*` is fixed once the OOD point is drawn). With it, `C` is a valid execution. Every escape probability is the current one: **the certificate's per-message errors do not change**.

The cleanest way to reuse `romSound_log` unchanged: apply it to the verifier program that returns `verdict && !Good(history)`, `Good` the noncomputable statement "`Back(P^fin)` read off the history is valid", with the new doom predicates, which hold at the root, so `Doomed` is the root itself.

## Availability: what is new in the error

The extractor reads only the adversary's queries; `romSound_log`'s extracted history reads the final cache, the verifier's queries included. Today's extractor needs only level 0's word, and the gap is one term, a fresh hash answer of the verifier equal to the announced root (`prEvent_logged2_root_le`, `13708/2^256`). The new one needs every level's word and every fold challenge:

* **Every level's root**: the same lemma per committed root (at most `6` levels): each `13708/2^256`.
* **Every fold challenge**: outside `Fail`, once the verifier's duplex makes a fresh permutation query, every later one is fresh (a later adversary query would have predicted its capacity). The last fold challenge precedes the final level's query message, whose proof-of-work permutation also gives the first query sample (its lanes `0, 1`): if any fold challenge is fresh, that permutation is a fresh verifier answer passing the `17`-bit grind whose first sample names the proof's first `⌊128/depth⌋` positions, at least `117` bits at every deployed shape. Per verifier query at most `2^-134`, `13708 · 2^-134 ≈ 2^-120.3` in all, inside the statement's spare `2674 · 2^-125`.

Each is at most `2^-125`. `lean_vm`'s `soundnessError` gains them, and the end statement does not change: `soundnessRpm_le_statement` uses `Q + 13708 + 2 ≤ Q + 2^14` (`ErrorBounds.lean`), leaving room for more than two thousand terms of `2^-125`.

## What it takes in Lean

1. **The opening** (`LeanVM/Protocol/Whir/Sound/`): the invariant `Bad = ∅` with `Back`, the four transitions above from the existing lemmas (`card_excSet_le_nAff` and `IsWitness` for `B_1`, the fold, batching, OOD and query counts), and `OpeningIface.stackedSpec` restated from the new precondition.
2. **The front and the assembly** (`EndToEnd/Front/`, `EndToEnd/Sound/`): each doom predicate weakened by "`∨ C*` is valid", generically if the phases' doom predicates factor through `C*`, and the end event as above.
3. **Availability**: the root lemma per level, the committed word of every level (`committedWord_eq` generalised), and the fresh-chain lemma.
4. **The extractor**: replay the verifier's transcript from the adversary's permutation queries (the schedule is the verifier program's, `runPure`'s with real answers), invert every level's tree (`committedLeaves`), the descent with one-error decoding, then the candidate run. Its proof against the history: `Sound.extractor_of_extracted` restated.
5. **Cost** (`LeanVM/Cost/`): compile it and prove its price. The decoder at multiplicity one replaces Roth–Ruckenstein's search; the replay compiles the verifier's schedule into the program, so the size bound (`14159`) grows by that, which `statement.tex` must then account for.

Items 1 to 3 are a refactor of the soundness proof, not new mathematics; item 5 is the largest by volume.

## Status

Done on `agreement-set-extractor` (each step builds on its own):

* `CertG` with an acceptance predicate, `romSound_logG`, `romSound_of_impG`, `Spec.toCertG`.
* The relativised invariant: `TViol` with a predicate, `pullT` through near tuples at the round's threshold, `FoldRoundBound` relativised (`AffineCombinerFoldRel`), `nextPred` across levels, `lvl0Pred` at level 0.
* The ghost opening (`whirLevelsG`, `verifyWhirG`, `verifyStackedOpeningG`) returning a `WhirTrace`, its specifications with postcondition `traceGood`, and the descent (`Whir.Sound.Descent`: a good trace has a level-0 list member whose stack is not bad).
* The assembly on the bad stacks, the ghost verifier (`leanVmProgramG`), `leanVmCert` a `CertG` with `GoodRun`, and the end theorem through `doomed_of_not_extracted` (accepted, not extracted, gives doom and not a good run). The statement's extractor is still the list decoder.

## Next

1. **The descent as an algorithm**: from the trace and the levels' words, the final polynomial, then at each round back the unique near tuple of the unfolded word on the agreement set (each lane decoded on the set with at most one error, which the Guruswami–Sudan decoder does on any point list at multiplicity one), and at each level boundary the polynomial of the message and the high part; at level 0 the stack. Proved equal to the existential descent when the trace is good: near tuples on a set of at least `d + 3` columns are unique.
2. **The replay**: the verifier run with the adversary's permutation answers up to the final level's polynomial, returning the trace, and every level's word inverted through the adversary's hash answers. The ghost levels take their final step as a parameter (`whirLevelsGF fin`): the full ghost is the cut one (the final step reads the final polynomial and returns) followed by the rest, so an accepted run's history has a prefix on which the cut ghost returns the same data. The replay interprets the cut ghost like `Compile.run`, with the adversary's permutation answers and openings returned unverified (they are not absorbed), and agrees with the extracted history wherever the adversary's answers cover the run's permutation inputs. Not the whole verifier's price is known on the cost machine: pricing this replay is new work (no cost proof covers running the verifier today).
3. **Availability**: without failure, an accepted proof whose replay stops early has a fresh verifier permutation before the final query positions, so the positions and their grind were guessed; every level's root is an adversary's hash (the stack root's argument, per level). New terms of the internal `soundnessError`, absorbed by the statement's `2^14`.
4. **Cost**: compile the new extractor to the cost machine and prove its price; then the statement's size bound and budget, `statement.tex`, and removing the list decoder.
