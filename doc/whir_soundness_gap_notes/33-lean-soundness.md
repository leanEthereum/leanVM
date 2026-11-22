# 33. The composition: Protocol D is round-by-round sound, machine-checked in Lean 4

Researcher 33. Notes 22, 28, 31 and 32 checked the lemmas of the modified WHIR (Protocol D of note 14) in separate libraries and each listed the composition as not checked. This note reports the glue: a new library `Soundness` of the project in `lean/` (seven files, about 2300 lines, `lean/Soundness/README.md`) that defines round-by-round soundness of a public-coin protocol, defines Protocol D over a ladder of levels with its tail as such a protocol, defines the full state of note 14 section 4.2 (the invariant of `Rounds` together with the potential of `Protocol`), and proves one theorem: Protocol D is round-by-round sound with the errors of Theorem D', hence sound and knowledge sound (in the relativised form of Theorem K) with their sum. Tags: **[machine-checked]** means a Lean theorem that compiles with no `sorry` and depends on Lean's three axioms only; **[not formalized]** means no Lean statement exists. No file outside `lean/Soundness/`, `lean/Soundness.lean` and this note was edited.

## 0. Summary

1. **The composition goes through, for the whole ladder and the tail, with no change to any piece.** `protocolD_rbr`: over a finite field of characteristic two, for analysis constants $\tau > 0$, $M \ge 2q$ and $K_0$ with $K_0(K_0-1)(K_0-M) > 0$, Protocol D (any number of levels, any number of tail rounds, any number $J$ of input claims) has a round-by-round state function with exactly the errors of the table of Theorem D', rows M0 to M5. **[machine-checked]**
2. **One statement a paper can cite.** `protocolD_sound`: on every ladder whose levels satisfy the standing assumptions and $\mathrm{ListBound}$, for every prover strategy, the probability that the verifier accepts while it is not the case that the final polynomial descends to a member of the level-0 list that matches the commit-phase answers and satisfies all input claims, is at most the sum of the per-message errors. `protocolD_sound_plain` is Theorem D' composed (the verifier accepts false input claims), `protocolD_sound_extract` is Theorem K composed (the verifier accepts and the descent fails), `protocolD_sound_one_level` writes the sum out for one level. **[machine-checked]**
3. **The hypothesis is connected.** `protocolD_sound_of_HK` replaces $\mathrm{ListBound}$ by the bound for single-lane words with values in the subfield that contains the domain (through `Interleave`: Theorem I above $(n + 3d)/4$, or Proposition R2' for lists up to half the subfield). `protocolD_sound_unique` has no list hypothesis (unique-decoding range). `protocolD_sound_deployed_unique_le` has no hypothesis at all: on a concrete level over a field of $2^{128}$ elements with its domain $\mathrm{GF}(2^{64})$, every prover strategy wins with probability at most $2^{-109}$, and strategies exist (`strategy_nonempty_one_level`). `err_level0` gives the level-0 numbers: at most $2^{-110}$ for the points, $2^{-119}$ for the batching, $2^{-118}$ for a fold, $2^{-127}$ for a tail round, before their grinds. **[machine-checked]**
4. **No error, no missing hypothesis and no mismatch between the libraries was found.** The invariant of `Rounds` and the potential of `Protocol` meet through one arithmetic fact (the thresholds grow by at least one a round) and three identities that Lean accepts by unfolding. Section 7 lists what composing showed: the shape the state function must have when commitment and opening are one protocol, which standing assumptions are never used, and that $\mathrm{ListBound}$ is used only on a diagonal.
5. **What the theorem is about is a model**: prover messages are the objects themselves (interactive oracle model), and three things are abstract data with stated properties instead of Annex B's encoder: the map $U \mapsto \mathcal P_{g_U}$, the high part, and the tables of the tail. Section 8 says exactly what is not covered.
6. **Checked on `h4`** with Lean 4.36.0 and Mathlib `v4.36.0`: every module of `Soundness` against the prebuilt Mathlib, and a Lake build of all six libraries of the project from an empty build directory: `Build completed successfully (18369 jobs)`. All 67 files of `lean/` have the same SHA-256 in the repository and in the project built. Nothing was installed or built on the Mac.

## 1. How it was checked

Host `h4`, scratch directory `/data/whir_lean_scratch_33` (created for this, safe to delete). Lean `leanprover/lean4:v4.36.0`, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, Lake `5.0.0-src+611c117`; Mathlib tag `v4.36.0`, the revision of `lean/lake-manifest.json`, which was not edited (nor `lakefile.toml`, nor `lean-toolchain`).

- Run 1, per module: the modules of `DeepFold`, `Protocol`, `Rounds`, `Interleave` and then of `Soundness` compiled in dependency order with `lean -o`, with `-DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false`, from an empty output directory, against the Mathlib already built in `/data/lean436/formal/Statement/.lake/packages` (read only, through `LEAN_PATH`). No output: no error, no warning. Directory `proj/`.
- Run 2, the run to cite: the whole of `lean/` copied to `lakeproj/`, its `.lake/packages` copied from note 22's scratch project (same `lake-manifest.json` and `lean-toolchain`, compared by SHA-256; nothing was downloaded), the build directory removed, then `lake build DeepFold Interleave Constructions Protocol Rounds Soundness` on 8 cores (`taskset -c 0-7`, `LEAN_NUM_THREADS=8`, nice 10): `Build completed successfully (18369 jobs)`, exit status 0, 39 seconds. `lakefile.toml` sets `warningAsError`. The only messages are Lake's advisory that five files of the other libraries (`Constructions/Subspace.lean`, `DeepFold/Basic.lean`, `DeepFold/Counting.lean`, `Interleave/Basic.lean`, `Protocol/Potential.lean`) import `Mathlib` without the module system, which is not a Lean warning. Log: `/data/whir_lean_scratch_33/lake-build.log`.
- Hashes: the SHA-256 of each of the 67 files of `lean/` (the six libraries, their root files, the READMEs, the lakefile, the toolchain file, the manifest, `.gitignore`) is the same in the repository and in `lakeproj/` at the time of run 2; the list is `/data/whir_lean_scratch_33/built.sha` (its own SHA-256 starts `b29f13f4`). First eight hex digits of the `Soundness` sources as built: `RBR.lean` 669fe369, `State.lean` c4348002, `ProtocolD.lean` 872d5f09, `Sound.lean` 2339741f, `Extract.lean` a623db1c, `Hypothesis.lean` 1761d2a2, `Axioms.lean` 4cc5a049, `Soundness.lean` cbbd5c9f.
- No `sorry`, `admit`, `axiom` or `native_decide` occurs in the sources. `Soundness/Axioms.lean` runs `#print axioms` under `#guard_msgs` on all 83 theorems of the library: 81 depend on `propext`, `Classical.choice`, `Quot.sound`, one on `propext` alone, one on no axiom. The file is generated from the theorem names and the checker's output, and the build fails if a statement gains an axiom. A control file with one `sorry` and one wrong expectation was rejected by the same command line.
- `Axioms.lean` also instantiates `protocolD_rbr`, `protocolD_sound`, `fold_full`, `query_full` and `points_full` at `GaloisField 2 128`.

## 2. Round-by-round soundness, as defined (`RBR.lean`)

The definition follows Definition `def:rbr` of the leanVM document (`doc/leanvm/body/03-proving-primitives.tex`; Annex B's proof of `thm:rbr` checks its four properties). It was written from that definition; the `Spec` notion of `formal/lean_vm` was neither imported nor compared.

A protocol is a transition system `PublicCoin`: a type `Pos` of positions (partial transcripts that end with a verifier message, or anything the messages so far determine that fixes the rest of the protocol), for each position a type `Msg s` of prover messages and a finite type `Chal s` of verifier messages, of which the verifier sends a uniform one, and `next : ∀ s, Msg s → Chal s → Pos`. The message types may depend on the position, which is what a ladder of levels of different shapes needs. A protocol that has ended stays where it is.

```lean
structure StateFunction (Γ : PublicCoin) (start win : Γ.Pos → Prop) (err : Γ.Pos → ℚ)
    (doomed : Γ.Pos → Prop) (doomedP : ∀ s, Γ.Msg s → Prop) : Prop where
  start_doomed : ∀ s, start s → doomed s                                   -- (i)
  prover_doomed : ∀ s (p : Γ.Msg s), doomed s → doomedP s p                -- (ii)
  verifier_doomed : ∀ s (p : Γ.Msg s), doomedP s p →
    dens (fun c : Γ.Chal s => ¬ doomed (Γ.next s p c)) ≤ err s             -- (iii)
  doomed_not_win : ∀ s, doomed s → ¬ win s                                 -- (iv)

def RBRSound (Γ : PublicCoin) (start win : Γ.Pos → Prop) (err : Γ.Pos → ℚ) : Prop :=
  ∃ doomed doomedP, StateFunction Γ start win err doomed doomedP
```

`doomed` is the state function on positions and `doomedP` its value after a prover message. `start` is the condition under which the run begins doomed (in the document, "the statement is false"), `win` the event the adversary wants (false at positions where the protocol has not ended), and `err s` the error of the verifier message sent from `s`. `dens` is `Protocol.dens`: the number of messages with the property over the number of messages.

A prover strategy for `n` rounds from `s` (`PublicCoin.Strategy`) is a message at `s` and a strategy for each verifier message: deterministic, and free to depend on everything the verifier has sent. `winProb win n s σ` is the probability over the `n` verifier messages that the position reached satisfies `win`.

**The union bound** (`StateFunction.winProb_le`, `RBRSound.winProb_le`). **[machine-checked]** If `E n s` is a budget (nonnegative, and `err s + E n (next s p c) ≤ E (n + 1) s` for all `p`, `c`), then from a starting position every strategy has `winProb win n s σ ≤ E n s`. This is the sentence after `def:rbr`, "interactive soundness error is then at most the sum of the errors". `RBRSound.winProb_le_mul` is the case of a uniform bound, `n ε`. A bound for every deterministic strategy gives the same bound for randomized ones by averaging (not stated in Lean).

## 3. The full state and its transitions (`State.lean`)

```lean
def FullState (τ : ℚ) (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (s Θ : ℕ) (k r : ℕ) (O : Word K r)
    (z : Fin s → K × K) (v : Fin s → K) (W : (Lane r → K[X]) →ₗ[K] K) (σ : K)
    (B : (Lane r → K[X]) → Prop) : Prop :=
  Doomed D O d (thr k) (exL k r) z v W σ B ∧ levelPot τ D d thr s Θ z k r O < 1
```

This is $(\mathrm I_{i,k})$ and $(\mathrm G_{i,k})$ of note 14 section 4.2 after $k$ fold rounds of a level with $r$ to come: `Rounds.Doomed` at the agreement `thr k` $= A^{(i,k)}$ with the exponents $e_k$ (`Protocol.exL`), and the potential $T_k$ of the level's points (`Protocol.levelPot`) below one. `Θ` is the threshold $K_0(K_0-1)(K_0-M)$ of the triple count, `B` the predicate of the relativised invariant (true for plain soundness).

Each transition is a probability over the verifier's message, for every prover message, with the error of Theorem D'. All **[machine-checked]**.

| message | statement | from | to | error | joins |
| --- | --- | --- | --- | --- | --- |
| M0, points | `points_full` | a committed word with $\mathrm{ListBound}$ | not bad: for every answer vector, sent after the points, at most one list member matches, and $T_0 < 1$ | $\bigl[\binom L2 + \frac{L^3q^6}{\Theta}\sum_{j<\ell}\tau^{-j}\bigr]\epsilon^s$, $\epsilon = (d + 2^\ell - 1)/q$ | `Protocol.dens_not_good_le`, `Protocol.pinned_unique` |
| M1, $\lambda_0$ | `batch_full` | good points, answers, $J$ claims false relative to `B` | `FullState` at round 0 for the batched claim | $(J - 1)/q$ | `Rounds.batch_transition`, Lemma P |
| M2, fold | `fold_full` | `FullState` at $(k, r + 1)$, any $(v_G, v_F, \sigma_0, \sigma_1, \varphi)$ | `FullState` at $(k + 1, r)$ for the fold, the updated claim and values, and `pull B` | $(K_0 - 1)/q^2 + \tau$, and $(K_0 - 1)/q^2$ if $r = 0$ | `Protocol.levelPot_step`, `Rounds.fold_transition` |
| M3, queries and $\lambda_{i+1}$ | `query_full` | $(\mathrm I_{i,\ell_i})$ of the level that ends, good points of the next word, their answers | `FullState` at round 0 of the next level | $((A - 1)/n)^t + (s + t)/q$ | `Rounds.query_transition_pinned`, `Doomed.one_lane` |
| M4, last queries | `final_full` | $(\mathrm I_{I-1,\ell})$, a final polynomial of degree at most $d$ | point check, query check, running claim and `B` on the polynomial all hold | $((A - 1)/n)^t$ | `Rounds.final_transition` |
| M5, tail round | `step_tail` (in `ProtocolD.lean`) | a false sumcheck claim on two tables, a round polynomial of degree at most 2 | check passes and the next claim is true | $2/q$ | `Rounds.tail_round_transition` |

How the state is re-initialized at a level boundary, precisely (`step_handover`, `query_full`): after the last fold of level $i$ the state is $(\mathrm I_{i,\ell_i})$ with $T_{\ell_i} = 0$ (`levelPot_zero`). The prover commits the next word and the high part. The point message of level $i + 1$ leads to the state "$(\mathrm I_{i,\ell_i})$ and the new points are good for the new word" except with probability $\varepsilon^{\mathrm{pt}}_{i+1}$; the old condition does not mention the new points. The query message then leads to `FullState` at round 0 of level $i + 1$: its invariant part is the conclusion of M3 (which uses the separating half of goodness), and its potential part is the other half of goodness, which the queries do not touch. The old potential is dropped. This is note 14's state after the points $z^{(i+1)}$, word for word.

Two technical bridges were needed and have no content: `dens_eq_card_div` (the densities of `Rounds` are quotients of cardinalities with the decidability instance the elaborator picks for the predicate, which is not syntactically the classical one of `Protocol.dens`), and `card_queries_le`, `card_queries_prod_le` (`Rounds` counts query vectors in `Fintype.piFinset (fun _ => D)`; a verifier message here is a vector `Fin t → D` with `D` as a type).

## 4. Protocol D as a transition system (`ProtocolD.lean`)

A level is `Level K`: domain `D`, degree bound `d`, fold rounds `ℓ`, points `s`, queries `t`, thresholds `thr` (`thr k` $= A^{(i,k)}$, a function on all of $\mathbb N$; take `thr k` $= A^{(i,0)} + k$), the list size `L` the analysis assumes, and the linear map `low` from the level's tuples to polynomials ($U \mapsto \mathcal P_{g_U}$). A run starts at `Pos.commit lv rest`, the ladder being `lv :: rest`. `protocolD K T J` is the protocol with tail `T` and `J` input claims.

| position | prover sends | verifier sends | note 14 |
| --- | --- | --- | --- |
| `commit` | the level-0 word $O^{(0)}$, a function $K \to \{0,1\}^{\ell_0} \to K$ | $s_0$ points of $K^2$ | C1, C2 |
| `opening` | answers $y$ and $J$ weighted claims (any linear functionals on tuples, with values), which may depend on the points | $\lambda_0$ | C3, the claims of Open, O1 |
| `fold`, $r + 1$ rounds to come | $(v_G, v_F, \sigma_0, \sigma_1)$ and $\varphi_1..\varphi_s$ | $(\alpha, \beta)$ | 1(a), 1(b), 1(c) |
| `fold`, no round to come, a next level | the next word $O'$ and a high part $C$ (`Handover`) | the next level's points | 2(a), 2(b) |
| `boundary` | the answers $y'$ | $t$ positions of $D$ and $\lambda_{i+1}$ | 2(b) to 2(e) |
| `fold`, no round to come, last level | the final polynomial $P$, of degree at most $d$ (`FinalMsg`) | $t$ positions of $D$ | 3 |
| `tail`, $r + 1$ variables | a round polynomial of degree at most 2 | a scalar | 3, the tail |
| `tail`, no variable | nothing | nothing (the terminal check) | 3 |
| `done` | | | |

The updates are those of `Rounds` and `Protocol`, unchanged: `foldW`, `foldVal`, `foldWeight`, `foldClaim` in a fold round; `batchW`, `batchC` at the opening; `nextW`, `nextC` at a boundary (the residual, the converted point claims and the query claims with the powers $\lambda^0, \lambda^1..\lambda^s, \lambda^{s+1}..\lambda^{s+t}$). The verifier's decision is the proposition `acc` of the `done` position: the point check and the query check of step 3, every sumcheck check, and the terminal check.

Three things are abstract data with stated properties, where the real protocol has Annex B's encoder:

- `low` of each level is any linear map.
- The high part `C` of a `Handover` is any polynomial with $\langle W, C\rangle = 0$ for the running weight $W$ at that point, and $\deg(\mathrm{low}\,U + C) \le d$ for every member $U$ of the list of the new word. In the protocol $C = \widehat W_\kappa H$, the first property is "weights see only low parts" and the second is (S1).
- The tail `Terminal` is a number $\nu$ of rounds and two tables on $\{0,1\}^\nu$, functions of the running weight and the final polynomial; a `FinalMsg` is a polynomial for which their inner product is $\langle W, P\rangle$. In the protocol the tables are the terminal weight and the low part $f^{(I)}$. `Terminal.direct` has no round: the verifier checks $\langle W, P\rangle = \sigma$ itself.

So the model's prover has at least the moves of the real prover provided Annex B's identities hold for the real encoder; those identities are not formalized (section 8).

Two components of a position are read by the analysis only, never by the verifier. `G` is the extraction predicate on the tuples of the current round: at round 0 of level 0 it is `claimsHold` ($U$ is in $\mathrm{List}(O^{(0)}; A^{(0,0)}, d^{(0)})$, matches all commit-phase answers and satisfies all $J$ claims); a fold round by $c$ replaces it by `descend` ($P$ agrees with the fold $O_c$ on at least $A^{(i,k+1)}$ columns and some near tuple of the unfolded word on that agreement set satisfies `G`); a boundary by $U \mapsto G(\mathrm{low}\,U + C)$. `tru` is the proposition that some tuple satisfies `claimsHold`, that is, that the input claims are true in the sense of Theorem D'. At the end `ext` is `G` on the final polynomial.

**The state function** `doomed` (note 14 section 4.2 with the predicate of section 5.1):

- `commit`: nothing (the levels satisfy the standing assumptions `Level.OK`).
- `opening`: the points are good for the committed word (`Protocol.Good`).
- `fold`: `FullState` with `B := ¬ G`.
- `boundary`: `Doomed` of the level that ended, and the new points are good for the new word.
- `tail`: `ext`, or a check has failed, or the sumcheck claim on the current tables is false.
- `done`: `¬ (acc ∧ ¬ ext)`.

Every case also carries that the levels still to be played satisfy `Level.OK` and that `G P → tru` for all `P`. The state function does not change with a prover message (`doomedP s p := doomed s`), so (ii) holds by definition and (iii) is "from a doomed position, whatever the prover sends". This is note 14's remark that every condition is a function of the transcript up to the last verifier message.

**The errors** `err`: `errPoints` $= \varepsilon^{\mathrm{pt}}$ at `commit` and at a `fold` position with no round to come and a next level; $(J - 1)/q$ at `opening`; `errFold` $= (K_0 - 1)/q^2 + \tau$ at a `fold` position with at least two rounds to come and $(K_0 - 1)/q^2$ with one; `errQuery` $= ((A - 1)/n)^t$ at the last level's end and `errQuery` $+ (s + t)/q$ at a `boundary`; $2/q$ at a `tail` position with a variable left; 0 at the terminal check and at `done`.

**The winning conditions**, all on `done acc ext tru`: `win` is `acc ∧ ¬ (ext ∧ tru)`; `winPlain` is `acc ∧ ¬ tru` (the verifier accepts false input claims); `winExtract` is `acc ∧ ¬ ext` (the verifier accepts and the descent from the final polynomial fails). Both imply `win`.

## 5. The theorems

```lean
theorem protocolD_rbr [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) :
    RBRSound (protocolD K T J) (start M) win (err τ K₀ M J)

theorem protocolD_sound [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (rest : List (Level K))
    (hOK : ∀ l ∈ lv :: rest, l.OK M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv rest)) :
    (protocolD K T J).winProb win n (Pos.commit lv rest) σ ≤
      budget T τ K₀ M J (Pos.commit lv rest)

theorem protocolD_sound_one_level [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (hOK : lv.OK M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv [])) :
    (protocolD K T J).winProb win n (Pos.commit lv []) σ ≤
      errPoints τ K₀ M lv + ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) +
        (lv.ℓ * (((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2) + ((lv.ℓ - 1 : ℕ) : ℚ) * τ) +
        (errQuery lv lv.ℓ + T.ν * (2 / (Fintype.card K : ℚ)))

theorem protocolD_sound_deployed_unique_le (n : ℕ)
    (σ : (protocolD E128 (Terminal.direct E128) 512).Strategy n (Pos.commit levelU [])) :
    (protocolD E128 (Terminal.direct E128) 512).winProb win n (Pos.commit levelU []) σ ≤
      1 / 2 ^ 109
```

`K` is a type with `[Field K] [Fintype K]`, `T : Terminal K`, `tripleThr K₀ M = K₀ * (K₀ - 1) * (K₀ - M)`, `start M` holds at the positions `commit lv rest` whose levels all satisfy `Level.OK M`, and `Level.OK M lv` is: $\ell \ge 1$; $D$ nonempty; $\binom{n}{2} \le M$; `thr k + 1 ≤ thr (k + 1)`; and $\mathrm{ListBound}$ in the form "for all $k + r = \ell$, every word with $r$ lane variables has at most `lv.L` tuples of degree at most $d$ agreeing with it on at least `thr k` columns".

**In words** (`protocolD_rbr` with `protocolD_stateFunction`). Let $K$ be a finite field of characteristic two with $q$ elements, $\tau > 0$ rational, and $M \ge 2q$, $K_0$ integers with $K_0(K_0-1)(K_0-M) > 0$. In Protocol D with any tail and $J$ input claims, call a position doomed as in section 4. Then: (i) the empty transcript on a ladder satisfying the standing assumptions and $\mathrm{ListBound}$ is doomed; (ii) no prover message leaves the doomed set; (iii) from a doomed position, for every prover message, the verifier's message leads to a position that is not doomed with probability at most $\varepsilon^{\mathrm{pt}}_i$ for the points of level $i$, $(J - 1)/q$ for $\lambda_0$, $(K_0 - 1)/q^2 + \tau$ for a fold challenge and $(K_0 - 1)/q^2$ for the last of a level, $((A_i - 1)/n_i)^{t_i} + (s_i + t_i)/q$ for the queries of a level with $\lambda_{i+1}$, $((A_{I-1} - 1)/n_{I-1})^{t_{I-1}}$ for the last queries, and $2/q$ for a tail round; (iv) at a doomed end position, if the verifier has accepted then the final polynomial descends to a member of $\mathrm{List}(O^{(0)}; A^{(0,0)}, d^{(0)})$ that matches all commit-phase answers and satisfies all input claims.

**In words** (`protocolD_sound`). Under the same hypotheses, on every such ladder, for every deterministic prover strategy and every number of rounds, the probability over the verifier's messages that the verifier accepts and it is not the case that [the final polynomial descends to a list member as in (iv), and the input claims are true] is at most
$$\varepsilon^{\mathrm{pt}}_0 + \frac{J - 1}{q} + \sum_{i}\Bigl[\ell_i\frac{K_0 - 1}{q^2} + (\ell_i - 1)\tau\Bigr] + \sum_{i < I-1}\Bigl[\varepsilon^{\mathrm{pt}}_{i+1} + \Bigl(\frac{A_i - 1}{n_i}\Bigr)^{t_i} + \frac{s_i + t_i}{q}\Bigr] + \Bigl(\frac{A_{I-1} - 1}{n_{I-1}}\Bigr)^{t_{I-1}} + \frac{2\nu}{q},$$
which is `budget` at the starting position (a recursive definition over the ladder; `budget_step` shows it is the error of the next message plus the budget of the next position, `budget_one_level` and `budgetFolds_eq` unfold it for one level). The number of rounds needs no care: `rounds` counts the verifier messages to come, `rounds_next` shows a round consumes one, `done_of_rounds_eq_zero` that the protocol has then ended, and an ended protocol stays where it is, so the bound at `n = rounds` is the bound for the whole run. `chal_nonempty_of_doomed` shows the verifier's message set is nonempty at every doomed position.

`protocolD_sound_plain` and `protocolD_sound_extract` are the same bound for the two events of Theorem D' and Theorem K: "the verifier accepts although no member of the level-0 list matches the answers and satisfies all claims", and "the verifier accepts and the descent from the final polynomial does not reach such a member".

**The extraction predicate is the extractor's acceptance condition** (`Extract.lean`). **[machine-checked]** `descend_iff_unique`: when $A^{(i,k+1)} \ge d + 3$ (which is (S2)), `descend` says that the tuple agrees with the fold on at least $A^{(i,k+1)}$ columns, that the unfolded word has a near tuple on that agreement set, that it is the only one, and that it satisfies `G`. `descend_step` (from `Rounds.descent_step`): for a tuple of degree at most $d$, that near tuple is in the list of the previous round and folds back to the tuple. So `ext` says: the chain of unique near tuples that the descent of note 14 section 5.2 computes from the final polynomial ends in a member of the level-0 list that matches the answers and satisfies the claims. `claimsHold_unique` (Corollary K2, uniqueness): for good points there is at most one such member, the one the commit-phase answers pin.

## 6. The hypothesis and the numbers (`Hypothesis.lean`)

- `Level.OK.of_rsListBound`: a level whose domain is the image of points `D₀` of a subfield `F` satisfies `Level.OK` if `Interleave.RSListBound D₀ K (Lane r) d (thr 0) L` holds for every $r \le \ell$ (with the assumptions that are not about lists). The link is `card_listW_le_of_rsListBound`. **[machine-checked]**
- `Level.HK`, `Level.HK.ok`, `protocolD_sound_of_HK`: the hypothesis is `Interleave.RSListBound₁ D₀ d (thr 0) L₁`, the bound $L_1$ for single words $F \to F$ at the level's first threshold, with $d < A^{(i,0)}$ and either $A^{(i,0)} > (n + 3d)/4$ or $2L_1 \le |F|$; the level's list size is $2L_1 - 1$. The conclusion is the soundness statement of section 5. This is note 14 section 7.3 ("single $K$-valued words suffice with at most a factor two") as the hypothesis of the composed theorem. **[machine-checked]**
- `Level.Unique`, `protocolD_sound_unique`: if $A^{(i,0)} > (n + d)/2$ the level's list size is one and no list hypothesis is left. **[machine-checked]**
- `levelU`, `protocolD_sound_deployed_unique`, `budget_levelU_le`, `protocolD_sound_deployed_unique_le`: the field is `Interleave.E128` ($2^{128}$ elements, a quadratic extension of $\mathrm{GF}(2^{64})$), the level has the whole of $\mathrm{GF}(2^{64})$ as domain, $d = 2^{24} + 5$, six fold rounds, twelve points, 128 queries, thresholds $2^{63} + 2^{24} + k$, list size one; $K_0 = 2^{137}$, $M = 2^{129}$, $\tau = 2^{-119}$, 512 claims, no tail. Every hypothesis of `protocolD_sound` is discharged, the budget is at most $2^{-109}$, and `strategy_nonempty_one_level` shows that the set of strategies the statement quantifies over is not empty. So the theorem is not vacuous: its hypotheses are satisfiable together at the deployed field size, and it bounds a real quantity by a small number. **[machine-checked]**
- `err_level0` (with `errPoints_level0`, `errFold_level0`, `errFold_level0_last`): over a field of $2^{128}$ elements, for a first level with $d = 2^{24} + 5$, $\ell = 6$, $s = 12$, $L = 2^{40}$, with $K_0 = 2^9q$, $M = 2q$, $\tau = 2^{-119}$ and $J \le 512$: `err` is at most $2^{-110}$ at `commit`, $2^{-119}$ at `opening`, $2^{-118}$ at every `fold` position with a round to come and $2^{-119}$ at the last, $2^{-127}$ at a tail round. These are the errors before the grinds of note 20 section 6.2 (15, 7, 7 and 0 bits). The query message's error depends on $t$ and $A$ and is not instantiated for a list of $2^{40}$. **[machine-checked]**

## 7. What composing showed

No error and no missing hypothesis in note 14, and no mismatch between the libraries. In decreasing order of interest:

1. **The shape of the state function when commitment and opening are one protocol.** Theorem D' defines false input claims from the commit-phase answers and the claims, which the prover sends after the level-0 points; its property (i) reads "the start is the definition of false input claims together with goodness, whose failure is charged to M0". As one protocol in the sense of `def:rbr`, with the claims chosen after the points, "the claims are false" cannot be part of a state that survives prover messages: the prover leaves it by naming true claims. The composed statement therefore has the form of Theorem K with the predicate note 14 section 5.1 names in passing ("does not satisfy the relation"): `B := ¬ G`. With it the starting condition is trivial, the hypothesis `hfalse` of M1 is a tautology (`step_opening`), and Theorem D' is the corollary `protocolD_sound_plain`. A consequence worth stating: the batching error $(J - 1)/q$ and all later errors are paid on every run, whether the claims are true or false, which is what a statement about an adaptively chosen claim needs. Nothing in note 14 is wrong here; the two-phase wording just does not survive formalization as written.
2. **The invariant and the potential meet in one arithmetic fact and three identities.** `Rounds.fold_transition` wants the invariant at agreement $A - 1$ and the points outside the exceptional set of the round at agreement $A$; `Protocol.levelPot_step` gives the latter at `thr (k + 1)`. They fit when `thr k + 1 ≤ thr (k + 1)` (in note 14, equality). The identities, which Lean accepts by unfolding definitions: `Rounds.exHalves (2 ^ k) (exL (k + 1) r)` is `exL k (r + 1)`; `Rounds.foldWord c O` is `Protocol.foldW O c`; `exL k 0` is the zero map, which is what `Doomed.one_lane` asks for at the end of a level. `Rounds.half₀` and `Protocol.half₀` (and `half₁`) are two definitions of one thing, an ambiguity for a file that opens both namespaces and nothing more.
3. **Standing assumptions that the composed soundness statement never uses.** (S2) ($d + 2 \le A^{(i,0)}$, $A_i \le n_i$): not used by `protocolD_rbr` or by any of the three soundness statements. It is used only to say that the near tuple of a descent step is unique (`descend_iff_unique`), that is, to identify the existential predicate `ext` with the output of a decoder. $\tau < 1$: not used. $K_0 > M$: used only through $K_0(K_0-1)(K_0-M) > 0$. (S1) enters only as the two properties of the high part in `Handover`. What is used: $\ell_i \ge 1$, $D_i \ne \emptyset$, (S3) as $\binom{n_i}{2} \le M$, $M \ge 2q$, $\tau > 0$, the growth of the thresholds, and $\mathrm{ListBound}$.
4. **$\mathrm{ListBound}$ is used on a diagonal only.** `Level.OK.listBound` asks, for a word with $r$ lane variables, a bound at the agreement $A^{(i,\ell-r)}$: the committed word at $A^{(i,0)}$, a word folded $k$ times at $A^{(i,k)}$, single-lane words at $A_i$. Note 14 asks every lane count at $A^{(i,0)}$, which is stronger (`Protocol.listBound_level`). The difference is at most $\ell_i$ columns and does not change any number of note 14, but it is the exact hypothesis of the composition.
5. **The level boundary is as note 14 says**, with the state between the new points and the queries equal to "$(\mathrm I_{i,\ell_i})$ and the new points are good" (section 3). The suspicion that the invariant of `Rounds` and the potential of `Protocol` might not fit there is not borne out: the old potential is identically zero after the last fold, and the new one is a function of the new word and the new points only.
6. **Where Annex B is assumed, exactly**: three properties (section 4): $\langle W, C\rangle = 0$ and $\deg(\mathrm{low}\,U + C) \le d$ for the high part, and $\langle W, P\rangle = \sum_x \mathrm{wtab}(x)\,\mathrm{ftab}(x)$ for the final polynomial. Nothing else about the novel basis, the column weights or the terminal weight enters the composition. In particular the weights need not be functionals of low parts anywhere except at these two points.
7. **Small things.** $J - 1$ is truncated subtraction, so the statement covers $J = 0$. `errQuery` at a position reads `thr k` for the number $k$ of rounds the position records, which is $\ell_i$ on every run from `commit`. The state function is proved for all positions, reachable or not.

## 8. What the theorem does not cover

- **Annex B's identities for the real encoder and weights.** That the novel-basis encoder provides `low` (linear), that $C = \widehat W_{\kappa}H$ has the two properties of `Handover` for every running weight the protocol can reach, that the terminal weight and $f^{(I)}$ are tables with the property of `FinalMsg`, that the verifier's folded column value is the folded word, that `lem:colweight` holds at points outside the domain (it is inside `nextW`, which is defined from `low`). **[not formalized]**
- **Completeness.** No honest prover is defined. `strategy_nonempty_one_level` shows strategies exist on one level without tail; on a ladder or with a tail the existence of a hand-over or final message depends on the abstract data. **[not formalized]**
- **Fiat-Shamir and grinding.** The statements are about the interactive protocol with uniform verifier messages. The per-message errors are before any grind; that a grind of $b$ bits divides an error by $2^b$, and the passage from round-by-round soundness to the non-interactive protocol (BCS), are not stated. **[not formalized]**
- **Merkle commitments.** A committed word is a function sent by the prover (interactive oracle model). Binding of the hash commitment and the extraction of the committed words from the adversary's hash queries are outside. **[not formalized]**
- **The outer protocol.** The sixteen ring-switching scalars in the batching message (row M1 is $(J_0 - 1)/q$ here, $(J_0 + 1)/q$ in the stacked opening), the stacking, whatever happens between the commitment and the opening (goodness of the points is a property of the word and the points, so it survives, but no outer message is modeled), several openings of one commitment, the bytecode claim and the recursion. **[not formalized]**
- **The ladder schedule D$_S$** of notes 15 and 20 (fresh points with the fold challenges). `Protocol/Ladder.lean` has Lemma S; the protocol composed here is Protocol D, one batch of points a level. **[not formalized]**
- **The extractor as an algorithm.** `ext` is a predicate; that the near tuple is found by one-error decoding in polynomial time, and the extractor's interface with the outer protocol, are not stated. **[not formalized]**
- **The hypothesis.** $\mathrm{ListBound}$, or `H_K`, is a hypothesis outside the unique-decoding range. The Johnson and counting instances of note 14 section 2 are not connected. **[not formalized]**
- **Numbers beyond level 0.** `err_level0` is level 0 at list $2^{40}$; the other rows of the tables of note 14 section 7.4 and note 20 section 6.3, and any query count at a lowered threshold, are not instantiated. Each is arithmetic on the general statement. **[not formalized]**
- **Randomized provers** (immediate by averaging) and **a comparison with the `Spec` of `formal/`**. **[not formalized]**

## 9. Reproduction

`lean/Soundness/README.md`. On a build host: `cd doc/whir_soundness_gap_notes/lean && lake exe cache get && lake build DeepFold Interleave Constructions Protocol Rounds Soundness`. The project that was checked is `h4:/data/whir_lean_scratch_33/lakeproj`, with `lake-build.log`, the build script `lake_build.sh` and the hash list `built.sha` one directory up; `proj/` beside it is the per-module check of run 1 (script `check.sh`).
