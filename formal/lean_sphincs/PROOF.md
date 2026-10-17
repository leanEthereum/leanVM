# The leanSPHINCS proof

`Sphincs` models the scheme of `crates/signatures/src/lean_sphincs`, specified in `doc/lean_sphincs`: the one-time keys of a height-26 tree sign few-time keys, each a two-level WOTS forest of 8 trees of height 4, each leaf of a tree the hash of two subtrees of height 3 over WOTS keys. The digest picks, per tree, a leaf, a WOTS key in each of its two subtrees and a codeword for each WOTS key (`lut`, entries in `{0..4}` summing to 5); the signature opens each chain of the two WOTS keys at position `4 - d_i`. The proof forks, module by module, the one of the FORS variant of leanSPHINCS; the `SphincsFors` and `SphincsBase` modules here are those it imports.

No tree of the forest has a root hash. A subtree is hashed up to level 2 and a tree leaf is the hash of the four level-2 nodes `m_0[0] ‖ m_0[1] ‖ m_1[0] ‖ m_1[1]` of its two subtrees; a tree is hashed up to level 3 and the few-time key is the hash of the sixteen level-3 nodes `t_0[0] ‖ t_0[1] ‖ … ‖ t_7[0] ‖ t_7[1]`. The signature is unchanged (3 path elements per subtree, 4 per tree): the last path element is the other top node of its tree. The verifier folds 2 levels in a subtree and 3 in a tree and puts the node it reached and the last path element in index order (`orderTops`: the reached node first when bit 2 of the WOTS-key index, bit 3 of the leaf index, is 0).

Final statement: `Sphincs.Lifetimes.requestedSecurity`, 127 classical bits (SUF-CMA in the ROM) for the deterministic Lean signer at subtree heights 26, 20, 14, 13, 12, 10, 8.

| b | proved N | cover attack | best known attack | proved / best known |
| ---: | ---: | ---: | ---: | ---: |
| 26 | 1,383,000,000 | 1.43966e9 | 1.44e9 | 96% |
| 20 | 26,030,000 | 2.85120e7 | 2.84e7 | 92% |
| 14 | 480,900 | 5.57495e5 | 5.40e5 | 89% |
| 13 | 247,000 | 2.89047e5 | 2.78e5 | 89% |
| 12 | 126,900 | 1.49820e5 | 1.43e5 | 89% |
| 10 | 33,490 | 4.02171e4 | 3.76e4 | 89% |
| 8 | 8,830 | 1.07843e4 | 9.9e3 | 89% |

The cover attack column is the lifetime in the cover model: the number of signatures at which a digest query covers a forest with probability `2^-127` (Poisson loads of the kept indices). The best known attack also uses the WOTS+C unit-neighbour route, which applies unchanged: a forger that sees the realized key takes the better of the cover rate `Y` and the rate `r` of that route, and the lifetime is the largest `N` with `E[max(Y, r)] ≤ 1`. It is 100 / 100 / 97 / 96 / 96 / 94 / 92% of the cover lifetime (`b = 26 … 8`). `scripts/forest_attack.py` computes both columns. `Y` comes from a Monte Carlo of the realized key (loads, leaves, WOTS keys, codewords), with about 0.3% of noise on `N` and 0.6% at `b = 8`: the column has three digits and the ratios are good to about a point. The rate is `r = 0.9694`: a search of about `2^116` hashes for a neighbouring encoding, then one chain preimage at `2 · 2^-128` per query, is at its best after about `2^122` queries. A rate between 0.95 and 0.98 moves the lowest ratio between 87.5% and 89.4%.

## The codeword table

`lut` (`Scheme.lean`, `codewordCodes`) is a list of 256 codewords `d ∈ {0..4}^6` with digit sum 5; the 8-bit digest field of a WOTS key is the index. The table is a rule: sort the 246 codewords of digit sum 5 by decreasing `Σ d_i²`, then lexicographically; entry `t` is codeword number `t mod 214` (`codewordRule`, and `codewordCodes_eq_rule`, checked by the kernel). It holds 214 codewords, and the first 42 twice:

| digits of the codeword | `Σ d_i²` | codewords | in the table | entries |
| --- | ---: | ---: | --- | ---: |
| `{4,1}` | 17 | 30 | all, twice each | 60 |
| `{3,2}` | 13 | 30 | the first 12 twice, 18 once | 42 |
| `{3,1,1}` | 11 | 60 | all, once | 60 |
| `{2,2,1}` | 9 | 60 | all, once | 60 |
| `{2,1,1,1}` | 7 | 60 | the first 34, once | 34 |
| `{1,1,1,1,1}` | 5 | 6 | none | 0 |

With `f(t)` the probability that a uniform entry is covered by the componentwise maximum of `t` uniform entries, `f(1..6)` = 0.005188, 0.067847, 0.172139, 0.280345, 0.376068, 0.456117: weight on the codewords with few large digits costs a little at one signature (`f(1) = Σ w_d² / 256²`) and gains from two on. At most 123 entries have a given digit at least one, which sets the reveal rate of the contact bound.

Every entry has digit sum 5 (`Completeness.lut_sum`, `Cost.lut_sum`), so a WOTS key is verified with exactly 5 chain steps: the verification cost and the signature size below do not depend on the table. The proof uses the table through that lemma, through `litCount_le_all` (`BridgeRevealRate.lean`) and through the counts `pmfT` of `H0Tables.lean` (a fold over the 256 indices: a repeated codeword is a count of 2); nothing uses that the entries are distinct. `scripts/forest_table.py` holds the table and computes from it the Lean literal and the kernel-checked tables `fTab`, `f2Tab` (`H0FTab.lean`), `P1tab`, `P2tab` (`H0PTab.lean`) and `PHtab` (`H0NTab.lean`); `scripts/forest_certificates.py` imports it and refuses to run if the Lean sources hold other tables.

No `sorry`, no `native_decide`, no new axioms: `Sphincs/Axioms.lean` guards every public theorem (`propext`, `Classical.choice`, `Quot.sound` only). Certificates are exact rationals checked by the kernel (`decide +kernel`). `LifetimeCertificates.lean` stores only the scalars of each Poisson table (`m`, `P`, `J`, `n1`), option (`c1`, `θ`, `s`, `cthr`) and near certificate: `H0Fill.lean` rebuilds their lists (`fillPoisT`, `fillOpt`, `fillOptN`, the same functions as in the script) and the unchanged checkers check the result. The options of a cover are checked one by one with their bound `B` (`checkOptB`), and the chain of the cover is checked on these bounds (`checkCoverW_of`, `checkCoverH_of`).

## Build

```
lake exe cache get
lake build
```

Table: `python3 scripts/forest_table.py info` (composition), `check` (the Lean sources hold the tables of the script), `write` (rewrite them). Certificates: `python3 scripts/forest_certificates.py emit` (writes `Sphincs/LifetimeCertificates.lean` and `Sphincs/Lifetimes.lean`; checking the former is most of the build); `python3 scripts/forest_certificates.py check B N LX` checks one set in Python with the same exact arithmetic; `maxn B N0 [STEP LXLO LXHI]` searches the largest `N` over a grid of splits `lx`. Axiom guards: `lake env lean scripts/ForestTheorems.lean` then `python3 scripts/forest_axioms.py` (`prepare`, then `emit`; see the script).

## Hash inputs

Key generation first hashes the key's seed `S0` into the scheme seed `S = H(leanSPHINCS ‖ S0)` (`schemeSeedInput`, `schemeSeed`): the 11 ASCII bytes of `leanSPHINCS` then the 32 bytes of `S0`, 43 bytes, the whole 32-byte output kept. Every other hash input is `P ‖ A ‖ payload` (`Scheme.lean`: `tweakableHashInput`, `keygenHashInput`, `randomizerHashInput`): the 16-byte public parameter, then the 16-byte address `A = lo (4 bytes) ‖ hi (3 bytes) ‖ (type + 32·step) ‖ 0^8` with `lo` and `hi` little endian (`fieldBytes`), then the payload, which starts at byte 32. There is no other exception: the parameter derivation (under `P = 0`), the randomizer base, the seed derivations and the surrogates have the same address format, and their `seed` is `S`. `Th` keeps the first 16 bytes of the hash. The public key is `root ‖ P`, 32 bytes. Forest positions: tree `c < 8`, leaf `s < 16`, subtree `j < 2`, WOTS key `a < 8`, chain `i < 6`, `idx` the 26-bit instance. A seed derivation of chain starts is addressed by a pair of chains `t` (chains `2t` and `2t + 1`): `t < 32` in a WOTS+C key, `t < 3` in a forest WOTS key.

| call | type | step | hi | lo | payload |
| --- | ---: | --- | --- | --- | --- |
| WOTS+C chain secrets `2t`, `2t + 1` (both halves of the hash) | 0 | 0 | `t` | leaf | seed |
| WOTS+C chain step onto position `to` | 1 | `to − 1` | chain | leaf | value |
| WOTS+C leaf | 2 | 0 | 0 | leaf | 64 chain ends |
| tree node | 3 | 0 | level | node | left ‖ right |
| WOTS+C encoding | 4 | 0 | 0 | leaf | message ‖ counter (4 bytes) |
| parameter derivation, under `P = 0` | 5 | 0 | 0 | 0 | seed |
| randomizer base `R0` | 7 | 0 | 0 | 0 | seed ‖ message |
| message digest | 12 | 0 | 0 | 0 | message ‖ randomizer |
| surrogate sibling | 13 | 0 | level | 0 | seed |
| forest chain secrets `2t`, `2t + 1` (both halves of the hash) | 14 | 0 | `c + 8s + 128j + 256a + 2048t` | `idx` | seed |
| forest chain step from position `t` | 15 | `t` | `c + 8s + 128j + 256a + 2048i` | `idx` | value |
| forest WOTS-key leaf | 16 | 0 | `c + 8s + 128j + 256a` | `idx` | 6 chain tops |
| subtree node, level 1 and 2 | 17 | 0 | `c + 8s + 128j + 256·level + 1024·node` | `idx` | left ‖ right |
| tree leaf | 18 | 0 | `c + 8s` | `idx` | `m_0[0] ‖ m_0[1] ‖ m_1[0] ‖ m_1[1]`, the level-2 nodes of the two subtrees (64 bytes) |
| forest tree node, level 1 to 3 | 19 | 0 | `c + 8·level + 64·node` | `idx` | left ‖ right |
| few-time public key | 20 | 0 | 0 | `idx` | `t_0[0] ‖ t_0[1] ‖ … ‖ t_7[0] ‖ t_7[1]`, the level-3 nodes of the 8 trees (256 bytes) |

In 64-byte blocks: the scheme seed is 43 bytes, a chain step 48 and a node 64 (1 compression), a forest WOTS-key leaf 128 and a tree leaf 96 (2), the key 288 (5), a one-time leaf 1,056 (17), the digest 80 (2). The addresses of a subtree root (type 17, level 3) and of a tree root (type 19, level 4) exist in `HashDomain` and no algorithm uses them.

One hash of the seed gives two chain starts: the hash output is 32 bytes, the start of chain `2t` is bytes 0 to 15 and the start of chain `2t + 1` is bytes 16 to 31 (`deriveOutput`, `hashHalf`, `Seeded.otsSecrets`, `Seeded.forestSecrets` in `Scheme.lean`). A one-time key takes 32 derivations for its 64 chains and a forest WOTS key 3 for its 6 chains. The parameter, the surrogates and the randomizer base are one hash each and keep its first 16 bytes; so does every verification hash. `Seeded.otsStart`, `Seeded.forestStart` and `Seeded.chainValue` are the per-chain views (one derivation each), used in statements only: the signer's values are theirs (`Completeness.eval_otsSecrets`, `eval_forestSecrets`).

The signer derives one randomizer base per message, `R0 = Th(P, A(7, 0, 0), S ‖ message)` (one hash query), and attempt `i` uses the randomizer `R0 + i` (addition modulo `2^128`, `Seeded.signDigestLoop`); it keeps the first attempt whose digest index lands in the kept subtree. The randomizer comes last in the digest payload: a grinding attempt changes only the last block of the digest hash. The digest input is 80 bytes: the first block is `P ‖ A ‖ message` and the second the randomizer alone. The root is not hashed (`P` binds the key); `messageDigestPayload` keeps its root argument for its callers and ignores it.

### Digest fields

The digest is the first 234 bits of the hash output (`truncateMessageDigest`), read as a little-endian number; a field is `extractLsb'` at a bit offset (`Scheme.lean`: `wordOffset`, `indexOffset`, `superOffset`, `childOffset`, `digestMarks`, `digestIndex`). With `c < 8` the tree and `j < 2` the subtree:

| field | bits | bit offset |
| --- | ---: | --- |
| codeword-table index of WOTS key `(c, j)` | 8 | `8 (2c + j)`: byte `2c + j` of the digest |
| instance index `idx` | 26 | 128: the low 26 bits of the last 16 bytes |
| leaf of tree `c` | 4 | `154 + 4c` |
| WOTS key of subtree `(c, j)` | 3 | `186 + 3 (2c + j)` |

Bits 234 to 255 are unused. No field lies across two 64-bit words. The proof reads a digest as its index and one 26-bit field per tree (`ForestCoverage.lean`): `coordField` gathers the 26 bits of a tree from the three places that hold them (leaf, then per subtree WOTS key and table index), and `fullDigestView_bijective` states that the index and the 8 fields are a bijection of the 234 bits, so a uniform digest gives a uniform index and 8 independent uniform fields (`evalDist_fullDigestView_uniform`), each a uniform mark (`H0Mark.markEquiv`). The index of a uniform hash output is uniform (`evalDist_blockIndex_uniform`, from `evalDist_hashOutput_extractAt_uniform`: the bits at any offset of a uniform output are uniform).

Separation is unconditional. The scheme seed's input is 43 bytes and every other input at least 48, though the proof does not need it (`BridgeSchemeSeed` charges every call that names `S0`). An input determines its parameter, its address and its payload (`fieldBytes_injective` in `Bytes.lean`, `fieldInput_injective` in `SecurityDomains.lean`), two inputs of different types differ whatever their parameters (`fieldInput_ne_of_tag_ne_across` in `Fresh.lean`, `keygenInput_ne_hashInput`), and an address determines the call: `hashFields_injective` and `Position.input_separated` (`SecurityPosition.lean`) for verification, `deriveFields_injective` and `keygenInput_injective` for the seed derivations, `randomizerHashInput_injective` (`BridgeDet.lean`) for the randomizer base. The address has no layer and no tree field; the scheme has one of each (`Layer` and `TreeIndex` are `Fin 1`).

`Layout.signature_size`: a signature serializes to 4,276 bytes. `Cost.verification_compressions`: an accepted signature costs exactly 307 BLAKE2s compressions (2 for the 80-byte digest input, 189 for the forest, 116 for WOTS+C and the path), and no signature costs more (`verification_compressions_le`). The forest is 23 per tree (`compressions_coordRecover`: in each of the two subtrees 5 chain steps, 2 for the WOTS-key leaf and 2 folds; 2 for the tree leaf; 3 folds), times 8, plus 5 for the key.

Hash calls of the signer (`SecurityPrefixCost.lean`, `SecurityGraphCost.lean`, `SecurityPrefixErasedKeygen.lean`; exact counts on any oracle):

| computation | hash calls |
| --- | ---: |
| one-time key (`hashCalls_oneTimePublicKey`) | `32 + 64 · 3 = 224` |
| tree node at level `l` (`hashCalls_treeNode`) | `226 · 2^l − 1` |
| key generation from the scheme seed (`hashCalls_keygenFromMaster`) | `226 · 2^b + 2 (26 − b)` |
| key generation (`hashCalls_keygenFromSeed`) | `226 · 2^b + 2 (26 − b) + 1` |
| forest WOTS key leaf (`hashCalls_childLeaf`) | `3 + 6 · 4 + 1 = 28` |
| subtree node at level `l ≤ 2` (`hashCalls_subNode`) | `29 · 2^l − 1` |
| tree leaf (`hashCalls_superNode`) | `2 · 2 · 115 + 1 = 461` |
| tree node at level `l ≤ 3` (`hashCalls_topNode`) | `462 · 2^l − 1` |
| forest key of an instance (`hashCalls_forestKey`) | `8 · 2 · 3,695 + 1 = 59,121` |
| opening of one tree (`hashCalls_coordOpen_exact`) | `2 · 222 + 6,926 = 7,370` |
| forest opening (`hashCalls_forsOpen_exact`) | 58,960 |
| WOTS+C values of a signature (`hashCalls_published_values`) | `32 + 120 = 152` |
| signature after the scan (`hashCalls_finishSign_exact`) | `118,082 + counter search + 152 + path` |

The Lean signer recomputes the forest instance for its key and again for the opening, and the tree nodes of the path; these are the counts of that signer, and the budget `q` of the theorem counts them. Only the count of key generation from the scheme seed enters the certificates (`kCreditF`); the call that derives the scheme seed is not credited.

## The proof

The reduction is the one of the FORS variant ([its proof route](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/blob/cc0648feb5b686ba1447678120e401f7b78098f7/formal/lean_sphincs/PROOF.md)), forked module by module with the forest in the hash domains (`Scheme.lean`, `Security*.lean`, `Bridge*.lean`).

**The scheme seed.** `BridgeSchemeSeed.budgetedWin_le_master` replaces `S = H(leanSPHINCS ‖ S0)` by a uniform seed. After internalizing long inputs the game reads an eager uniform table; swapping the table's answer at `leanSPHINCS ‖ S0` with an independent uniform value (`evalDist_table_point`) makes `S` uniform and independent of the table, and the swapped table differs from the table only at that input. A run of the game from `S` does not depend on `S0`, so it names that input with chance at most `2^-256` per hash call (`probEvent_update_seed_le`), whoever makes the call, and the budgeted win is the budgeted win of the game from a uniform scheme seed (`experimentMasterDet`) at the same budget, plus `q / 2^256`. The rest of the proof is about that game: the key generation it charges is that from the scheme seed, so the one call that derives `S` is left in the adversary's budget, and the guesses cost `3 q / 2^256` in all (`Det.forgeAdvantageDet_le_seedFree`), which the slack of every route absorbs.

**Two secrets per derivation.** The scheme seed is removed as before: the answers of all derivations are sampled before the seed and programmed at the seed's inputs, and the adversary sees them only by querying an input that contains the seed (`SecuritySeedGuess`, a `2^-256` guess per query). The prepared material is unchanged: one independent uniform 256-bit value per secret (`SeedModel.Material`), the secret being its first 16 bytes. What is programmed at the input of a derivation is `SeedModel.derivedOutput`: the two secrets of its pair of chains side by side, or the value of a surrogate. Distinct derivations have distinct inputs (`derivationInput_injective`, from `keygenInput_injective`) and read distinct secrets, and every secret is the half of its derivation that the signer takes (`secretHalf_derivedOutput`, `secret_prepared`). A table of answers comes from the same number of materials whatever the table (`card_fiber_derivedOutput`: one free second half per chain start), so uniform material programs independent uniform answers (`SeedCoupling.evalDist_derivedOutput_uniform`), which is the law of the random oracle on these inputs (`evalDist_prepareTable`, `evalDist_prepared_continuation`). Every module above the seed model sees `truncateHash (material.2 position)` as before, and its statements are unchanged. The only numbers that change are the hash-call counts of the signer above; the key-generation credit of the certificates is `kCreditF b = 226 · 2^b + 2 (26 − b)` (`BridgeDetW.lean`, `keygenCost`).

After the deterministic signer is replaced by a seed-free one (`BridgeDet*`), a forgery is a first-order hit, a WOTS second-order event, or one of the forest events of the refined classification (`BridgeImplicationA`): a contact without guess record, two contacts at different chains of one index, a recorded contact at a chain opened at or below its step, a near cover with a recorded contact, or a cover. Budgets are split at `qh ≈ 2^(128 + lx)`.

**No root hashes.** The graph of hashed values (`SecurityPosition.lean`) keeps its positions; only the children of two kinds of position change: a tree leaf (`superChild`) reads the four level-2 nodes of its two subtrees and the key (`roots`) the sixteen level-3 nodes of the trees. The root of a subtree and the root of a tree remain positions that nothing reads: the position set already over-approximates what is hashed, every position is prepared, and an address still determines one position, so a query has one target as before. The values a signature reveals are unchanged (`GraphView.publicData`: the subtree path at levels 0 to 2 and the tree path at levels 0 to 3, the last of each being the other top node, which was already a path element). In the forest witness (`SecurityForestWitness.lean`) an opening gives two top nodes per tree, the one its fold reaches and its last path element (`opSubTops`, `opTops`). If the sixteen level-3 nodes differ from the honest ones and the key is reached, the key hash has a second preimage (`RootsMatch`, a first-order event as for the 8 roots before). Otherwise each tree has the honest last path element and its fold of 3 levels reaches an honest node (`Completeness.orderTops_eq_iff`), which is classified as a fold to the root was (`top_fold_classification`: honest tree leaf and path, or a node match at levels 1 to 3); likewise for the four level-2 nodes of a tree leaf (`SuperMatch`, `sub_fold_classification`, node matches at levels 1 and 2). The statements above the witness (`Forest.Opening`, `recovered_classification`, the classification of a win) are unchanged.

### The scan signer `R = R0 + i`

After the seed is eliminated the start `R0` of a message is uniform and hidden, and the signature of a message uses the first landing randomizer at or after it. For one unsigned message a randomizer is fresh, cached and rejected, or cached and landing; the law of the signed pair is the walk value of `LoopWalk.lean` over these statuses (`BridgeScan.scan_boundW`). A cached landed pair is selected with a probability that depends on the cache (the run of rejected values before it), not `1/(n + R)`, and one digest query raises the selection mass of the adversary's pairs by at most `(2 − p)/2^128` (`LoopWalk.creation_le`, `p = 2^-(26−b)`; attained by scanning forward from random starts), against `1/2^128` for independent attempts. The potentials therefore keep the cached pairs of each unsigned message as one exclusive group (`GroupFuture.grp`, `BridgeGroups.grpAll`) applied to the one-coin future of the pairs still to come:

- a new pair is paid by one future coin (`GroupFuture.probe_step`, `termO_newPair`) as long as the group of its message keeps mass `1 − τ` on the identity; the witness is only monotone, so the coin is `(2 − p)/(2^128 p (1 − τ))` (`H0Fair.wbarOf`, `FairS`), with `τ` from the numbers of cached digests and of cached landed pairs (`LoopWalk.mass_le`);
- the number of cached landed pairs of unsigned messages is capped by an exact martingale (`lam` in `BridgeForsPotentialOnce`): above the cap the bound is trivial, and the cap term is at most `(64/65)^(2^15)` at the start (`H0Fair.lam_start`);
- a signing call is paid by one fresh slot and the group of its message (`sign_term`): no coupling and no fair share;
- for the largest budgets one message can hold almost all the mass (its signature is then a known pair with certainty). A message with more than half of the budget is *heavy* (`BridgeHeavy`): it acts by the law of its signed view (`GroupHeavy.sgn`, exact under its own digest queries) and uses one spare fresh slot; the other messages have at most half of the budget (`BridgeHeavyW`, `BridgeHeavyRoutes.det_largeH`, certificates with `N + 1` signatures in `BridgeHeavyCert`).

### Small budgets (`q - keygenCost ≤ qh`)

- **Linear potential** (`BridgePotentialA`..`A8`, `BridgeFleafA3`). A forest step whose written coordinate is still unexposed is *latent*: it becomes a contact with chance `2^-128` when that coordinate is exposed. Contacts carry the weight `cw` (one if decided, `2^-128` while latent); exposures keep every multilinear expression of the weights in the mean (`mean_cw`, `mean_cw2`) and the final payoff is bounded through pinned completions (`completion_pin`, `prob_fct`). The potential pays guesses, first-order hits, WOTS second-order events, unrecorded forest contacts and pairs of contacts, and leaves `(ρ - 1 - x) 2^-128` per forest step query unused (`smallRoute_potentialF`).
- **One-coin cover potential** at baseline `ρ / 2^128` with the exact cover indicator as witness (`BridgeForsPotentialOnce`, `BridgeForsGameOnce`), and its H-term certificate (`H0*`: Poissonization, splitting into independent indices, first and second moments of the per-tree cover fraction from the distribution of the componentwise maximum of codewords, `H0ForestOpt`).
- **Contact bound A4** (`BridgeA4F`, `BridgeA4Sign`, `BridgeA4Final` on the game framework `BridgeGameF`). A recorded contact is *settled* once a reveal opens its chain at or below its step; settled contacts pay one, unsettled ones pay the reveal rate of the remaining signatures, the coin part and the capped near potential: `Ψ = Σ_recorded cw · (settled ? 1 : sig + coin + min(1, potN(y))) + y 2^-128 coin + κ 2^-128 Σ_{j<y} potN(j)`. The weighted sums keep their mean through ordinary queries (`BridgeWsum.wsum_ordinary`). Through a signing call (`sign_contact`): the signer asks no forest step input, so it records no forest step, keeps every step answer and exposes a written coordinate only by revealing its chain (`BridgeRunFacts`); a completed call reveals upward-closed chains (`closedRuns_loop`); a call opens a given chain at or below `min(t + 1, 3)` with chance at most `123 · 2^-b · 2^-15` plus `wbar` per cached pair of the message, over every run (`reveal_le_all`, `BridgeRevealAll`, `BridgeRevealRate`: at most 123 of the 256 table entries have a given digit at least one; with the scan signer the second part is `hitMass`, the probability that the signature uses a cached landed pair, and the coin part of the potential is `ν (budget · offSum + C(budget, 2) · rateS)` with `rateS = (2 − p)/2^128`: a unit of budget is a contact attempt or a digest query, not both); a latent contact exposed by the call is decided with chance `2^-128` whatever the call does (`BridgeExposeMean.interp_value_le`). The near potential uses the subtree-free near witness (`BridgeForestNear`, certificate `H0NearOpt`). A forest step query costs `2^-128 (N rate + 1 - κ)`, paid by the slack of the linear potential once `κ ≥ 2 - ρ + x + N rate` (`arm_paysF`).
- Assembly: `sample_boundF` (`BridgeSampleBoundF`), `det_smallF` and the closed form `small_closeFF` with the rational check `checkSmallF` (`BridgeDetCloseF`).

### Large budgets

The one-coin bound at the survival-weighted baseline (`BridgeSatW*`, `det_largeW`) with forest covers (`BridgeDetW.checkCoverW`, `H0ForestOpt`).

### Both routes

`BridgeHeavyCert.det_bitsFH`: 127 bits from the small-route table (rate at `qh`), the small-route option, the near certificate, `checkSmallF` at `qh` (coin summand `(2 − p) qh / 2^129`), and a chain of covers of `[qh + 1, 2^127)`, each with its own Poisson table: light covers (`checkCoverW`, coin `wbarOf`) up to about `0.249 · 2^128`, then one heavy cover (`checkCoverH`, `N + 1` signatures, coin `wbarH`). For `b = 26` there is no grinding and one light cover reaches `2^127`. The splits are `lx` = −10.41 / −9.25 / −8.17 / −8.02 / −7.88 / −7.61 / −7.39 (`b = 26 … 8`, `PARAMS` in the script), the best of a grid of step 1/8 refined to 1/64 around its optimum; the limits are the largest `N` both routes certify there, rounded down to four digits. For `b = 26` the large route alone limits `N`; below, both routes are tight.
