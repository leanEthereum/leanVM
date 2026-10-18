# Triage of the aggregation guest

`crates/rec_aggregation/guests/lean_ethereum.py` (G below) against the specification, function by function: **S** computes what a Spec definition already defines (up to representation), **GS** is guest-specific and needs its own mirror and a refinement lemma. It decides the shape of the guest mirror (`LeanVM/Guest/`). V is `Spec/Verifier.lean`, N `Spec/Node.lean`, LX `formal/lean_xmss/LeanXmss/Scheme.lean`, SP `formal/lean_sphincs/Sphincs/Scheme.lean`, LD `formal/lean_da/LeanDa/Scheme.lean`.

Representation conventions: a canonical cell `c0 + y·c1` is the 16 bytes `kBytes c0 ++ kBytes c1`, a digest its two cells (`digestScalars`); a count `n` is `gpow n`; an integer word is its bit pattern (`eOfNat`); an `E` cell in a transcript is its three limbs, 24 bytes (`blockOf`).

The compiled guest (`BYTECODE_LOG = 18`): 262144 instructions, 1044 functions (488 `__loop` helpers, specializations `f__L…`); the largest are `open_stacked` (28 specializations), `verify_sig_lean_sphincs` and `verify_lean_xmss`.

## Functions

### Fiat-Shamir, bits, exponent gadgets, sumcheck, Merkle, WHIR (G:446-1317)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 1 | pack64x2 | S: `E.ofLimbs a b 0` | `assert_in_k` |
| 2 | assert_canonical | S: `IsCanonical128` | `hint_f192_limbs`: unique tower representation |
| 3 | canonical_limbs | S: limbs 0, 1 | as #2 |
| 4 | challenge_from_state | S: `challengeOf` (V:477) | `hint_f192_limbs`: `assert_in_k` |
| 5 | fs_compress | S: `absorbBlock cv (blockOf x tag)` (V:522) | `hint_f192_limbs`: `assert_in_k`, canonical operand |
| 6 | obs | S: `.read` absorb, `Node.observe` | |
| 7 | fs_next | S: `run .read` (V:557) | stream word, bound by the absorb |
| 8 | squeeze_state | S: `absorbBlock cv (blockOf 0 2)` | |
| 9 | squeeze | S: `.sample`, `Node.squeeze` | via #4 |
| 10 | absorb_nonce | S: `.grind`'s new chaining value | |
| 11 | squeeze_step | S: `.sample`, both words exposed | via #4 |
| 12 | bind_bits | dead code, never called | |
| 13 | exponent_tables | GS: constant tables `g^j ↦ eOfNat (2^j)`, `g^j ↦ g^(2^j)` | |
| 14 | g_power_of_word | GS: `gpow (kToNat v.limb0)`, upper limbs zero | `hint_decompose_bits`: booleanity, reconstruction |
| 15 | verify_log2_ceil | GS: `log2Ceil` (V:695), floored | `hint_log2_ceil`: pinned by the two bounds |
| 16 | log2_ceil_in_the_exponent | GS: as #15 on `g^N` (completes for `N ≤ 2^33`: the log is range-checked below `SIZE_BITS = 34`, G:627) | `hint_decompose_bits_exponent` |
| 17 | decode_query_bits | S: one step of `sampleQueriesAux` (V:1598) | `hint_decompose_bits(192)`: booleanity, reconstruction |
| 18 | grind_check | S: `.grind`, `powOk` (V:482) | `hint_f192_limbs`, `hint_decompose_bits(64)` |
| 19-24 | eq_weight, eqtree, lag64, eq_prefix_chain, rs_eq_run, fold_final_msg | S: `eqKernel`, `lagrangeWeights 64` over `windowDenominator`, `eqEval`, `ringWeight`'s products, `multilinearEval` | |
| 25, 26 | sumcheck_round4, sumcheck_round5 | S: `sumcheckRoundPoly` (V:1313), plain and eq mode | stream |
| 27 | batch_sumcheck | S: `Node.batchRounds` (N:215) | bound by the absorbs |
| 28 | verify_merkle_path | GS: `climb` (V:526) below the cap | `merkle_children`: selected child pinned by write-once, parent hashed, direction bits from #17 |
| 29, 30 | hash_cap_node, verify_merkle_cap | GS: the cap's root on every queried path | `merkle_caps`, `merkle_cap_active`: a zero on a path refuted by `flags[parent] = 1` |
| 31-34 | opening_fold, opening_ood_point, opening_final_message, opening_row_weights | S: `foldRounds`/`tailRounds`, `sampleN`, `readN`, `eqKernel` (reversed at level 0) | stream |
| 35 | opening_queries | GS: `openAll` (V:543) and `enforcedSum` (V:1622) | `merkle_leaf_rows`: limbs in `K`, bound by the root |
| 36 | open_stacked | GS: `verifyWhir`/`whirLevels` (V:1718) per candidate (stack log 22..28, rate 1..4), same reads, samples and grinds in Spec order; the terminal moves to #43 | via #30, #18 |

### Bus, tables, Flock, the child verifier (G:1320-2281)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 37 | verify_bus_gkr | GS: `verifyGkrGrandProducts`/`gkrLayers` (V:1392), same reads, samples, values; an odd depth runs a binary root layer first | |
| 38 | padding_weight (29 arms) | S value: `paddingWeight` (V:713), and `τ = log2Ceil n` | `hint_decompose_bits(τ+1)` |
| 39 | verify_tables | GS: `verifyBusBalance` after GKR, `tablePhase`, `publicInputPhase`; 112 claims in Spec order | `sort_order`: range check, order, write-once and pigeonhole give a bijection; `bytecode_val` is `FixedClaims.bytecodeValue` (deferred) |
| 40 | verify_flock | S: `verifyFlock (.claimed c)` (V:1997), in Spec order | `matpart` is `FixedClaims.matrixValue`, pinned by the terminal |
| 41 | certify_placement | GS: `placementsOf`/`stackOffsets`/`columnKappas` | `col_sort_order`: as `sort_order` |
| 42 | column_selector (29 arms) | S: `Placement.eqAbove` (V:870), padded to 28 coordinates | `hint_decompose_bits_exponent(28)` |
| 43 | check_opening_terminal | S: `verifyStackedOpening`'s weight and terminal (V:1781) | |
| 44 | verify_sub | GS: `verifyDeferredWith` (V:2235): seed, `readSizes`, `commitStack`, bus, tables, Flock, ring switch, stacked opening, then `defer_out = Node.fixedCells` | `stream`, `table_logs` |

### Signature verifiers (G:2285-2658)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 45, 46 | shifts, is_child | GS gadgets: `keyAt`/node index, `nodePayload` order | caller pins bits; `siblings` |
| 47, 48 | chain_step, walk | S: a step of `chainWalk`, `recoverChain` (LX:276, SP:466) | `chain_starts`: canonical |
| 49 | walk_group | GS: dispatch over three base-4 digits; product `g^Σd`, encoded `Σ d·4^i` | `digits` |
| 50 | hash_values | S: `leafHash` (LX:285, SP:476); needs `n mod 4 ∈ {0, 2}` | |
| 51 | merkle_path | GS: `treeFold` (LX:312, SP:497) with hinted ordered children | `siblings` |
| 52 | verify_lean_xmss | GS: must be `xmssVerify` (N:64, LX:335) | `leaf_index_bits`, `randomizer`, `digits`, `chain_starts`, `siblings` |
| 53 | sp_forest_key (256 specializations) | S: `childRecover … (lut t)` (SP:563) | `sp_forest_values` |
| 54-56 | sp_fold, sp_subtree_arm, sp_tree_arm | S/GS: `subFold`/`topFold`/`orderTops`; dispatch arms | `sp_forest_nodes`, `sp_keys`, `sp_leaves` |
| 57 | verify_sig_lean_sphincs | GS: must be `sphincsVerify` (N:70, SP:739) | `sp_*`, `digits`, `chain_starts`, `siblings` |

### Digests, claim lists, LeanDA (G:2661-3116)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 58 | statement_digest | S: `statementDigest` (N:191), byte for byte | `hint_f192_limbs` |
| 59 | scaled_log | GS gadget: `2^shift · log x` as a bit pattern | `hint_decompose_bits_exponent(16)` |
| 60, 61 | claims_window, claims_tail | GS: chunks of `blake2sBytes`, counters by disjoint bits | `claims` |
| 62 | claim_list_digest | S: `xmssListDigest`/`sphincsListDigest` (N:167) | `signers_split`, `claims` |
| 63-65 | child_claims_window, child_claims_tail, child_claim_list_digest | GS: a child's list digest rebuilt from this node's table, each claim marking its slot | `child_claim_index`: range check, write-once |
| 66 | da_verify | S: `Da.Witness.Opens` (`commitCodewords`, `vectorDigest`, row orthogonality) | via #67 |
| 67 | da_row_shape | GS: `r ∈ [1, 1024]`, `lp = clog r` | `da_shape` |
| 68-72 | da_verify_column, da_verify_cell, da_levels, da_vector_dispatch, da_vector_cell | S/GS: `treeRoot` over the column-major list, `listCellDigest`, `vectorDigest` segments | `da_symbols`, `da_weights` |
| 73, 74 | da_list_digest, da_hash_roots | S: `daListDigest` (N:181) | |
| 75 | cover_da_root | GS: coverage of a DA slot | `da_index` |

### Top level (G:3119-3486)

| # | function | label and correspondence |
|---|---|---|
| 76 | main | GS: one node; must give `∃ seed s w`, public input `statementDigest seed s`, `NodeRel`. Counts, `fs_seed` (pinned by the public input), DA roots and list digests, signers digest, raw signatures (`.direct` holders), at most one direct DA, per child its lists rebuilt from this node's table, its `statementDigest`, `verify_sub`; coverage `written = n_total`; `AtZero` or `aggregate_claims`; own digest against `m[0]`, `m[1]` |
| 77 | aggregate_claims | S: `Node.batch` (N:261), same values in the same order |

Effort: 37 functions need only a representation lemma, 39 a guest-specific mirror and a refinement lemma, 1 is dead. Shared infrastructure: chained BLAKE2s over cells equals `blake2sBytes`; address cells equal `tweakFields` bytes; write-once and pigeonhole bijections; the baked placeholder tables checked against their Spec definitions by kernel decision.

## The hint interface

Each stream is a FIFO of entries popped by `hint_witness`; computed hints (`hint_decompose_bits`, `_exponent`, `hint_log2_ceil`, `hint_f192_limbs`) and the VM's own advice (inverses for `!=`, back-solved products) need no stream. All producers are in `crates/rec_aggregation/src/aggregation.rs`, and every stream is pushed in the order the guest pops it.

| level | streams |
|---|---|
| node (`aggregate_with_stats`) | `meta`, `da_meta`, `fs_seed`, `da_roots`, `claims`, `dup_claims`, `signers_split`, `raw_index`, `sp_raw_index`, `child_meta`, `child_claim_index`, `child_defer`, `child_da_count`, `da_index`, `leaf_defer` |
| batching (`aggregate_deferred_claims`) | `bc_sumcheck_msgs`, `mat_sumcheck_msgs`, `bc_star_hint`, `mat_stars_hint` |
| per child (`gen_verify`) | `stream` (zero-padded to 8192), `table_logs`, `sort_order`, `bytecode_val`, `zc_tau_max`, `matpart`, `col_sort_order`, `merkle_caps`, `merkle_cap_active`, `merkle_leaf_rows`, `merkle_children` |
| signatures | `leaf_index_bits`, `randomizer`, `digits`, `chain_starts`, `siblings`, `sp_*` (raw leanXMSS first, then leanSPHINCS) |
| DA | `da_weights`, `da_shape`, `da_symbols` |

## Findings

No soundness bug and no unpinned hint: every hint is pinned, or is existential content of the statement, the witness or a proof.

`NodeRel` admits witnesses the guest cannot run, so completeness assumes the deployed limits (`NodeRel` stays as it is unless one of them is a real mismatch):

1. a child's stack log is in `[22, 28]` (G:2246; the Spec admits 15);
2. a child's proof stream is at most 8192 scalars (G:2095);
3. at most one direct DA holder (G:3154);
4. repeated declared claims held through a child need distinct child entries (G:2815, 2835, 2876, 3291), where N:363 lets two equal claims share one holder;
5. at most 16 children, at most 16 DA roots per statement and per child, every list and the coverage below `2^16` (G:3145-3169, 3275);
6. at least one declared claim (G:3207).

Minor: `bind_bits` is dead; `hash_values` needs `n mod 4 ∈ {0, 2}`; `Spec/Da.lean` cites a stale guest range, and `Spec/Node.lean` an older leanVM commit.
