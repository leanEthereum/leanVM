# Statistical ZK research

The entry point is [main.tex](main.tex). It builds one document containing the target definition, remaining proof plan, current results and all supporting notes. The target is honest-verifier statistical ZK with total distance at most `2^-128`; full ZK is not yet proved.

```bash
cd doc/research
latexmk -pdf main.tex
python3 check.py
```

The PDF is `.build/main.pdf`. Read `body/01-target.tex`, `body/02-proof-plan.tex` and `body/03-status.tex` first. Supporting proofs are grouped under `body/`; the appendices separate count-tree history and the optional public-preprocessing branch. `body/c-source-map.tex` maps the former standalone filenames to internal sections. All note references are internal PDF links, and references are collected in `references.tex`.

The earlier joint theorem in [body/flock/zk-flock-sixteen.tex](body/flock/zk-flock-sixteen.tex) covers any twelve lane-59 values in one specified sixteen-point encoder coset, all twelve final GKR children and the established terminal/Flock interface, below `2^-155`, or `2^-151` including memory and the shared root. It assumes a common valid completion and does not cover multiple cosets or the full transcript. Its source is specified in [body/flock/zk-flock-children.tex](body/flock/zk-flock-children.tex). Run `python3 doc/research/audits/zk_flock_multicoset_audit.py` for the exact dual identity, binary-source geometry and error bounds, and `python3 doc/research/audits/zk_flock_children_audit.py --full --wide` for complete source validity, joint ranks and exhaustive native query maps.

The subsequent [balanced long-chain repair](body/flock/zk-flock-lowbank.tex) uses 3840 cycles and jointly hides one sixteen-point low coset and one thirty-two-point high coset with the established VM/memory/root interface, below `2^-132`. Independent count columns separate the two regions without further rows or error terms; the high coset alone remains below `2^-151`. The actual 48-query/terminal/GKR audit attains binary rank `9024/9024` and verifies the three source groups separately. Run `python3 doc/research/audits/zk_flock_lowbank_audit.py --full` for valid read chains, exhaustive native query maps and exact error ledgers. The theorem assumes a common valid completion and does not cover arbitrary query families or the full opening.

Without this extra bank, [body/flock/zk-flock-query-fiber.tex](body/flock/zk-flock-query-fiber.tex) gives a six-query obstruction excluding 128-bit privacy at all four rates. The default multicoset audit preserves that negative regression. Use `--query-map --joint-boundary --lowbank` to diagnose the enlarged source with all initial lane-59 queries and terminal/GKR fields; `--include-low` retains public-prefix observations. The successful sampled ranks are not a uniform statistical bound.

The original long-chain matching admitted a concentrated twenty-eight-query distinguisher and a structural thirty-two-point rank deficit. The balanced matching removes those specific deficits without further rows. The historical concentration event is below `2^-399`, which does not bound all possible leaks of either source. The query-family note gives a precise next target: count the minimal query supports of functionals that annihilate the padding but detect an allowed private shift. Its required support counts remain unproved.

`preamble/` centralizes document setup and loads the VM's shared notation from `../leanvm/preamble/macros.tex`. There is one build directory and one document root. Do not restore independent document wrappers around body files.

Python audits live together in `audits/`, preserving their local imports. Run a named audit from that directory, for example:

```bash
cd audits
python3 zk_four_round_tail_audit.py
```

Alternatively, from the repository root use `python3 doc/research/audits/zk_four_round_tail_audit.py`. Unqualified audit commands in the detailed notes assume the `audits/` working directory. The audit helper loads the actual `python-verifier/verifier.py` from the repository. Full-support count-head modes are expensive and are not part of the quick structural check. Exact rank certificates and successful verifier replays are evidence for their stated lemmas, not an end-to-end privacy proof.

The small-frame memory branch is [body/foundations/zk-memory-frames.tex](body/foundations/zk-memory-frames.tex); [body/bus/zk-memory-root.tex](body/bus/zk-memory-root.tex) composes its opening envelope with the shared bus root and proves that the root kernel survives the actual mixed algebraic PCS. This does not simulate the rest of the VM view. Run `python3 doc/research/audits/zk_memory_frames_audit.py` for their algebraic certificates and exact error ledger. The separate native obstruction example runs with `cargo run --release -p lean_vm --example zk_memory_prefix_audit`: it verifies two full VM proofs and separately checks the exceptional authenticated PCS leaves. The complete proofs use ordinary Fiat-Shamir queries, not forced exceptional queries.

[body/10-wire-ledger.tex](body/10-wire-ledger.tex) inventories the current wire and exact committed-size budget. [body/flock/zk-flock-coset.tex](body/flock/zk-flock-coset.tex) rules out two Flock row orders using initial-query distinguishers and diagnoses a binary-rank shortfall in a third. A richer valid-padding source preserves the endpoint theorem, but its middle rounds and full opening still need proof. Run `python3 doc/research/audits/zk_flock_coset_audit.py` for the exact privacy floors, add `--native` for native witness/NTT/authentication checks, or `--mixed-rank` for the fixed-query diagnostic. A common valid padding sampler, full joint GKR/Flock simulation and authentication remain unproved.

[body/flock/zk-flock-interface.tex](body/flock/zk-flock-interface.tex) proves that pinned-IV padding also leaks through directly disclosed table columns, even with row shuffling. A new three-point source and general compression inputs jointly hide all eighteen BLAKE2s value claims with the established endpoints. Run `python3 doc/research/audits/zk_three_point_audit.py` and `python3 doc/research/audits/zk_flock_interface_audit.py` for the certificates, or `cargo run --release -p lean_vm --example zk_flock_interface_audit` for two complete small-frame VM proofs whose scalar streams exhibit the invariant. The candidate varies message, chaining value and metadata, not merely the message profile. Middle rounds and full opening remain unproved.

[body/flock/zk-flock-columns.tex](body/flock/zk-flock-columns.tex) extends that joint theorem to all thirty-seven BLAKE2s terminal columns, below `2^-156`. A disjoint library of equal-compression pairs supplies metadata randomness while preserving the packed witness pointwise. It fits the same height and memory reservation. A further conditional composition joins this view to the shared bus root and memory envelope below `2^-151`, assuming a valid common completion. Run `python3 doc/research/audits/zk_flock_columns_audit.py` for full-library bus checks, native ranks and the exact ledger. The paired source, not the former independent-per-position source, must be used in subsequent PCS analysis.

[body/flock/zk-flock-pair-opening.tex](body/flock/zk-flock-pair-opening.tex) rules out that block-local metadata source for full ZK: two PCS queries cancel its masks, with simulator-error floors above `2^-10` through `2^-17` across the supported rates. A second, globally permuted library preserves the partial theorem and breaks this cancellation, but full PCS privacy remains unproved. Run `python3 doc/research/audits/zk_flock_pair_opening_audit.py`, optionally with `--native`, for the exact obstruction, disjoint extension, native witness pair and authenticated encoder checks.

`check.py` checks the document input graph, note and citation references, audit links and the local audit import closure. It does not verify the mathematical claims. No Rust, Python or recursive production-verifier behaviour is changed by this project.
