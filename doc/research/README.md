# Statistical ZK research

The entry point is [main.tex](main.tex). It builds one document containing the target definition, remaining proof plan, current results and all supporting notes. The target is honest-verifier statistical ZK with total distance at most `2^-128`; full ZK is not yet proved.

```bash
cd doc/research
latexmk -pdf main.tex
python3 check.py
```

The PDF is `.build/main.pdf`. Read `body/01-target.tex`, `body/02-proof-plan.tex` and `body/03-status.tex` first. Supporting proofs are grouped under `body/`; the appendices separate count-tree history and the optional public-preprocessing branch. `body/c-source-map.tex` maps the former standalone filenames to internal sections. All note references are internal PDF links, and references are collected in `references.tex`.

`preamble/` centralizes document setup and loads the VM's shared notation from `../leanvm/preamble/macros.tex`. There is one build directory and one document root. Do not restore independent document wrappers around body files.

Python audits live together in `audits/`, preserving their local imports. Run a named audit from that directory, for example:

```bash
cd audits
python3 zk_four_round_tail_audit.py
```

Alternatively, from the repository root use `python3 doc/research/audits/zk_four_round_tail_audit.py`. Unqualified audit commands in the detailed notes assume the `audits/` working directory. The audit helper loads the actual `python-verifier/verifier.py` from the repository. Full-support count-head modes are expensive and are not part of the quick structural check. Exact rank certificates and successful verifier replays are evidence for their stated lemmas, not an end-to-end privacy proof.

The small-frame memory branch is [body/foundations/zk-memory-frames.tex](body/foundations/zk-memory-frames.tex); [body/bus/zk-memory-root.tex](body/bus/zk-memory-root.tex) composes its restricted opening envelope with the shared bus root. Run `python3 doc/research/audits/zk_memory_frames_audit.py` for their algebraic certificates and exact error ledger. The separate native obstruction example runs with `cargo run --release -p lean_vm --example zk_memory_prefix_audit`: it verifies two full VM proofs and separately checks the exceptional authenticated PCS leaves. The complete proofs use ordinary Fiat-Shamir queries, not forced exceptional queries. The restricted frame construction preserves the two public-input cells but still needs joint simulation with intermediate GKR messages, counts and the actual full stacked opening.

`check.py` checks the document input graph, note and citation references, audit links and the local audit import closure. It does not verify the mathematical claims. No Rust, Python or recursive production-verifier behaviour is changed by this project.
