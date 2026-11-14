# formal

Lean 4 proofs, all in the random-permutation model, that leanVM is knowledge sound and complete; that its aggregation program is sound and complete as one aggregation step, for one node (soundness across recursion levels is not proved); that leanXMSS and leanSPHINCS are strongly unforgeable; and that LeanDA's commitments are position binding, and code binding for an argument assumed knowledge sound whose relation is evaluated over the model's permutation (not the guest's in-circuit DA check). What is proved, and what is not, is [statement.tex](./statement.tex).

Key file: [Theorems.lean](./Statement/Theorems.lean)

```sh
cd formal
./check-all.sh lean      # build and kernel-check every Lean project: no sorry, axioms Lean's three
./check-all.sh vectors   # compare with this repository's Rust: guest data, verifier and prover (needs cargo)
```
