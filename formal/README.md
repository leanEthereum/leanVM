# formal

Lean 4 proofs that leanVM is knowledge sound and complete, that its aggregation program is sound and complete, that leanXMSS and leanSPHINCS are strongly unforgeable and that LeanDA is binding, all in the random-permutation model. What is proved, and what is not, is [statement.tex](./statement.tex).

Key file: [Theorems.lean](./Statement/Theorems.lean)

```sh
cd formal
./check-all.sh lean      # build and kernel-check every Lean project: no sorry, axioms Lean's three
./check-all.sh vectors   # compare with this repository's Rust: guest data, verifier and prover (needs cargo)
```
