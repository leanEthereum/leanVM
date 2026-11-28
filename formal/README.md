# formal

Lean 4 proofs, all in the random-permutation model, that a node statement's digest binds it, that the batching run outside the circuit is sound, that leanXMSS and leanSPHINCS are strongly unforgeable, and that LeanDA's commitments are position binding and its membership test is sound, a committed matrix that passes it being a matrix of codewords (over the model's permutation, not the guest's in-circuit DA check). Stated, and open while the proofs are ported to Hotwire (the link in place of the bus): leanVM's knowledge soundness and completeness, and its aggregation program's soundness and completeness as one aggregation step, for one node, its executable prover, run from a node's statement and witness, making a proof the verifier accepts; their proofs for the protocol before Hotwire are archived at tag `formal-bus-archive`. What is proved, and what is not, is [statement.tex](./statement.tex).

Key file: [Theorems.lean](./Statement/Theorems.lean)

```sh
cd formal
./check-all.sh lean      # build and kernel-check every Lean project: no sorry, axioms Lean's three (needs cargo: it first writes the files derived from the guest, which are not committed)
./check-all.sh vectors   # compare with this repository's Rust: verifier and prover (needs cargo)
```
