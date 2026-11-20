# How to prove a function

The worked examples are `E::mul` (no loop), `clmul_low` (a constant table), `clmul` and `eq_eval` (a loop, a heap slice, a panic): copy their files.

## Files

- `Rv64mc/Spec/<Area>/<Fn>.lean`: `Pre`, `Post` in terms of the Model's mirror (`Model.eMul`, `Model.eqEvalRust`) and `Core/Repr.lean`'s predicates (`EListAt`, `SliceArgs`, `Env.Live`), and `def spec env p i need := Holds env p i need Pre Post`, the stack `need` a parameter (ghost values, such as a slice's elements, quantified outside: `∀ xs ys, Holds …`). Arguments in registers as the RISC-V ABI passes them: an `E` by value is two registers (`c0`, `c1`), a `u128` is low then high (`Spec.Field.lo128`, `hi128`), a slice is a pointer and a length. No proof here.
- `Rv64mc/Proof/<Area>/<Fn>.lean`: `theorem ok (env) (p) (i) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needC …} (hnC : frame + needC ≤ need) … (<per callee: Callee.spec env p L.<callee>.idx needC>) (<per table: DataRef.Words env L.d_<key> d_<key>_words>) : <Fn>.spec env p i need`, over the generated template (`Gen.Tmpl.<Module>`), never an address, an index or a stack size: `frame` is the template's `addi sp, sp, -frame` (a leaf with a frame takes `(hn : frame ≤ need)`, one without takes nothing). A Proof never imports `Gen/Needs`, so a callee whose frame changes re-proves no caller.
- `Rv64mc/Table/<Area>.lean`: each `ok` at `liftProg Gen.fns` and its index (`Rv64mc/Gen/index.tsv`), at `need := Gen.Needs.<Module>` (the generator's frame plus deepest callee, `Rv64mc/Gen/Needs.lean`), with `Gen.<Module>.tmpl_eq` and `wf`, each `frame + needC ≤ need` by `decide`, a callee's `Table` theorem as its hypothesis (or a hypothesis of the table theorem while that callee is unproved), and a table's `DataRef.Words` as a hypothesis, which `DataRef.Words.of_data` proves from the image's `env.data`.
- A callee not proved yet: write its `Spec` file anyway and take `Callee.spec env p L.callee.idx needC` as a hypothesis. A callee that never returns is `Spec.Runtime.NoReturn env p idx needF`.
- A constant table (a template field `d_<key> : DataRef`, whose content the generator writes as `d_<key>_words`): take `DataRef.Words env L.d_<key> d_<key>_words` as a hypothesis; `rv_auto` reads `d.hi + d.lo + 8 k` as word `k` of it (`Core/ReprLemmas.lean`).

## The proof

```lean
theorem ok … : EMul.spec env p i need := by
  rv_auto hp with [hL] using [hcl, hrd]
  all_goals simp only [Model.eMul, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1]
  all_goals simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, append_hi_lo]
```

- `rv_auto hp with [hL] using [callee specs]` steps every path and closes the calling convention, every callee's precondition (its stack room, `env.Static`, `NEXT`), the memory frame (`Env.Frame`, own stack stores and callees' frames), `env.Static` and the saved registers. What it leaves: the functional part of `Post` (and of a callee's `Pre`), and a goal at every loop head (the target of a backward jump). `with` takes the link's facts (`hL` whole); `using` takes contracts (`Holds`, `NoReturn`, or `∀ f, …`). `stop [pc]` adds a stop (`pc` is the index in the body: label `k` is at `2k`).
- Functional goals: unfold the Model (`simp only [Model.f]`), put XORs in one order (`BitVec.xor_assoc`, `BitVec.xor_comm`, `xor_left_comm`), `ac_rfl` at one level. Values loaded from a heap object read `M.getMem (p + BitVec.ofNat 64 (16 * j))`: rewrite with a `load` lemma through the frame (`EListAt.load`, `Core/ReprLemmas.lean`, where such lemmas go). A bit reversal the compiler lowers to shifts and masks is `reverse_net` (`Proof/Field/Reverse.lean`): `rw [← reverse_net]; simp only [swapBits, bswap]` (and `ac_rfl` if the `|||`s are grouped differently).
- A loop: `theorem loop … : ∀ k j R M, j + k + 1 = len → Inv … j R M → SafeN … ⟨⟨i, head, ret, top⟩ :: rest, R, M⟩` (head from the goal `rv_auto` leaves), the hypotheses of `ok`'s context it needs (`hk`, the stack bound, `env.Static m`, `NEXT`'s bound, the objects). `Inv` states every register the body reads in the form `rv_sym` computes (pointers as `base + BitVec.ofNat 64 (16 * j) + 8#64`), the accumulator as the Model's fold over `take j`, the saved registers, `env.Frame top Tactic.F m M`, and the prologue's stores as `∀ a, top + -frame ≤ a → M.getMem a = (stores).getMem a`. Proof: `induction k`, each case `intro j R M hj hinv; rv_intro hinv; rv_sym hp with [hL] using [...]`; at the back edge `apply ih (j + 1) _ _ (by omega)` then `rv_close`; what is left is the pointer step, the fold step and the exit test. In `ok`, `refine loop … (len - 1) 0 _ _ (by omega) ?_` then `rv_close`.
- Name branch hypotheses as `rv_sym` does: the latest `hc`, earlier ones `hc_1`, `hc_2`; split facts are `hpre_k`, `hret<call>_<k>`, `hinv_k`.

## Cost

Record each function in `notes/proof-log.tsv`: `module`, `instr` (from `Gen/index.tsv`), `loops`, `proof_lines` (lines of `ok` and its loop lemmas), `cpu_s` (tactic plus kernel, `set_option profiler true` on a copy, or `/usr/bin/time` less the imports), `manual_notes` (what was not automatic). A straight-line function should cost about a second; if it costs more, profile before anything else.

## Pitfalls

- Never prove an equation the kernel must find by unfolding a value: no `Eq.refl` between a register read and a computed value, no literal arithmetic by `rfl` (the kernel unfolds `2^64 - 1` one successor at a time, and a `mulhu` value into `Nat.div`). Use the named lemmas `rv_sym` uses, or `decide` for closed facts.
- Never run `bv_omega` or `omega` on a goal whose context holds the program's state: it carries the whole context into every auxiliary proof. State the arithmetic as a lemma with only what it needs (`end_iff`, `step_ptr`) and apply it.
- `any_goals exact lemma _ _` on goals the lemma does not fit can unify for minutes: close goals in order, one bullet each.
- Write literals as `0x…#64`, as the templates do; `(16 : BitVec 64)` is another term and stops a syntactic match.
- A representation predicate (`EListAt`, `Live`) is kept whole in hypotheses; `SliceArgs` and your own `Pre`/`Post` definitions are split into their conjuncts.
- Warnings fail the build: no unused `all_goals`, no deprecated lemma names.
