# How to prove a function

The worked examples are `E::mul` (no loop) and `eq_eval` (a loop, a heap slice, a panic): copy their files.

## Files

- `Rv64mc/Spec/<Area>/<Fn>.lean`: `need` (frame size plus the deepest callee's `need`, from the template's first `addi sp, sp, -N`), `Pre`, `Post` in terms of the Model's mirror (`Model.eMul`, `Model.eqEvalRust`) and `Core/Repr.lean`'s predicates (`EListAt`, `SliceArgs`, `Env.Live`), and `def spec env p i := Holds env p i need Pre Post` (ghost values, such as a slice's elements, quantified outside: `∀ xs ys, Holds …`). Arguments in registers as the RISC-V ABI passes them: an `E` by value is two registers (`c0`, `c1`), a `u128` is low then high (`Spec.Field.lo128`, `hi128`), a slice is a pointer and a length. No proof here.
- `Rv64mc/Proof/<Area>/<Fn>.lean`: `theorem ok (env) (p) (i) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p) (<one hypothesis per callee: Callee.spec env p L.<callee>.idx>) : <Fn>.spec env p i`, over the generated template (`Gen.Tmpl.<Module>`), never an address or an index.
- `Rv64mc/Table/<Area>.lean`: each `ok` at `liftProg Gen.fns` and its index (`Rv64mc/Gen/index.tsv`), with `Gen.<Module>.tmpl_eq` and `wf`, a callee's `Table` theorem as its hypothesis (or a hypothesis of the table theorem while that callee is unproved).
- A callee not proved yet: write its `Spec` file anyway (its `need` from its frame and its own callees) and take `Callee.spec env p L.callee.idx` as a hypothesis. A callee that never returns is `Spec.Runtime.NoReturn env p idx 0`.

## The proof

```lean
theorem ok … : EMul.spec env p i := by
  rv_auto hp with [hL] using [hcl, hrd]
  all_goals simp only [Model.eMul, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1]
  all_goals simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, append_hi_lo]
```

- `rv_auto hp with [hL] using [callee specs]` steps every path and closes the calling convention, every callee's precondition (its stack room, `env.Static`, `NEXT`), the memory frame (`Env.Frame`, own stack stores and callees' frames), `env.Static` and the saved registers. What it leaves: the functional part of `Post` (and of a callee's `Pre`), and a goal at every loop head (the target of a backward jump). `with` takes the link's facts (`hL` whole); `using` takes contracts (`Holds`, `NoReturn`, or `∀ f, …`). `stop [pc]` adds a stop (`pc` is the index in the body: label `k` is at `2k`).
- Functional goals: unfold the Model (`simp only [Model.f]`), put XORs in one order (`BitVec.xor_assoc`, `BitVec.xor_comm`, `xor_left_comm`), `ac_rfl` at one level. Values loaded from a heap object read `M.getMem (p + BitVec.ofNat 64 (16 * j))`: rewrite with a `load` lemma through the frame (`EListAt.load`, `Proof/Field/Slice.lean`).
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
