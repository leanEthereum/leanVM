# Patterns: before and after

Short sketches; the names are illustrative.

## A monolithic tactic block becomes named steps

Before: the reader replays forty tactics to learn what was shown.

```lean
theorem verify_accepts (h : Honest π) : verify π = true := by
  unfold verify readSizes checkStack
  simp [h.sizes, h.stack, List.all_eq_true]
  intro i hi
  rcases h.rows i hi with ⟨a, b, hab⟩
  ...
```

After: each step states what it establishes, and each can be repaired alone.

```lean
theorem verify_accepts (h : Honest π) : verify π = true := by
  -- the sizes read from the proof are the honest prover's
  have hSizes : readSizes π = some (sizesOf π) := readSizes_of_honest h
  -- every stacked row passes its check
  have hRows : ∀ i < π.rows.length, rowOk π i := fun i hi => rowOk_of_honest h i hi
  exact verify_eq_true_of hSizes hRows
```

## A positional literal becomes a stable name

Before: the proof breaks when an edit inserts a statement before position 62094.

```lean
have := (Fn.body (fnAt 17)).get! 62094
rw [show (drop 1358 stmts).head? = some s from rfl]
```

After: the names survive renumbering (`formal/AGENTS.md`, "Changing the spec", lists the mechanisms).

```lean
have := val% «verify_sub» "g_squares"
rw [show stmtAt (pos% «verify_sub» "acc@2") = some s from rfl]
```

## Unfolding a definition becomes its contract lemma

Before: every consumer unfolds, so every consumer breaks when the definition changes shape.

```lean
theorem foo : P (phaseX st) := by
  unfold phaseX; simp only [bind, Option.bind]; split <;> ...
```

After: the owning module states the definition's normal form once; consumers rewrite with it.

```lean
-- in the module that defines phaseX
theorem phaseX_eq : phaseX st = liftOption (xOf st) := by ...
-- in the consumer
theorem foo : P (phaseX st) := by rw [phaseX_eq]; exact p_of_xOf st
```

## A proof copied per instance becomes one lemma

Before: the same twenty lines for each of eight functions, edited by hand when one changes.

```lean
theorem readsOk_f1 : ReadsOk f1 := by unfold ReadsOk f1; decide
theorem readsOk_f2 : ReadsOk f2 := by unfold ReadsOk f2; decide
...
```

After: one checker proved sound, and each instance a kernel evaluation (or a generated instance).

```lean
theorem readsOk_of_check (h : checkReads f = true) : ReadsOk f := ...
theorem readsOk_f1 : ReadsOk f1 := readsOk_of_check (by decide +kernel)
```

## A non-terminal bare `simp` becomes `simp only` or a stated step

Before: the next tactic depends on whatever shape `simp` left, which changes with Mathlib.

```lean
  simp at h
  rw [Nat.add_comm] at h
  exact h.2
```

After: the shape is fixed by a lemma list, or stated outright.

```lean
  simp only [List.mem_cons, Nat.lt_succ_iff] at h
  rw [Nat.add_comm] at h
  exact h.2
-- or
  have h' : a + b < n := by simpa using h
  exact h'
```

## A budget becomes a fix

Before: the budget hides an evaluation the elaborator should not do.

```lean
set_option maxHeartbeats 4000000 in
theorem addr_one : addressOfIndex 1 = g := by simp [addressOfIndex]
```

After: an algebraic lemma, or a kernel decision on a closed goal, then a rewrite.

```lean
theorem addr_one : addressOfIndex 1 = g := by rw [addressOfIndex, pow_one]
-- or, for a closed concrete equation
rw [show channelSep MemPush.toRaw = g by decide +kernel]
```
