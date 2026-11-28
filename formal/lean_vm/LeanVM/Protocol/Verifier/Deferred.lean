/-
  LeanVM.Protocol.Verifier.Deferred

  What a verifier program may return (`VerifierProgram.Returns`), read off a successful run, and
  the split program's algebra that the deferring verifier rests on: the program side of the link
  reads the split only on `splitColumns tables`, so a fresh claim's values give the computed
  split's program side.
-/

module

import LeanVM.Protocol.Verifier.PackedLength

public import LeanVM.Protocol.RunWithHash
public import Statement.LeanVmGuestBatching

/-!
# The deferring verifier's split

The deployed verifier computes the program's split at the link's point (`computedSplit`,
`Bytecode::split`); the deferring verifier takes it from a child's fresh claim
(`freshSplit fresh`: `Split.ofColumns tables fresh.values`, zero off the split columns). The two
splits differ where no split column is, but the link reads a split only through its program side
(`programSide`: `verify_link`'s fold over the tables and their operand slots), weighted by
`slot_weights`; and `slot_weights` is zero off the split columns (`slotWeights_zero`), since both
name exactly the slots the tables' links read: the operand slots of the program link, an access's
frame slot and its slot, frame and `pc` reads (`splitColumns_*`). So the program side of the
computed split equals that of the split the true fresh claim gives
(`programSide_ofColumns_splitValues`).

`VerifierProgram.Returns p a`, along some run `p` may return `a`, is read off a successful run
(`returns_of_run`) and walked with `returns_bind`.
-/

@[expose] public section

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

namespace VerifierProgram

variable {α β : Type}

theorem pure_eq' (a : α) : (pure a : VerifierProgram α) = ret a := rfl

theorem bind_eq' (p : VerifierProgram α) (f : α → VerifierProgram β) : p >>= f = p.bind f := rfl

theorem ret_bind' (a : α) (f : α → VerifierProgram β) : (ret a).bind f = f a := rfl

theorem bind_assoc' {γ : Type} (p : VerifierProgram α) (f : α → VerifierProgram β)
    (g : β → VerifierProgram γ) : (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | readPacked n k ih => simp only [bind, ih]
  | samplePacked n k ih => simp only [bind, ih]
  | grind b k ih => simp only [bind, ih]
  | commit h w k ih => simp only [bind, ih]
  | query i ps k ih => simp only [bind, ih]

/-- **`p` may return `a`**, along some run. -/
inductive Returns : VerifierProgram α → α → Prop where
  /-- A return. -/
  | ret (a : α) : Returns (ret a) a
  /-- After reading a scalar. -/
  | read {k : E → VerifierProgram α} {a : α} (x : E) : Returns (k x) a → Returns (read k) a
  /-- After sampling a challenge. -/
  | sample {k : E → VerifierProgram α} {a : α} (x : E) : Returns (k x) a → Returns (sample k) a
  /-- After reading a packed message. -/
  | readPacked (n : ℕ) {k : List E → VerifierProgram α} {a : α} (xs : List E) :
      xs.length = n → Returns (k xs) a → Returns (readPacked n k) a
  /-- After a packed draw. -/
  | samplePacked (n : ℕ) {k : List E → VerifierProgram α} {a : α} (xs : List E) :
      xs.length = n → Returns (k xs) a → Returns (samplePacked n k) a
  /-- After a proof of work. -/
  | grind (bits : ℕ) {k : VerifierProgram α} {a : α} : Returns k a → Returns (grind bits k) a
  /-- After a commitment. -/
  | commit (height width : ℕ) {k : VerifierProgram α} {a : α} :
      Returns k a → Returns (commit height width k) a
  /-- After an opening. -/
  | query (i : ℕ) (positions : List ℕ) {k : List (List K) → VerifierProgram α} {a : α}
      (rows : List (List K)) : Returns (k rows) a → Returns (query i positions k) a

/-- **`p` may return `a` along some path of its tree**, a packed message or draw of any length:
`Returns` without the lengths, what the wire's cost calculus quantifies over. -/
inductive ReturnsAny : VerifierProgram α → α → Prop where
  | ret (a : α) : ReturnsAny (ret a) a
  | read {k : E → VerifierProgram α} {a : α} (x : E) : ReturnsAny (k x) a → ReturnsAny (read k) a
  | sample {k : E → VerifierProgram α} {a : α} (x : E) : ReturnsAny (k x) a →
      ReturnsAny (sample k) a
  | readPacked (n : ℕ) {k : List E → VerifierProgram α} {a : α} (xs : List E) :
      ReturnsAny (k xs) a → ReturnsAny (readPacked n k) a
  | samplePacked (n : ℕ) {k : List E → VerifierProgram α} {a : α} (xs : List E) :
      ReturnsAny (k xs) a → ReturnsAny (samplePacked n k) a
  | grind (bits : ℕ) {k : VerifierProgram α} {a : α} : ReturnsAny k a → ReturnsAny (grind bits k) a
  | commit (height width : ℕ) {k : VerifierProgram α} {a : α} :
      ReturnsAny k a → ReturnsAny (commit height width k) a
  | query (i : ℕ) (positions : List ℕ) {k : List (List K) → VerifierProgram α} {a : α}
      (rows : List (List K)) : ReturnsAny (k rows) a → ReturnsAny (query i positions k) a

theorem Returns.toAny {p : VerifierProgram α} {a : α} (h : Returns p a) : ReturnsAny p a := by
  induction h with
  | ret a => exact .ret a
  | read x _ ih => exact .read x ih
  | sample x _ ih => exact .sample x ih
  | readPacked n xs _ _ ih => exact .readPacked n xs ih
  | samplePacked n xs _ _ ih => exact .samplePacked n xs ih
  | grind b _ ih => exact .grind b ih
  | commit h w _ ih => exact .commit h w ih
  | query i ps rows _ ih => exact .query i ps rows ih

theorem returnsAny_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β}
    (h : ReturnsAny (p >>= f) b) : ∃ a, ReturnsAny p a ∧ ReturnsAny (f a) b := by
  induction p with
  | ret a => exact ⟨a, .ret a, h⟩
  | fail => cases h
  | read k ih => cases h with
    | read x h => obtain ⟨a, ha, hb⟩ := ih x h; exact ⟨a, .read x ha, hb⟩
  | sample k ih => cases h with
    | sample x h => obtain ⟨a, ha, hb⟩ := ih x h; exact ⟨a, .sample x ha, hb⟩
  | readPacked n k ih => cases h with
    | readPacked _ xs h => obtain ⟨a, ha, hb⟩ := ih xs h; exact ⟨a, .readPacked n xs ha, hb⟩
  | samplePacked n k ih => cases h with
    | samplePacked _ xs h => obtain ⟨a, ha, hb⟩ := ih xs h; exact ⟨a, .samplePacked n xs ha, hb⟩
  | grind b k ih => cases h with
    | grind _ h => obtain ⟨a, ha, hb⟩ := ih h; exact ⟨a, .grind _ ha, hb⟩
  | commit hh w k ih => cases h with
    | commit _ _ h => obtain ⟨a, ha, hb⟩ := ih h; exact ⟨a, .commit _ _ ha, hb⟩
  | query i ps k ih => cases h with
    | query _ _ r h => obtain ⟨a, ha, hb⟩ := ih r h; exact ⟨a, .query _ _ r ha, hb⟩

theorem returnsAny_ret {a b : α} (h : ReturnsAny (ret a : VerifierProgram α) b) : b = a := by
  cases h; rfl

theorem returnsAny_require {c : Prop} [Decidable c] {u : Unit} (h : ReturnsAny (require c) u) :
    c := by
  unfold require at h
  split at h
  · assumption
  · cases h

theorem returns_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β}
    (h : Returns (p >>= f) b) : ∃ a, Returns p a ∧ Returns (f a) b := by
  induction p with
  | ret a => exact ⟨a, .ret a, h⟩
  | fail => cases h
  | read k ih =>
    cases h with
    | read x h => obtain ⟨a, ha, hb⟩ := ih x h; exact ⟨a, .read x ha, hb⟩
  | sample k ih =>
    cases h with
    | sample x h => obtain ⟨a, ha, hb⟩ := ih x h; exact ⟨a, .sample x ha, hb⟩
  | readPacked n k ih =>
    cases h with
    | readPacked _ xs hl h => obtain ⟨a, ha, hb⟩ := ih xs h; exact ⟨a, .readPacked n xs hl ha, hb⟩
  | samplePacked n k ih =>
    cases h with
    | samplePacked _ xs hl h =>
      obtain ⟨a, ha, hb⟩ := ih xs h; exact ⟨a, .samplePacked n xs hl ha, hb⟩
  | grind b k ih =>
    cases h with
    | grind _ h => obtain ⟨a, ha, hb⟩ := ih h; exact ⟨a, .grind _ ha, hb⟩
  | commit hh w k ih =>
    cases h with
    | commit _ _ h => obtain ⟨a, ha, hb⟩ := ih h; exact ⟨a, .commit _ _ ha, hb⟩
  | query i ps k ih =>
    cases h with
    | query _ _ r h => obtain ⟨a, ha, hb⟩ := ih r h; exact ⟨a, .query _ _ r ha, hb⟩

theorem returns_ret {a b : α} (h : Returns (ret a : VerifierProgram α) b) : b = a := by
  cases h; rfl

/-- A requirement that may return holds. -/
theorem returns_require {c : Prop} [Decidable c] {u : Unit} (h : Returns (require c) u) : c := by
  unfold require at h
  split at h
  · assumption
  · cases h

/-- A program's successful run returns what the program may return. -/
theorem returns_of_run (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    {p : VerifierProgram α} :
    ∀ {s : VerifierProgramState} {a : α} {s' : VerifierProgramState},
      runWithHash H F p s = some (a, s') → Returns p a := by
  induction p with
  | ret b =>
    intro s a s' h
    simp only [runWithHash] at h
    cases h
    exact .ret b
  | fail => intro s a s' h; simp [runWithHash] at h
  | read k ih =>
    intro s a s' h
    simp only [runWithHash] at h
    rcases hs : s.stream with _ | ⟨x, xs⟩ <;> rcases hg : s.sponge.ground with _ | g <;>
      simp only [hs, hg] at h
    · simp [pure] at h
    · simp [pure] at h
    · exact .read x (ih x h)
    · simp [pure] at h
  | sample k ih => intro s a s' h; simp only [runWithHash] at h; exact .sample _ (ih _ h)
  | readPacked n k ih =>
    intro s a s' h
    simp only [runWithHash] at h
    split at h
    · next hc => exact .readPacked n _ (List.length_take_of_le hc.2) (ih _ h)
    · simp [pure] at h
  | samplePacked n k ih =>
    intro s a s' h; simp only [runWithHash] at h
    exact .samplePacked n _ (VerifierProgram.length_samplesPacked F s.sponge n) (ih _ h)
  | grind bits k ih =>
    intro s a s' h
    simp only [runWithHash] at h
    rcases hs : s.stream with _ | ⟨n, xs⟩ <;> rcases hg : s.sponge.ground with _ | g <;>
      simp only [hs, hg] at h
    · simp [pure] at h
    · simp [pure] at h
    · revert h
      generalize absorbNonce F s.sponge n = pr
      obtain ⟨pow, sp⟩ := pr
      intro h
      change (if _ then _ else _) = _ at h
      split at h
      · exact .grind bits (ih h)
      · simp [pure] at h
    · simp [pure] at h
  | commit height width k ih =>
    intro s a s' h
    simp only [runWithHash] at h
    rcases hs : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;>
      rcases hg : s.sponge.ground with _ | g <;> simp only [hs, hg] at h
    all_goals first | exact .commit height width (ih h) | simp [pure] at h
  | query i ps k ih =>
    intro s a s' h
    obtain ⟨_, _, _, _, _, rows, _, _, _, hk⟩ :=
      (runWithHash_query_eq_some_iff H F i ps k s _).mp h
    exact .query i ps rows (ih rows hk)

end VerifierProgram

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Node

/-! ## The runs' facts -/

/-- A lifted option that may return `a` is `some a`. -/
theorem returnsAny_liftOption {α : Type} {o : Option α} {a : α}
    (h : VerifierProgram.ReturnsAny (liftOption o) a) : o = some a := by
  unfold liftOption at h
  split at h
  · cases h
  · exact congrArg some (VerifierProgram.returnsAny_ret h).symm

theorem returns_liftOption {α : Type} {o : Option α} {a : α}
    (h : VerifierProgram.Returns (liftOption o) a) : o = some a := by
  unfold liftOption at h
  split at h
  · cases h
  · rw [VerifierProgram.returns_ret h]

/-- A power of two's bits: `n &&& (n - 1) = 0` with `0 < n` is `n = 2^k` at `2^k ≤ n < 2^(k+1)`. -/
theorem eq_pow_of_and_pred {n k : ℕ} (hand : n &&& (n - 1) = 0) (hlo : 2 ^ k ≤ n)
    (hhi : n < 2 ^ (k + 1)) : n = 2 ^ k := by
  by_contra hne
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 ^ k + m := ⟨n - 2 ^ k, by omega⟩
  have hm' : m < 2 ^ k := by rw [pow_succ] at hhi; omega
  have h1 : (2 ^ k + m).testBit k = true := by
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm']; rfl
  have h2 : (2 ^ k + m - 1).testBit k = true := by
    rw [show 2 ^ k + m - 1 = 2 ^ k + (m - 1) by omega, Nat.testBit_two_pow_add_eq,
      Nat.testBit_lt_two_pow (by omega)]; rfl
  have h := congrArg (·.testBit k) hand
  simp [Nat.testBit_and, h1, h2] at h

/-- `log2Strict` of a power of two's length: the length is `2` to it. -/
theorem pow_of_log2Strict {n k : ℕ} (h : log2Strict n = some k) : n = 2 ^ k := by
  unfold log2Strict at h
  split at h
  · next hn =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hpos, hand⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hb : bitLength n - 1 = Nat.log2 n := by unfold bitLength; simp [hn0]
    rw [hb]
    exact eq_pow_of_and_pred hand (Nat.log2_self_le hn0) Nat.lt_log2_self
  · cases h

/-- The layout `buildLayout` gives: the bytecode and the tables it was given, and the program's
log-size, its length `2^(BYTECODE_SLOT_BITS + log_bytecode)` and at most `MAX_LOG_BYTECODE`. -/
theorem buildLayout_facts {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    layout.bytecode = bytecode ∧ layout.tables = tables ∧
      bytecode.length >>> bytecodeSlotBits = 2 ^ layout.logBytecode ∧ layout.logBytecode ≤ maxLogBytecode := by
  unfold buildLayout at h
  split at h
  · cases h
  · next logLength hlog =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, ?_, by simp only; omega⟩
      simp only
      rw [pow_of_log2Strict hlog, Nat.shiftRight_eq_div_pow, Nat.pow_div hc.2.2.2.1 (by norm_num)]
    · cases h

/-- What `readAnnouncedSizes` returns: a layout `buildLayout` gives. -/
theorem readSizes_facts {bytecode : List K} {x : Layout × ℕ}
    (h : VerifierProgram.Returns (readAnnouncedSizes bytecode) x) :
    x.1.bytecode = bytecode ∧ x.1.tables = tables ∧
      bytecode.length >>> bytecodeSlotBits = 2 ^ x.1.logBytecode ∧ x.1.logBytecode ≤ maxLogBytecode := by
  unfold readAnnouncedSizes at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨layout, hl, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  exact buildLayout_facts (returns_liftOption hl)

/-- A sumcheck's point has one challenge per round, on any path. -/
theorem returnsAny_sumcheck {count : ℕ} :
    ∀ {eqs : List (Option E)} {claim : E} {x : List E × E},
      VerifierProgram.ReturnsAny (sumcheck claim count eqs) x → x.1.length = eqs.length
  | [], claim, x, h => by unfold sumcheck at h; rw [VerifierProgram.returnsAny_ret h]; rfl
  | e :: es, claim, x, h => by
    unfold sumcheck at h
    obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
    obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
    obtain ⟨⟨pt, fin⟩, hp, h⟩ := VerifierProgram.returnsAny_bind h
    rw [VerifierProgram.returnsAny_ret h, List.length_cons, List.length_cons, ← returnsAny_sumcheck hp]

/-- A sumcheck's point has one challenge per round. -/
theorem returns_sumcheck {count : ℕ} :
    ∀ {eqs : List (Option E)} {claim : E} {x : List E × E},
      VerifierProgram.Returns (sumcheck claim count eqs) x → x.1.length = eqs.length
  | [], claim, x, h => by unfold sumcheck at h; rw [VerifierProgram.returns_ret h]; rfl
  | e :: es, claim, x, h => by
    unfold sumcheck at h
    obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨⟨pt, fin⟩, hp, h⟩ := VerifierProgram.returns_bind h
    rw [VerifierProgram.returns_ret h, List.length_cons, List.length_cons, ← returns_sumcheck hp]

/-- `Chunks::new` keeps the width it was given. -/
theorem Chunks.new_width {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : c.width = w := by
  unfold Chunks.new at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · cases h

/-! ## The split columns -/

section Columns

variable {α β : Type}

theorem mem_foldl_of_mem {g : List α → β → List α} (hg : ∀ cs x c, c ∈ cs → c ∈ g cs x) :
    ∀ {l : List β} {cs : List α} {c : α}, c ∈ cs → c ∈ l.foldl g cs
  | [], _, _, h => h
  | y :: l, cs, c, h => by
    rw [List.foldl_cons]; exact mem_foldl_of_mem (l := l) hg (hg cs y c h)

theorem mem_foldl_of_step {g : List α → β → List α} (hg : ∀ cs x c, c ∈ cs → c ∈ g cs x)
    {c : α} {x : β} (hc : ∀ cs, c ∈ g cs x) : ∀ {l : List β} {cs : List α}, x ∈ l →
      c ∈ l.foldl g cs
  | [], _, h => by cases h
  | y :: l, cs, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_foldl_of_mem (l := l) hg (hc cs)
    · exact mem_foldl_of_step (l := l) hg hc h

end Columns

/-- `note`, `splitColumns`' step: the list with `c`, appended if new. -/
abbrev noteColumn (columns : List SplitColumn) (c : SplitColumn) : List SplitColumn :=
  if c ∈ columns then columns else columns ++ [c]

theorem mem_noteColumn_self (columns : List SplitColumn) (c : SplitColumn) :
    c ∈ noteColumn columns c := by
  unfold noteColumn; split
  · assumption
  · simp

theorem mem_noteColumn_of_mem {columns : List SplitColumn} {c' : SplitColumn} (c : SplitColumn)
    (h : c' ∈ columns) : c' ∈ noteColumn columns c := by
  unfold noteColumn; split
  · exact h
  · simp [h]

/-- One table's step of `splitColumns`, table `t`'s columns noted. -/
def tableColumnsStep : List SplitColumn → Table × ℕ → List SplitColumn := fun columns (table, t) ↦
  let links := table.links
  let columns := links.bytecodeLink.operands.foldl
    (fun columns (slots, _) ↦ slots.foldl (fun columns s ↦ noteColumn columns (.slot t s)) columns)
    columns
  links.memory.foldl (fun columns access ↦
    let columns := match access.frame with
      | some (s, _) => noteColumn columns (.slot t s)
      | none => columns
    access.reads.foldl (fun columns read ↦
      match read with
      | .word _ _ => columns
      | .slot slot _ => noteColumn columns (.slot t slot)
      | .frame slot _ => noteColumn columns (.slot t slot)
      | .pc slot _ => noteColumn columns (.pc t slot)) columns) columns

theorem splitColumns_eq (tl : List Table) :
    splitColumns tl = tl.zipIdx.foldl tableColumnsStep ((List.range tl.length).map .count) := rfl

section Steps

theorem operandStep_mono (t : ℕ) (cs : List SplitColumn) (x : List ℕ × Form) (c : SplitColumn)
    (h : c ∈ cs) : c ∈ x.1.foldl (fun columns s ↦ noteColumn columns (.slot t s)) cs :=
  mem_foldl_of_mem (fun _ _ _ h ↦ mem_noteColumn_of_mem _ h) h

theorem readStep_mono (t : ℕ) (cs : List SplitColumn) (read : Read) (c : SplitColumn)
    (h : c ∈ cs) : c ∈ (match read with
      | .word _ _ => cs
      | .slot slot _ => noteColumn cs (.slot t slot)
      | .frame slot _ => noteColumn cs (.slot t slot)
      | .pc slot _ => noteColumn cs (.pc t slot)) := by
  cases read <;> first | exact h | exact mem_noteColumn_of_mem _ h

theorem accessStep_mono (t : ℕ) (cs : List SplitColumn) (access : Access) (c : SplitColumn)
    (h : c ∈ cs) : c ∈ access.reads.foldl (fun columns read ↦
      match read with
      | .word _ _ => columns
      | .slot slot _ => noteColumn columns (.slot t slot)
      | .frame slot _ => noteColumn columns (.slot t slot)
      | .pc slot _ => noteColumn columns (.pc t slot))
      (match access.frame with
      | some (s, _) => noteColumn cs (.slot t s)
      | none => cs) := by
  refine mem_foldl_of_mem (readStep_mono t) ?_
  split
  · exact mem_noteColumn_of_mem _ h
  · exact h

theorem tableColumnsStep_mono (cs : List SplitColumn) (tt : Table × ℕ) (c : SplitColumn)
    (h : c ∈ cs) : c ∈ tableColumnsStep cs tt := by
  obtain ⟨T, t⟩ := tt
  exact mem_foldl_of_mem (accessStep_mono t) (mem_foldl_of_mem (operandStep_mono t) h)

/-- A column table `t`'s step notes is in the split columns. -/
theorem mem_splitColumns_of_step {tl : List Table} {t : ℕ} {T : Table} (ht : tl[t]? = some T)
    {c : SplitColumn} (hc : ∀ cs, c ∈ tableColumnsStep cs (T, t)) : c ∈ splitColumns tl := by
  rw [splitColumns_eq]
  exact mem_foldl_of_step tableColumnsStep_mono hc (List.mem_zipIdx_iff_getElem?.mpr ht)

/-- A column the memory accesses' step notes, whatever came before. -/
theorem mem_tableColumnsStep_of_access {T : Table} {t : ℕ} {c : SplitColumn}
    (hc : ∃ access ∈ T.links.memory, ∀ cs, c ∈ access.reads.foldl (fun columns read ↦
      match read with
      | .word _ _ => columns
      | .slot slot _ => noteColumn columns (.slot t slot)
      | .frame slot _ => noteColumn columns (.slot t slot)
      | .pc slot _ => noteColumn columns (.pc t slot))
      (match access.frame with
      | some (s, _) => noteColumn cs (.slot t s)
      | none => cs)) (cs : List SplitColumn) : c ∈ tableColumnsStep cs (T, t) := by
  obtain ⟨access, ha, hc⟩ := hc
  exact mem_foldl_of_step (accessStep_mono t) hc ha

theorem mem_readsFold_of_read {t : ℕ} {reads : List Read} {read : Read} (hr : read ∈ reads)
    {c : SplitColumn}
    (hc : ∀ cs, c ∈ (match read with
      | .word _ _ => cs
      | .slot slot _ => noteColumn cs (.slot t slot)
      | .frame slot _ => noteColumn cs (.slot t slot)
      | .pc slot _ => noteColumn cs (.pc t slot))) (cs : List SplitColumn) :
    c ∈ reads.foldl (fun columns read ↦
      match read with
      | .word _ _ => columns
      | .slot slot _ => noteColumn columns (.slot t slot)
      | .frame slot _ => noteColumn columns (.slot t slot)
      | .pc slot _ => noteColumn columns (.pc t slot)) cs :=
  mem_foldl_of_step (readStep_mono t) hc hr

end Steps

/-- Every opcode's count is a split column. -/
theorem count_mem_splitColumns {tl : List Table} {t : ℕ} (ht : t < tl.length) :
    SplitColumn.count t ∈ splitColumns tl := by
  rw [splitColumns_eq]
  exact mem_foldl_of_mem tableColumnsStep_mono (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)

/-- The program link's operand slots of table `t` are split columns. -/
theorem operand_mem_splitColumns {tl : List Table} {t : ℕ} {T : Table} (ht : tl[t]? = some T)
    {x : List ℕ × Form} (hx : x ∈ T.links.bytecodeLink.operands) {s : ℕ} (hs : s ∈ x.1) :
    SplitColumn.slot t s ∈ splitColumns tl := by
  refine mem_splitColumns_of_step ht fun cs ↦ ?_
  refine mem_foldl_of_mem (accessStep_mono t) ?_
  refine mem_foldl_of_step (operandStep_mono t) (fun cs ↦ ?_) hx
  exact mem_foldl_of_step (g := fun columns s ↦ noteColumn columns (SplitColumn.slot t s))
    (fun _ _ _ h ↦ mem_noteColumn_of_mem _ h) (fun cs ↦ mem_noteColumn_self cs _) hs

/-- An access's frame slot of table `t` is a split column. -/
theorem frame_mem_splitColumns {tl : List Table} {t : ℕ} {T : Table} (ht : tl[t]? = some T)
    {access : Access} (ha : access ∈ T.links.memory) {s e : ℕ} (hf : access.frame = some (s, e)) :
    SplitColumn.slot t s ∈ splitColumns tl := by
  refine mem_splitColumns_of_step ht (mem_tableColumnsStep_of_access ⟨access, ha, fun cs ↦ ?_⟩)
  refine mem_foldl_of_mem (readStep_mono t) ?_
  rw [hf]
  exact mem_noteColumn_self _ _

/-- An access's slot and frame reads of table `t` are split columns, and its `pc` reads. -/
theorem read_mem_splitColumns {tl : List Table} {t : ℕ} {T : Table} (ht : tl[t]? = some T)
    {access : Access} (ha : access ∈ T.links.memory) {read : Read} (hr : read ∈ access.reads) :
    (∀ s scale, read = .slot s scale → SplitColumn.slot t s ∈ splitColumns tl) ∧
    (∀ s scale, read = .frame s scale → SplitColumn.slot t s ∈ splitColumns tl) ∧
    (∀ s scale, read = .pc s scale → SplitColumn.pc t s ∈ splitColumns tl) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro s scale hrs <;>
    refine mem_splitColumns_of_step ht (mem_tableColumnsStep_of_access ⟨access, ha, fun cs ↦ ?_⟩) <;>
    refine mem_readsFold_of_read hr (fun cs ↦ ?_) _ <;> subst hrs <;> exact mem_noteColumn_self _ _

/-! ## The weights vanish off the split columns -/

/-- `w` is zero off `P`. -/
def ZeroOff (w : List E) (P : ℕ → Prop) : Prop := ∀ s, ¬ P s → w.getD s 0 = 0

theorem zeroOff_addAtSlot {w : List E} {P : ℕ → Prop} (hw : ZeroOff w P) {s' : ℕ} (hs : P s')
    (v : E) : ZeroOff (addAtSlot w s' v) P := by
  intro s hns
  have hne : s' ≠ s := fun h ↦ hns (h ▸ hs)
  unfold addAtSlot
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
  exact hw s hns

theorem zeroOff_replicate (P : ℕ → Prop) (n : ℕ) : ZeroOff (List.replicate n (0 : E)) P := by
  intro s _
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem foldl_inv {γ δ : Type} {I : γ → Prop} {f : γ → δ → γ} :
    ∀ {l : List δ} {a : γ}, (∀ a x, x ∈ l → I a → I (f a x)) → I a → I (l.foldl f a)
  | [], _, _, h => h
  | x :: l, a, hf, h =>
    foldl_inv (l := l) (fun a y hy ↦ hf a y (List.mem_cons_of_mem _ hy)) (hf a x (by simp) h)

/-- **One table's slot weights vanish off its named slots**: `omega` off slot `3` and the slots
named by `columns`, `frame` off the slots `columns` names, `pc` off the `pc` columns it names,
given that `columns` names every slot the table's links read. -/
theorem tableSlotWeights_zero (T : Table) (t : ℕ) (columns : List SplitColumn)
    (hop : ∀ x ∈ T.links.bytecodeLink.operands, ∀ s ∈ x.1, SplitColumn.slot t s ∈ columns)
    (hfr : ∀ access ∈ T.links.memory, ∀ s e, access.frame = some (s, e) →
      SplitColumn.slot t s ∈ columns)
    (hrd : ∀ access ∈ T.links.memory, ∀ read ∈ access.reads,
      (∀ s scale, read = .slot s scale → SplitColumn.slot t s ∈ columns) ∧
      (∀ s scale, read = .frame s scale → SplitColumn.slot t s ∈ columns) ∧
      (∀ s scale, read = .pc s scale → SplitColumn.pc t s ∈ columns))
    (slot : List E) (gamma : E × E) (mu : List E) (etaMem etaBc : E) :
    let w := tableSlotWeights T slot gamma mu etaMem etaBc
    ZeroOff w.1 (fun s ↦ s = 3 ∨ SplitColumn.slot t s ∈ columns) ∧
      ZeroOff w.2.1 (fun s ↦ SplitColumn.pc t s ∈ columns) ∧
      ZeroOff w.2.2 (fun s ↦ SplitColumn.slot t s ∈ columns) := by
  intro w
  let Po := fun s ↦ s = 3 ∨ SplitColumn.slot t s ∈ columns
  have h0 : ZeroOff ((List.replicate (2 ^ bytecodeSlotBits) (0 : E)).set 3 (etaBc * slot.getD 3 0)) Po := by
    intro s hs
    have hne : 3 ≠ s := fun h ↦ hs (Or.inl h.symm)
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
    exact zeroOff_replicate _ _ s hs
  have h1 := foldl_inv (I := fun omega ↦ ZeroOff omega Po)
    (f := fun omega (x : List ℕ × Form) ↦ x.1.foldl (fun omega s ↦
      addAtSlot omega s (etaBc * slot.getD (x.1.headD 0) 0)) omega)
    (l := T.links.bytecodeLink.operands)
    (fun omega x hx hw ↦ foldl_inv (I := fun omega ↦ ZeroOff omega Po) (fun omega s hs hw ↦
      zeroOff_addAtSlot hw (Or.inr (hop x hx s hs)) _) hw) h0
  let Inv := fun acc : List E × List E × List E ↦ ZeroOff acc.1 Po ∧
      ZeroOff acc.2.1 (fun s ↦ SplitColumn.pc t s ∈ columns) ∧
      ZeroOff acc.2.2 (fun s ↦ SplitColumn.slot t s ∈ columns)
  refine foldl_inv (I := Inv) (fun acc x hx hacc ↦ ?_)
    ⟨h1, zeroOff_replicate _ _, zeroOff_replicate _ _⟩
  obtain ⟨access, m⟩ := x
  have ha : access ∈ T.links.memory := (List.of_mem_zip hx).1
  have hframe : ZeroOff (match access.frame with
      | some (s, e) => addAtSlot acc.2.2 s (etaMem * m * gamma.1 * gpow e)
      | none => acc.2.2) (fun s ↦ SplitColumn.slot t s ∈ columns) := by
    rcases hf : access.frame with _ | ⟨s, e⟩
    · exact hacc.2.2
    · exact zeroOff_addAtSlot hacc.2.2 (hfr access ha s e hf) _
  refine foldl_inv (I := Inv) (fun acc read hr hacc ↦ ?_) ⟨hacc.1, hacc.2.1, hframe⟩
  obtain ⟨hs, hf, hp⟩ := hrd access ha read hr
  cases read with
  | word _ _ => exact hacc
  | slot s scale => exact ⟨zeroOff_addAtSlot hacc.1 (Or.inr (hs s scale rfl)) _, hacc.2.1, hacc.2.2⟩
  | frame s scale => exact ⟨hacc.1, hacc.2.1, zeroOff_addAtSlot hacc.2.2 (hf s scale rfl) _⟩
  | pc s scale => exact ⟨hacc.1, zeroOff_addAtSlot hacc.2.1 (hp s scale rfl) _, hacc.2.2⟩

theorem getD_map_map_zipIdx {γ δ : Type} (tl : List Table) (g : Table × ℕ → γ) (f : γ → List δ)
    (t : ℕ) : ((tl.zipIdx.map g).map f).getD t [] = (tl[t]?.map fun T ↦ f (g (T, t))).getD [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx]
  cases tl[t]? <;> simp

/-- **The program side's weights vanish off the split columns** (`slot_weights`, `link.rs`, against
`split_terms`, `split.rs`): table `t`'s `omega` and `frame` at a slot `s ≠ 3` no split column
names, its `pc` at a `pc` slot none names. -/
theorem slotWeights_zero (tl : List Table) (slot : List E) (gamma : E × E) (mu : List (List E))
    (etaMem etaBc : E) (t s : ℕ) :
    let w := slotWeights tl slot gamma mu etaMem etaBc
    (s ≠ 3 → SplitColumn.slot t s ∉ splitColumns tl →
      (w.omega.getD t []).getD s 0 = 0 ∧ (w.frame.getD t []).getD s 0 = 0) ∧
    (SplitColumn.pc t s ∉ splitColumns tl → (w.pc.getD t []).getD s 0 = 0) := by
  intro w
  simp only [w, slotWeights, getD_map_map_zipIdx]
  rcases ht : tl[t]? with _ | T
  · simp
  · have hz := tableSlotWeights_zero T t (splitColumns tl)
      (fun x hx s hs ↦ operand_mem_splitColumns ht hx hs)
      (fun access ha s e hf ↦ frame_mem_splitColumns ht ha hf)
      (fun access ha read hr ↦ read_mem_splitColumns ht ha hr)
      slot gamma (mu.getD t []) etaMem etaBc
    simp only [Option.map_some, Option.getD_some]
    refine ⟨fun h3 hs ↦ ⟨hz.1 s ?_, hz.2.2 s hs⟩, fun hs ↦ hz.2.1 s hs⟩
    rintro (h | h)
    · exact h3 h
    · exact hs h

/-! ## The program side -/

/-- The program side of the link at `r` (`verify_link`'s fold over the tables, `link.rs`): `X_ω`'s
and `P_fp`'s sums of the split weighted by the slot weights. -/
def programSide (weights : SlotWeights) (split : Split) : E × E :=
  (List.range nTables).foldl (fun (acc : E × E) t ↦
    let omega := weights.omega.getD t []
    let pc := weights.pc.getD t []
    let frame := weights.frame.getD t []
    let slots := split.slots.getD t []
    let pcs := split.pc.getD t []
    let program := acc.1 + omega.getD 3 0 * gpow t * split.count.getD t 0
    ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : E × E) s ↦
      (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
        acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0)

theorem foldl_congr' {γ δ : Type} {f g : γ → δ → γ} :
    ∀ {l : List δ} (a : γ), (∀ a x, x ∈ l → f a x = g a x) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a x (by simp)]
    exact foldl_congr' _ fun a y hy ↦ h a y (List.mem_cons_of_mem _ hy)

/-- Two splits with the same weighted terms have the same program side. -/
theorem programSide_congr (w : SlotWeights) {s1 s2 : Split}
    (hcount : ∀ t < nTables, s1.count.getD t 0 = s2.count.getD t 0)
    (hterm : ∀ t < nTables, ∀ s, 4 ≤ s → s < 2 ^ bytecodeSlotBits →
      ((w.omega.getD t []).getD s 0 * (s1.slots.getD t []).getD s 0 +
          (w.pc.getD t []).getD s 0 * (s1.pc.getD t []).getD s 0 =
        (w.omega.getD t []).getD s 0 * (s2.slots.getD t []).getD s 0 +
          (w.pc.getD t []).getD s 0 * (s2.pc.getD t []).getD s 0) ∧
      (w.frame.getD t []).getD s 0 * (s1.slots.getD t []).getD s 0 =
        (w.frame.getD t []).getD s 0 * (s2.slots.getD t []).getD s 0) :
    programSide w s1 = programSide w s2 := by
  unfold programSide
  refine foldl_congr' _ fun acc t ht ↦ ?_
  have ht' : t < nTables := List.mem_range.mp ht
  simp only
  rw [hcount t ht']
  refine foldl_congr' _ fun acc s hs ↦ ?_
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have hs'' := List.mem_range.mp hs'
  have hlt : s' + 4 < 2 ^ bytecodeSlotBits := by
    have : (2 : ℕ) ^ bytecodeSlotBits = 16 := rfl
    omega
  obtain ⟨e1, e2⟩ := hterm t ht' (s' + 4) (by omega) hlt
  rw [e1, e2]

/-- The value `Split.ofColumns` reads for a split column, from values given column by column. -/
theorem valueOf_map {cs : List SplitColumn} {c : SplitColumn} (hc : c ∈ cs) (f : SplitColumn → E) :
    ((cs.idxOf? c).bind ((cs.map f)[·]?)).getD 0 = f c := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hc)
  obtain ⟨hlt, hci, -⟩ := List.idxOf?_eq_some_iff.mp hi
  rw [hi, Option.bind_some, List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
    Option.getD_some, hci]

theorem nTables_eq_length : tables.length = nTables := by decide

/-- **The fresh claim's split has the computed split's program side**: at a point `point`, the
split `Split.ofColumns tables` of the split columns' values (`splitValues`) and the program's split
(`splitAt`, at the pairs read times `pc`) give the link's program side the same value, at any slot
weights `slot_weights` gives over `tables()`. -/
theorem programSide_ofColumns_splitValues (bytecode : List K) (point : List E) (slot : List E)
    (gamma : E × E) (mu : List (List E)) (etaMem etaBc : E) :
    programSide (slotWeights tables slot gamma mu etaMem etaBc)
        (Split.ofColumns tables (splitValues bytecode point)) =
      programSide (slotWeights tables slot gamma mu etaMem etaBc)
        (splitAt bytecode point (pcSlots tables)) := by
  set split := splitAt bytecode point (pcSlots tables)
  set f : SplitColumn → E := fun
    | .count op => split.count.getD op 0
    | .slot op slot => (split.slots.getD op []).getD slot 0
    | .pc op slot => (split.pc.getD op []).getD slot 0 with hf
  have hv : splitValues bytecode point = (splitColumns tables).map f := rfl
  have hval : ∀ c ∈ splitColumns tables,
      (((splitColumns tables).idxOf? c).bind ((splitValues bytecode point)[·]?)).getD 0 = f c :=
    fun c hc ↦ hv ▸ valueOf_map hc f
  refine programSide_congr _ (fun t ht ↦ ?_) (fun t ht s hs4 hs ↦ ?_)
  · have hc := count_mem_splitColumns (tl := tables) (t := t) (by rw [nTables_eq_length]; exact ht)
    simp only [Split.ofColumns]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
      Option.getD_some, hval _ hc]
  · have hz := slotWeights_zero tables slot gamma mu etaMem etaBc t s
    have hslots : ((Split.ofColumns tables (splitValues bytecode point)).slots.getD t []).getD s 0 =
        (((splitColumns tables).idxOf? (.slot t s)).bind
          ((splitValues bytecode point)[·]?)).getD 0 := by
      simp [Split.ofColumns, List.getD_eq_getElem?_getD, ht, hs]
    have hpcs : ((Split.ofColumns tables (splitValues bytecode point)).pc.getD t []).getD s 0 =
        (((splitColumns tables).idxOf? (.pc t s)).bind
          ((splitValues bytecode point)[·]?)).getD 0 := by
      simp [Split.ofColumns, List.getD_eq_getElem?_getD, ht, hs]
    rw [hslots, hpcs]
    have hpc : (slotWeights tables slot gamma mu etaMem etaBc |>.pc.getD t []).getD s 0 *
          (((splitColumns tables).idxOf? (.pc t s)).bind
            ((splitValues bytecode point)[·]?)).getD 0 =
        (slotWeights tables slot gamma mu etaMem etaBc |>.pc.getD t []).getD s 0 *
          (split.pc.getD t []).getD s 0 := by
      by_cases hm : SplitColumn.pc t s ∈ splitColumns tables
      · rw [hval _ hm]
      · rw [hz.2 hm, zero_mul, zero_mul]
    by_cases hm : SplitColumn.slot t s ∈ splitColumns tables
    · rw [hval _ hm, hpc]
      exact ⟨rfl, rfl⟩
    · obtain ⟨ho, hfr⟩ := hz.1 (by omega) hm
      rw [ho, hfr, hpc]
      simp only [zero_mul, zero_add, and_self]

end LeanVM.Protocol.Verifier

end
