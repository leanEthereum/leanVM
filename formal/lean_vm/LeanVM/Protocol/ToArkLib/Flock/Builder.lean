/-
  LeanVM.Protocol.ToArkLib.Flock.Builder

  A builder for product-gate circuits: a state monad whose one effect records a gate at the next
  free position, with two compositional contracts for its programs, soundness against a
  specification and well-formedness with an exact gate count. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.Circuit

/-!
# Building product-gate circuits

A gadget is a program in `Builder m`, a state monad over the next free position and the gates
recorded so far. Its one effect, `mul a b`, records the gate `(a, b)` at the next position and
returns that position's form. Linear operations need no effect: they are XORs of forms.

Two contracts compose through `bind`:

* `Sound w mb P`: whenever the gates a run of `mb` records hold at the block `w`, its result
  satisfies `P`. With `Grows` (a program only appends gates), `sound_bind` composes them.
  Gadget specifications are written once against the semantic value of their outputs.
* `Ok S n₀ mb k P`: run from a good state (`Inv S`: the gates recorded so far are bounded from the
  start availability `S.avail`, and exactly `S.avail` and the positions `[S.base, next)` are
  available after them), `mb` keeps the state good, records exactly `k` gates, and returns a
  result satisfying `P` at the new `next`. `ok_bind`, `ok_pure`, `ok_map`, `ok_mul` compose it;
  `Inv.bounded` reads off that the recorded schedule is bounded, without evaluating the circuit.

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

@[expose] public section

namespace ProductCircuit

variable {m : ℕ}

/-! ## The builder -/

/-- The builder's state: the next free position and the gates recorded so far. -/
structure BuildState (m : ℕ) where
  /-- The next gate position. -/
  next : ℕ
  /-- The gates recorded so far, in evaluation order. -/
  gates : Array (Pos m × Gate m)

/-- A circuit-building program. -/
abbrev Builder (m : ℕ) := StateM (BuildState m)

/-- Record the gate `(a, b)` at the next position and return that position's form. -/
def mul (a b : Form m) : Builder m (Form m) :=
  modifyGet fun s ↦
    (Form.var (pos s.next), { next := s.next + 1, gates := s.gates.push (pos s.next, ⟨a, b⟩) })

/-- One `mul`: the gate at `next`, and `next` advanced. -/
theorem run_mul (a b : Form m) (σ : BuildState m) :
    (mul a b).run σ =
      (Form.var (pos σ.next), { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) }) :=
  rfl

private theorem run_bind' {α β : Type} (mb : Builder m α) (f : α → Builder m β) (σ : BuildState m) :
    (mb >>= f).run σ = (f (mb.run σ).1).run (mb.run σ).2 := rfl

private theorem run_map' {α β : Type} (mb : Builder m α) (f : α → β) (σ : BuildState m) :
    (f <$> mb).run σ = (f (mb.run σ).1, (mb.run σ).2) := rfl

/-! ## Soundness -/

/-- Every gate recorded in the state holds at `z`. -/
def GatesHold (σ : BuildState m) (z : Pos m → Bool) : Prop :=
  ∀ kg ∈ σ.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z)

/-- A program only appends gates. -/
def Grows {α : Type} (mb : Builder m α) : Prop :=
  ∀ σ : BuildState m, ∀ kg ∈ σ.gates, kg ∈ (mb.run σ).2.gates

/-- Whenever the gates of a run of `mb` hold at `w`, its result satisfies `P`. -/
def Sound {α : Type} (w : Pos m → Bool) (mb : Builder m α) (P : α → Prop) : Prop :=
  ∀ σ : BuildState m, GatesHold (mb.run σ).2 w → P (mb.run σ).1

theorem grows_bind {α β : Type} {mb : Builder m α} {f : α → Builder m β} (hm : Grows mb)
    (hf : ∀ a, Grows (f a)) : Grows (mb >>= f) := by
  intro σ kg h
  rw [StateT.run_bind]
  exact hf _ _ _ (hm σ kg h)

theorem grows_pure {α : Type} (a : α) : Grows (pure a : Builder m α) := fun _ _ h ↦ h

theorem grows_map {α β : Type} {mb : Builder m α} (f : α → β) (hm : Grows mb) :
    Grows (f <$> mb) := fun σ kg h ↦ by rw [run_map']; exact hm σ kg h

theorem grows_mul (a b : Form m) : Grows (mul a b) := fun σ kg h ↦ by
  rw [run_mul]; exact Array.mem_push_of_mem _ h

theorem sound_bind {α β : Type} {w : Pos m → Bool} {mb : Builder m α} {f : α → Builder m β}
    {P : α → Prop} {Q : β → Prop} (hm : Sound w mb P) (hg : ∀ a, Grows (f a))
    (hf : ∀ a, P a → Sound w (f a) Q) : Sound w (mb >>= f) Q := by
  intro σ h
  rw [StateT.run_bind] at h ⊢
  exact hf _ (hm σ fun kg hkg ↦ h kg (hg _ _ kg hkg)) _ h

theorem sound_pure {α : Type} {w : Pos m → Bool} {a : α} {P : α → Prop} (h : P a) :
    Sound w (pure a : Builder m α) P := fun _ _ ↦ h

theorem sound_map {α β : Type} {w : Pos m → Bool} {mb : Builder m α} {f : α → β}
    {P : α → Prop} {Q : β → Prop} (hm : Sound w mb P) (hf : ∀ a, P a → Q (f a)) :
    Sound w (f <$> mb) Q := fun σ h ↦ by
  rw [run_map'] at h ⊢
  exact hf _ (hm σ h)

/-- The gate `mul` records holds: its result evaluates to the product of its forms. -/
theorem sound_mul {w : Pos m → Bool} (a b : Form m) :
    Sound w (mul a b) (fun o ↦ o.eval w = (a.eval w && b.eval w)) := fun σ h ↦ by
  rw [run_mul] at h ⊢
  rw [eval_var]
  exact h _ (Array.mem_push_self ..)

/-! ## Well-formedness -/

/-- Where a build starts: the positions available before any gate (the inputs and the
constant) and the first gate position, past every available one. -/
structure Start (m : ℕ) where
  /-- The positions available before any gate. -/
  avail : Form m
  /-- The first gate position. -/
  base : ℕ
  /-- No position from `base` on is available at the start. -/
  fresh : ∀ j, base ≤ j → avail.getLsbD j = false

namespace Start

variable (S : Start m)

/-- Position `j` is available once the gates below `n` are recorded. -/
def AvailAt (n j : ℕ) : Bool := S.avail.getLsbD j || (decide (S.base ≤ j) && decide (j < n))

/-- `L` mentions only positions available at `n`. -/
def SubN (L : Form m) (n : ℕ) : Prop := ∀ j, L.getLsbD j = true → S.AvailAt n j = true

/-- A good state: `next` is past the start, the recorded gates are bounded from the start
availability, and after them exactly the start availability and `[base, next)` are
available. -/
structure Inv (σ : BuildState m) : Prop where
  /-- Gate positions start at `base`. -/
  le : S.base ≤ σ.next
  /-- The recorded gates are bounded from the start availability. -/
  bounded : BoundedFrom S.avail σ.gates.toList
  /-- After them, exactly the start availability and `[base, next)` are available. -/
  avail : ∀ j, (availAfter S.avail σ.gates.toList).getLsbD j = S.AvailAt σ.next j

/-- Run from a good state at or after `n₀` with room for `k` gates, `mb` keeps the state good,
records exactly `k` gates, and returns a result satisfying `P` at the new `next`. -/
def Ok {α : Type} (n₀ : ℕ) (mb : Builder m α) (k : ℕ) (P : α → ℕ → Prop) : Prop :=
  ∀ σ : BuildState m, S.Inv σ → n₀ ≤ σ.next → σ.next + k ≤ 2 ^ m →
    S.Inv (mb.run σ).2 ∧ (mb.run σ).2.next = σ.next + k ∧ P (mb.run σ).1 (mb.run σ).2.next

variable {S}

theorem availAt_iff (n j : ℕ) :
    S.AvailAt n j = true ↔ S.avail.getLsbD j = true ∨ (S.base ≤ j ∧ j < n) := by
  simp [AvailAt]

theorem SubN.mono {L : Form m} {n n' : ℕ} (h : S.SubN L n) (hn : n ≤ n') : S.SubN L n' := by
  intro j hj
  rcases (availAt_iff n j).mp (h j hj) with h' | h'
  · exact (availAt_iff n' j).mpr (Or.inl h')
  · exact (availAt_iff n' j).mpr (Or.inr ⟨h'.1, by omega⟩)

theorem SubN.xor {L M : Form m} {n : ℕ} (hL : S.SubN L n) (hM : S.SubN M n) :
    S.SubN (L ^^^ M) n := by
  intro j hj
  rw [BitVec.getLsbD_xor] at hj
  cases hl : L.getLsbD j
  · rw [hl, Bool.false_xor] at hj; exact hM j hj
  · exact hL j hl

theorem subN_zero (n : ℕ) : S.SubN 0 n := by
  intro j hj
  simp at hj

theorem subN_var {k : Pos m} {n : ℕ} (h : S.AvailAt n k = true) : S.SubN (Form.var k) n := by
  intro j hj
  rw [getLsbD_var, decide_eq_true_eq] at hj
  rwa [← hj]

/-- A start position is available at every stage. -/
theorem subN_start {k : Pos m} (h : S.avail.getLsbD k = true) (n : ℕ) :
    S.SubN (Form.var k) n :=
  subN_var ((availAt_iff _ _).mpr (Or.inl h))

theorem sub_of_subN {L a : Form m} {n : ℕ} (ha : ∀ j, a.getLsbD j = S.AvailAt n j)
    (h : S.SubN L n) : Sub L a :=
  sub_iff.mpr fun j hj ↦ (ha j).trans (h j hj)

theorem inv_init : S.Inv ⟨S.base, #[]⟩ where
  le := le_rfl
  bounded := trivial
  avail j := by simp [availAfter, AvailAt]

/-- Recording one gate at `next`, with forms available at `next`, keeps the state good. -/
theorem inv_push {σ : BuildState m} (hσ : S.Inv σ) (hlt : σ.next < 2 ^ m) {a b : Form m}
    (ha : S.SubN a σ.next) (hb : S.SubN b σ.next) :
    S.Inv { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) } where
  le := by dsimp only; have := hσ.le; omega
  bounded := by
    rw [Array.toList_push, boundedFrom_append]
    refine ⟨hσ.bounded, sub_of_subN hσ.avail ha, sub_of_subN hσ.avail hb, ?_, trivial⟩
    rw [hσ.avail, pos_val hlt, Bool.eq_false_iff, ne_eq, availAt_iff]
    have := hσ.le
    have := S.fresh σ.next hσ.le
    simp only [this, Bool.false_eq_true, false_or]
    omega
  avail j := by
    rw [Array.toList_push, availAfter_append_singleton, BitVec.getLsbD_or, hσ.avail,
      getLsbD_var, pos_val hlt, Bool.eq_iff_iff, Bool.or_eq_true, availAt_iff, availAt_iff,
      decide_eq_true_eq]
    have := hσ.le
    dsimp only
    constructor
    · rintro ((h | h) | h) <;> [exact Or.inl h; exact Or.inr ⟨h.1, by omega⟩;
        exact Or.inr ⟨by omega, by omega⟩]
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases hj : j < σ.next
        · exact Or.inl (Or.inr ⟨h.1, hj⟩)
        · exact Or.inr (by omega)

/-- The gate count of a contract, up to equality. -/
theorem Ok.cast {α : Type} {n₀ k k' : ℕ} {mb : Builder m α} {P : α → ℕ → Prop}
    (h : S.Ok n₀ mb k P) (hk : k = k') : S.Ok n₀ mb k' P := hk ▸ h

theorem ok_bind {α β : Type} {n₀ k₁ k : ℕ} {mb : Builder m α} {f : α → Builder m β}
    {P : α → ℕ → Prop} {Q : β → ℕ → Prop} (hm : S.Ok n₀ mb k₁ P) (hk : k₁ ≤ k)
    (hf : ∀ a n, n₀ ≤ n → P a n → S.Ok n (f a) (k - k₁) Q) : S.Ok n₀ (mb >>= f) k Q := by
  intro σ hσ hn hle
  obtain ⟨h1, h2, h3⟩ := hm σ hσ hn (by omega)
  rw [run_bind']
  obtain ⟨h1', h2', h3'⟩ := hf _ _ (by omega) h3 _ h1 le_rfl (by omega)
  exact ⟨h1', by omega, h3'⟩

theorem ok_pure {α : Type} {n₀ k : ℕ} {a : α} {P : α → ℕ → Prop} (h : ∀ n, n₀ ≤ n → P a n)
    (hk : k = 0) : S.Ok n₀ (pure a : Builder m α) k P := by
  intro σ hσ hn _
  subst hk
  exact ⟨hσ, rfl, h _ hn⟩

theorem ok_map {α β : Type} {n₀ k : ℕ} {mb : Builder m α} {f : α → β} {P : α → ℕ → Prop}
    {Q : β → ℕ → Prop} (hm : S.Ok n₀ mb k P) (hf : ∀ a n, n₀ ≤ n → P a n → Q (f a) n) :
    S.Ok n₀ (f <$> mb) k Q := by
  intro σ hσ hn hle
  obtain ⟨h1, h2, h3⟩ := hm σ hσ hn hle
  rw [run_map']
  exact ⟨h1, h2, hf _ (mb.run σ).2.next (by omega) h3⟩

/-- `mul` records one gate, and its result is available after it. -/
theorem ok_mul {n₀ : ℕ} {a b : Form m} (ha : S.SubN a n₀) (hb : S.SubN b n₀) :
    S.Ok n₀ (mul a b) 1 (fun o n ↦ S.SubN o n) := by
  intro σ hσ hn hle
  rw [run_mul]
  refine ⟨inv_push hσ (by omega) (ha.mono hn) (hb.mono hn), rfl, subN_var ?_⟩
  rw [pos_val (by omega), availAt_iff]
  have := hσ.le
  dsimp only
  omega

/-- The schedule of a good state is bounded from the start availability. -/
theorem Inv.boundedFrom {σ : BuildState m} (h : S.Inv σ) : BoundedFrom S.avail σ.gates.toList :=
  h.bounded

/-- A circuit whose gates are those of a run from `base`, for a program with the contract, and
whose inputs and constant are the start availability, is bounded. -/
theorem bounded_of_ok {α : Type} {c : ProductCircuit m} {mb : Builder m α} {k : ℕ}
    {P : α → ℕ → Prop} (hav : c.inputs ||| Form.var c.cpos = S.avail) (h : S.Ok S.base mb k P)
    (hk : S.base + k ≤ 2 ^ m) (hg : c.gates = (mb.run ⟨S.base, #[]⟩).2.gates) : c.Bounded := by
  rw [Bounded, hav, hg]
  exact (h _ inv_init le_rfl hk).1.bounded

end Start

end ProductCircuit

end
end LeanVM.Protocol
