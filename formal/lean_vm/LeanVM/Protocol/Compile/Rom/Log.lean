/-
  LeanVM.Protocol.Compile.Rom.Log

  The random oracle's ordered log as the random-oracle theorem reads it: lookups, the seeding
  description, the failure event (a fresh answer that collides or predicts a digest the log
  already refers to), the bound on the number of failing answers, and the order facts that
  hold in a log without failure.
-/

module

public import LeanVM.Protocol.Compile.Rom.Encoding
public import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle

/-!
# Logs and failure

A log is the ordered list of the fresh queries to the random oracle `H : Bytes → Digest` with
their answers (`LeanVM.Protocol.Rom.loggedRO`). The random-oracle theorem reads the compiled
verifier's computation back out of a log; that reading is sound only if no answer was guessed
before it was drawn. This module defines that condition.

## Failure

A fresh answer `u` at the input `t`, appended to the log `ℓ`, *fails* (`BadEntry`) if

* `u` is the output of an entry of `ℓ` (a collision);
* `u` is a 32-byte chunk at offset `0` or `32` of `t` or of an input of `ℓ` (a prediction: chain
  inputs carry their state at offset `0`, Merkle node inputs their children at `0` and `32`,
  proof-of-work inputs their base at `0`);
* `u` is the root two absorbed scalars encode (`RootOf`): an input `cv ‖ (x₁, 1)` of `t :: ℓ`
  whose state `cv` is the output of an entry of `ℓ` with input `_ ‖ (x₀, 1)`, the root being
  `digestOfScalars (x₀, x₁)`;
* `u` would make an input of `t :: ℓ` a later step of the seeding (`Seed.input a u`).

`Fail ℓ` holds if some entry of `ℓ` fails with respect to the entries before it.

## The count

At most `(4 + k) · (|ℓ| + 1)` answers fail (`sum_badEntry_le`), `k` the number of seeding steps:
`|ℓ|` collisions, and, for each of the `|ℓ| + 1` inputs, two chunks, one root and one seeding
predecessor per step. Every exclusion is a single digest because the encodings are injective
(`LeanVM.Protocol.Compile.Rom.Encoding`).

## Order

In a log without failure, an entry whose output is a chunk, a root, or a seeding predecessor of
an entry's input comes before that entry (`lt_of_chunk`, `lt_of_rootOf`, `lt_of_seedInput`),
and outputs are distinct (`output_ne`).

## The seeding

leanVM's seed is `H(H(ivpre) ‖ pi)`, where `ivpre` holds `H(bytecode)` between fixed bytes. The
seeding is described by a first input and a list of steps, each step's input being fixed bytes,
the previous digest, and fixed bytes (`Seed`). The affixes make each step injective, which the
count needs. The theorem takes a family of seedings (`Seeds`), one per statement: the adversary
chooses the statement. The failure condition reads only the steps common to the family
(`Seeds.steps`); a step with an empty prefix is covered by the chunk condition.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/-! ## Logs -/

/-- The random oracle's log: the fresh queries in order, with their answers. -/
abbrev Log : Type := List (Bytes × Digest)

/-- The answer a log gives (its first entry with the input). -/
abbrev look (ℓ : Log) : Bytes → Option Digest := logLookup ℓ

/-- The first 32 bytes of an input. -/
def chunk0 (x : Bytes) : Bytes := x.take 32

/-- Bytes `32..64` of an input. -/
def chunk1 (x : Bytes) : Bytes := (x.drop 32).take 32

theorem chunk0_append (c : Digest) (b : Bytes) : chunk0 (digestBytes c ++ b) = digestBytes c := by
  simp [chunk0, digestBytes_length]

theorem chunk1_append (c c' : Digest) :
    chunk1 (digestBytes c ++ digestBytes c') = digestBytes c' := by
  simp [chunk1, digestBytes_length]

/-! ## The seeding -/

/-- The seeding: the first input, then steps, each hashing fixed bytes, the previous digest and
fixed bytes. The seed is the last digest. -/
structure Seed where
  /-- The first input. -/
  first : Bytes
  /-- The steps, each a prefix and a suffix around the previous digest. -/
  steps : List (Bytes × Bytes)

/-- The input of a seeding step at the previous digest `d`. -/
def Seed.input (a : Bytes × Bytes) (d : Digest) : Bytes := a.1 ++ digestBytes d ++ a.2

theorem Seed.input_injective (a : Bytes × Bytes) : Function.Injective (Seed.input a) := by
  intro d d' h
  simp only [Seed.input, List.append_assoc, List.append_cancel_left_eq] at h
  exact digestBytes_injective (List.append_inj h (by rw [digestBytes_length,
    digestBytes_length])).1

/-- The seed, computed with a hash function in any monad. -/
def Seed.run {m : Type → Type} [Monad m] (H : Bytes → m Digest) (σ : Seed) : m Digest := do
  let d ← H σ.first
  σ.steps.foldlM (fun d a ↦ H (Seed.input a d)) d

/-- The first input of the remaining seeding steps from `d` that the answers `H` do not answer,
and whether it is the last step; `none` if all are answered. -/
def goPend (H : Bytes → Option Digest) : List (Bytes × Bytes) → Digest → Option (Bytes × Bool)
  | [], _ => none
  | a :: as, d => match H (Seed.input a d) with
    | none => some (Seed.input a d, as.isEmpty)
    | some d' => goPend H as d'

/-- The first input of the seeding that the answers `H` do not answer, and whether it is the
last; `none` once the seed is answered. -/
def pend (H : Bytes → Option Digest) (σ : Seed) : Option (Bytes × Bool) :=
  match H σ.first with
  | none => some (σ.first, σ.steps.isEmpty)
  | some d => goPend H σ.steps d

/-- **A family of seedings**, one per statement `x : X`: the seeding `seed x`, and the history
`root x` of the verifier program at which its seed puts the chain. Every step with a nonempty
prefix is among `steps`; the last step of each seeding is the previous digest followed by 32
bytes, the only seeding input with the 64 bytes of a chain input; and the last input of a
seeding, computed through answers without collisions, names its statement. -/
structure Seeds (X : Type) where
  /-- The seeding of a statement. -/
  seed : X → Seed
  /-- The history at which the seed puts the program. -/
  root : X → List Ev
  /-- The seeding steps with a nonempty prefix. -/
  steps : List (Bytes × Bytes)
  /-- Every step is among `steps` or has an empty prefix. -/
  steps_mem : ∀ x, ∀ a ∈ (seed x).steps, a ∈ steps ∨ a.1 = []
  /-- The last step is the previous digest followed by 32 bytes. -/
  last : ∀ x, ∃ s : Bytes, s.length = 32 ∧ (seed x).steps.getLast? = some ([], s)
  /-- The first input is not 64 bytes long. -/
  first_len : ∀ x, (seed x).first.length ≠ 64
  /-- No other step's input is 64 bytes long. -/
  mid_len : ∀ x, ∀ a ∈ (seed x).steps.dropLast, ∀ d, (Seed.input a d).length ≠ 64
  /-- The last input names the statement, for answers without collisions. -/
  inj : ∀ H : Bytes → Option Digest, (∀ a b v, H a = some v → H b = some v → a = b) →
    ∀ x x' t, pend H (seed x) = some (t, true) → pend H (seed x') = some (t, true) → x = x'

/-! ## Failure -/

/-- The root that the input `x` completes in `ℓ`: `x = cv ‖ (x₁, 1)` with `cv` the output of the
first entry of `ℓ` producing it, that entry's input ending in `(x₀, 1)`, and the root the
digest `(x₀, x₁)` encodes. -/
def RootOf (ℓ : Log) (x : Bytes) (r : Digest) : Prop :=
  ∃ (c : Digest) (x₀ x₁ : E) (e : Bytes × Digest), x = digestBytes c ++ blockOf x₁ 1 ∧
    ℓ.find? (fun e ↦ decide (e.2 = c)) = some e ∧ e.1.drop 32 = blockOf x₀ 1 ∧
    digestOfScalars (x₀, x₁) = some r

/-- A fresh answer `u` at `t` appended to `ℓ` fails: it collides with an output of `ℓ`, or is a
chunk, a root, or a seeding predecessor of `t` or of an input of `ℓ`. -/
def BadEntry {X : Type} (σ : Seeds X) (ℓ : Log) (t : Bytes) (u : Digest) : Prop :=
  (∃ e ∈ ℓ, e.2 = u) ∨
    ∃ x ∈ t :: ℓ.map Prod.fst, chunk0 x = digestBytes u ∨ chunk1 x = digestBytes u ∨
      RootOf ℓ x u ∨ ∃ a ∈ σ.steps, x = Seed.input a u

/-- Some entry of the log failed with respect to the entries before it. -/
def Fail {X : Type} (σ : Seeds X) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length), BadEntry σ (ℓ.take i) ℓ[i].1 ℓ[i].2

theorem not_fail_nil {X : Type} (σ : Seeds X) : ¬ Fail σ [] := fun ⟨_, hi, _⟩ ↦ by simp at hi

/-- The log with one more entry fails exactly if the log fails or the entry does. -/
theorem fail_append {X : Type} (σ : Seeds X) (ℓ : Log) (t : Bytes) (u : Digest) :
    Fail σ (ℓ ++ [(t, u)]) ↔ Fail σ ℓ ∨ BadEntry σ ℓ t u := by
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · left
      refine ⟨i, hi', ?_⟩
      rwa [List.getElem_append_left hi', List.take_append_of_le_length hi'.le] at h
    · right
      simpa using h
  · rintro (⟨i, hi, h⟩ | h)
    · refine ⟨i, by simp; omega, ?_⟩
      rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le]
    · exact ⟨ℓ.length, by simp, by simpa using h⟩

/-- A prefix of a log without failure has no failure. -/
theorem not_fail_take {X : Type} {σ : Seeds X} {ℓ : Log} (h : ¬ Fail σ ℓ) (n : ℕ) :
    ¬ Fail σ (ℓ.take n) := by
  rintro ⟨i, hi, hb⟩
  simp only [List.length_take] at hi
  refine h ⟨i, by omega, ?_⟩
  rwa [List.take_take, min_eq_left (by omega), List.getElem_take] at hb

/-! ## The count of failing answers -/

section Count

open Classical in
/-- The indicator of a predicate, in `ℝ≥0∞`. -/
noncomputable def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  unfold ind; split <;> simp

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by simp [ind, h]

theorem ind_of_not {p : Prop} (h : ¬ p) : ind p = 0 := by simp [ind, h]

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_of hp, ind_of (h hp)]
  · rw [ind_of_not hp]; exact bot_le

/-- A predicate with at most one witness has indicator sum at most one. -/
theorem sum_ind_le_one {γ : Type} [Fintype γ] {p : γ → Prop}
    (h : ∀ u u', p u → p u' → u = u') :
    ∑ u, ind (p u) ≤ 1 := by
  classical
  have : ∑ u, ind (p u) = ((Finset.univ.filter p).card : ℝ≥0∞) := by
    simp only [ind]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [this]
  exact_mod_cast Finset.card_le_one.mpr fun a ha b hb ↦
    h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

/-- Sums over digests commute with sums over a list. -/
theorem sum_list_sum_comm {β γ : Type} [Fintype γ] (L : List β) (f : β → γ → ℝ≥0∞) :
    ∑ u, (L.map fun x ↦ f x u).sum = (L.map fun x ↦ ∑ u, f x u).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- A list sum of terms bounded by `c`. -/
theorem list_sum_le {β : Type} (L : List β) (f : β → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ x ∈ L, f x ≤ c) :
    (L.map f).sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, add_mul, one_mul]
    rw [add_comm (L.length * c : ℝ≥0∞)]
    exact add_le_add (h x (by simp)) (ih fun y hy ↦ h y (by simp [hy]))

/-- An indicator of an existential over a list is at most the list sum of the indicators. -/
theorem ind_exists_le {β : Type} (L : List β) (q : β → Prop) :
    ind (∃ x ∈ L, q x) ≤ (L.map fun x ↦ ind (q x)).sum := by
  by_cases h : ∃ x ∈ L, q x
  · obtain ⟨x, hx, hq⟩ := h
    rw [ind_of ⟨x, hx, hq⟩]
    calc (1 : ℝ≥0∞) = ind (q x) := (ind_of hq).symm
      _ ≤ _ := List.single_le_sum (fun _ _ ↦ bot_le) _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · rw [ind_of_not h]; exact bot_le

theorem ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases hp : p
  · rw [ind_of (Or.inl hp), ind_of hp]; exact le_self_add
  · by_cases hq : q
    · rw [ind_of (Or.inr hq), ind_of hq]; exact le_add_self
    · rw [ind_of_not (by tauto)]; exact bot_le

/-- A root is determined by the input that completes it. -/
theorem rootOf_unique {ℓ : Log} {x : Bytes} {r r' : Digest} (h : RootOf ℓ x r)
    (h' : RootOf ℓ x r') : r = r' := by
  obtain ⟨c, x₀, x₁, e, hx, hf, he, hr⟩ := h
  obtain ⟨c', x₀', x₁', e', hx', hf', he', hr'⟩ := h'
  obtain ⟨rfl, rfl, -⟩ := chainInput_inj (hx.symm.trans hx')
  rw [hf] at hf'
  cases hf'
  obtain ⟨rfl, -⟩ := blockOf_inj (he.symm.trans he')
  rw [hr] at hr'
  exact Option.some.inj hr'

/-- **The count of failing answers**: at most `(4 + k) · (|ℓ| + 1)` digests fail at a fresh
input, `k` the number of seeding steps. -/
theorem sum_badEntry_le {X : Type} (σ : Seeds X) (ℓ : Log) (t : Bytes) :
    ∑ u, ind (BadEntry σ ℓ t u) ≤ ((4 + σ.steps.length) * (ℓ.length + 1) : ℕ) := by
  set L := t :: ℓ.map Prod.fst
  let g : Bytes → Digest → ℝ≥0∞ := fun x u ↦ ind (chunk0 x = digestBytes u) +
    ind (chunk1 x = digestBytes u) + ind (RootOf ℓ x u) +
    (σ.steps.map fun a ↦ ind (x = Seed.input a u)).sum
  have hpt : ∀ u, ind (BadEntry σ ℓ t u) ≤
      (ℓ.map fun e ↦ ind (e.2 = u)).sum + (L.map fun x ↦ g x u).sum := by
    intro u
    refine (ind_or_le _ _).trans (add_le_add (ind_exists_le _ _) ?_)
    refine (ind_exists_le _ _).trans (le_of_eq_of_le rfl ?_)
    refine List.sum_le_sum fun x _ ↦ ?_
    refine (ind_or_le _ _).trans ?_
    simp only [g, add_assoc]
    refine add_le_add le_rfl ((ind_or_le _ _).trans (add_le_add le_rfl ?_))
    exact (ind_or_le _ _).trans (add_le_add le_rfl (ind_exists_le _ _))
  have h1 : ∀ e ∈ ℓ, ∑ u, ind (e.2 = u) ≤ 1 := fun e _ ↦
    sum_ind_le_one fun u u' hu hu' ↦ hu.symm.trans hu'
  have h2 : ∀ x ∈ L, ∑ u, g x u ≤ (3 + σ.steps.length : ℕ) := by
    intro x _
    simp only [g, Finset.sum_add_distrib]
    rw [sum_list_sum_comm]
    have hc0 : ∑ u, ind (chunk0 x = digestBytes u) ≤ 1 :=
      sum_ind_le_one fun u u' hu hu' ↦ digestBytes_injective (hu.symm.trans hu')
    have hc1 : ∑ u, ind (chunk1 x = digestBytes u) ≤ 1 :=
      sum_ind_le_one fun u u' hu hu' ↦ digestBytes_injective (hu.symm.trans hu')
    have hr : ∑ u, ind (RootOf ℓ x u) ≤ 1 :=
      sum_ind_le_one fun u u' hu hu' ↦ rootOf_unique hu hu'
    have hs := list_sum_le σ.steps (fun a ↦ ∑ u, ind (x = Seed.input a u)) 1 fun a _ ↦
      sum_ind_le_one fun u u' hu hu' ↦ Seed.input_injective a (hu.symm.trans hu')
    rw [mul_one] at hs
    calc _ ≤ 1 + 1 + 1 + (σ.steps.length : ℝ≥0∞) := by gcongr
      _ = _ := by push_cast; ring
  calc ∑ u, ind (BadEntry σ ℓ t u)
      ≤ ∑ u, ((ℓ.map fun e ↦ ind (e.2 = u)).sum + (L.map fun x ↦ g x u).sum) :=
        Finset.sum_le_sum fun u _ ↦ hpt u
    _ = (ℓ.map fun e ↦ ∑ u, ind (e.2 = u)).sum + (L.map fun x ↦ ∑ u, g x u).sum := by
        rw [Finset.sum_add_distrib, sum_list_sum_comm, sum_list_sum_comm]
    _ ≤ ℓ.length * 1 + L.length * ((3 + σ.steps.length : ℕ) : ℝ≥0∞) :=
        add_le_add (list_sum_le _ _ _ h1) (list_sum_le _ _ _ h2)
    _ ≤ _ := by
        simp only [L, List.length_cons, List.length_map, mul_one]
        push_cast
        have : (ℓ.length : ℝ≥0∞) ≤ ℓ.length + 1 := le_self_add
        calc (ℓ.length : ℝ≥0∞) + (ℓ.length + 1) * (3 + σ.steps.length)
            ≤ (ℓ.length + 1) + (ℓ.length + 1) * (3 + σ.steps.length) := by gcongr
          _ = _ := by ring

end Count

/-! ## Lookups -/

theorem look_append_of_some {ℓ : Log} {x : Bytes} {v : Digest} (h : look ℓ x = some v)
    (ℓ' : Log) : look (ℓ ++ ℓ') x = some v := by
  induction ℓ with
  | nil => simp at h
  | cons e ℓ ih =>
    simp only [look, logLookup_cons] at h ⊢
    simp only [List.cons_append, logLookup_cons]
    split
    · simp_all
    · simp_all

/-- A lookup in a prefix is a lookup in the log. -/
theorem look_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {x : Bytes} {v : Digest}
    (h : look ℓ x = some v) : look ℓ' x = some v := by
  obtain ⟨r, rfl⟩ := hp
  exact look_append_of_some h r

/-- A lookup is the first entry with the input. -/
theorem look_eq_some_iff (ℓ : Log) (x : Bytes) (v : Digest) :
    look ℓ x = some v ↔
      ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i] = (x, v) ∧ look (ℓ.take i) x = none := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    simp only [look, logLookup_cons] at ih ⊢
    by_cases he : e.1 = x
    · simp only [he, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, by simp [← he], by simp⟩
      · rintro ⟨i, hi, hei, hn⟩
        cases i with
        | zero => simp at hei; subst hei; rfl
        | succ i => simp [logLookup_cons, he] at hn
    · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h he), ih]
      constructor
      · rintro ⟨i, hi, hei, hn⟩
        exact ⟨i + 1, by simpa using hi, by simpa using hei, by simp [logLookup_cons, he, hn]⟩
      · rintro ⟨i, hi, hei, hn⟩
        cases i with
        | zero => simp at hei; exact absurd (by rw [hei]) he
        | succ i =>
          refine ⟨i, by simpa using hi, by simpa using hei, ?_⟩
          simpa [logLookup_cons, he] using hn

/-- An entry is found by a lookup in every prefix that contains it, if no earlier entry has its
input. -/
theorem look_take_of_first {ℓ : Log} {i : ℕ} (hi : i < ℓ.length) {x : Bytes} {v : Digest}
    (hei : ℓ[i] = (x, v)) (hn : look (ℓ.take i) x = none) {m : ℕ} (hm : i < m) :
    look (ℓ.take m) x = some v := by
  rw [look_eq_some_iff]
  exact ⟨i, by simp; omega, by simpa using hei, by rwa [List.take_take, min_eq_left hm.le]⟩

/-- An entry of a log is answered by the log (perhaps by an earlier entry). -/
theorem look_ne_none_of_mem {ℓ : Log} {e : Bytes × Digest} (he : e ∈ ℓ) : look ℓ e.1 ≠ none := by
  rw [Ne, look, logLookup_eq_none_iff]
  exact fun h ↦ h (List.mem_map.mpr ⟨e, he, rfl⟩)

/-! ## Order facts without failure -/

section Order

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- Without failure, outputs are distinct. -/
theorem output_ne (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    (hij : i < j) : ℓ[i].2 ≠ ℓ[j].2 := by
  intro heq
  refine h ⟨j, hj, Or.inl ⟨ℓ[i], ?_, heq⟩⟩
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

/-- Without failure, two entries with one output are one entry. -/
theorem index_eq_of_output (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    (heq : ℓ[i].2 = ℓ[j].2) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd heq (output_ne h hi hj hij)
  · rfl
  · exact absurd heq.symm (output_ne h hj hi hij)

/-- The inputs of the entries up to `i` are those the failure condition of entry `i` reads. -/
theorem mem_inputs_of_le {i j : ℕ} (hi : i < ℓ.length) (hji : j ≤ i) :
    ℓ[j].1 ∈ ℓ[i].1 :: (ℓ.take i).map Prod.fst := by
  rcases Nat.lt_or_eq_of_le hji with hlt | rfl
  · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ℓ[j], ?_, rfl⟩)
    exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩
  · exact List.mem_cons_self

/-- Without failure, an entry whose output is a chunk of an entry's input comes before it. -/
theorem lt_of_chunk (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    (hc : chunk0 ℓ[j].1 = digestBytes ℓ[i].2 ∨ chunk1 ℓ[j].1 = digestBytes ℓ[i].2) : i < j := by
  by_contra hji
  refine h ⟨i, hi, Or.inr ⟨ℓ[j].1, mem_inputs_of_le hi (by omega), ?_⟩⟩
  rcases hc with hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)

/-- Without failure, an entry whose output is a seeding successor's predecessor comes before
it. -/
theorem lt_of_seedInput (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    {a : Bytes × Bytes} (ha : a ∈ σ.steps) (hc : ℓ[j].1 = Seed.input a ℓ[i].2) : i < j := by
  by_contra hji
  exact h ⟨i, hi, Or.inr ⟨ℓ[j].1, mem_inputs_of_le hi (by omega),
    Or.inr (Or.inr (Or.inr ⟨a, ha, hc⟩))⟩⟩

/-- Without failure, an entry whose output is the root an entry's input completes comes before
it. The root is read in the entries before the later of the two. -/
theorem lt_of_rootOf (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    (hr : RootOf (ℓ.take j) ℓ[j].1 ℓ[i].2) : i < j := by
  by_contra hji
  refine h ⟨i, hi, Or.inr ⟨ℓ[j].1, mem_inputs_of_le hi (by omega), Or.inr (Or.inr (Or.inl ?_))⟩⟩
  obtain ⟨c, x₀, x₁, e, hx, hf, he, hro⟩ := hr
  refine ⟨c, x₀, x₁, e, hx, ?_, he, hro⟩
  obtain ⟨n, rfl⟩ : ∃ n, i = j + n := ⟨i - j, by omega⟩
  rw [← List.take_append_drop j (ℓ.take (j + n)), List.find?_append, List.take_take,
    min_eq_left (by omega), hf]
  rfl

end Order

end
end LeanVM.Protocol.Compile.Rom
