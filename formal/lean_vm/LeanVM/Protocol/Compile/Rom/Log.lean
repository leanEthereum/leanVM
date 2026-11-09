/-
  LeanVM.Protocol.Compile.Rom.Log

  The random oracles' ordered log as the random-oracle theorem reads it: lookups, the seeding
  description, the failure event (a fresh answer that collides with or predicts a value the log
  already refers to), the bound on the number of failing answers, and the order facts that hold
  in a log without failure.
-/

module

public import LeanVM.Protocol.Compile.Rom.Encoding
public import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle

/-!
# Logs and failure

A log is the ordered list of the fresh queries to the two random oracles, the hash
`H : Bytes → Digest` and the permutation `F : KState → KState`, with their answers
(`LeanVM.Protocol.Rom.loggedRO`). The random-oracle theorem reads the compiled verifier's
computation back out of a log; that reading is sound only if no answer was guessed before it was
drawn. This module defines that condition.

## Failure

A fresh hash answer `u` at the input `x`, appended to the log `ℓ`, *fails* (`BadH`) if

* `u` is the output of a hash entry of `ℓ` (a collision);
* `u` is the 32-byte chunk at offset `0`, `32` or one of the seeding offsets `σ.offs` of `x` or
  of a hash input of `ℓ` (a prediction: Merkle node inputs carry their children at `0` and `32`,
  the IV's preimage the relation's and the bytecode's digests);
* `u` is a root a permutation input of `ℓ` absorbs (`RootOf`): two adjacent waiting scalars with
  tag `1` that encode it, or the last waiting scalar of the input that produced the state (the
  first permutation entry whose output has the input's capacity, `predIn`) and the first one of
  this input, a root straddling a forced permutation;
* `u` is the IV a permutation input of `ℓ` carries in its first four lanes (`laneDigest`).

A fresh permutation answer `u` at the input `s` *fails* (`BadF`) if its capacity, lanes
`16..25` (`capOf`), is the capacity of an output of `ℓ` (a collision of chaining values), or of
`s` or an input of `ℓ` (a prediction: a permutation input carries the capacity of the state it
continues), or zero (the capacity of the seed's input).

`Fail ℓ` holds if some entry of `ℓ` fails with respect to the entries before it.

## The count

At most `(5 + |σ.offs|) · (|ℓ| + 1)` hash answers fail (`sum_badH_le`), and each of at most
`2|ℓ| + 2` capacities excludes a `2^-576 ≤ 2^-256` fraction of the permutation's answers
(`sum_badF_div_le`).

## Order

In a log without failure, an entry whose output a later input refers to comes before it
(`lt_of_chunk`, `lt_of_cap`, `lt_of_rootOf`, `lt_of_laneDigest`), hash outputs are distinct
(`hOut_ne`), and so are the capacities of permutation outputs (`fCap_ne`), none of them zero.

## The seeding

leanVM's seed is `F(seedInput(H(tag ‖ bytecode), pi))`. A seeding (`Seed`) is
a list of hash steps, each input a function of the answers before it, then one permutation step
whose input is a function of all of them. The theorem takes a family of seedings (`Seeds`), one
per statement: the adversary chooses the statement. Every hash answer of a seeding is referred to
by a later step, at a byte offset among `σ.offs`, or by the permutation input's first four lanes
(`Seeds.refs`); the permutation inputs have zero capacity (`Seeds.cap0`); and the permutation
input names its statement for answers without collisions (`Seeds.inj`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Logs -/

/-- An entry of the log: a hash query or a permutation query, with its answer. -/
abbrev Entry : Type := LogEntry Bytes Digest KeccakState KeccakState

/-- The oracles' log: the fresh queries in order, with their answers. -/
abbrev Log : Type := List Entry

/-- The hash answer a log gives (its first hash entry with the input). -/
abbrev lookH (ℓ : Log) : Bytes → Option Digest := lookL ℓ

/-- The permutation answer a log gives (its first permutation entry with the input). -/
abbrev lookF (ℓ : Log) : KeccakState → Option KeccakState := lookR ℓ

/-- The hash inputs of a log. -/
def hIns (ℓ : Log) : List Bytes := (leftOf ℓ).map Prod.fst

/-- The hash outputs of a log. -/
def hOuts (ℓ : Log) : List Digest := (leftOf ℓ).map Prod.snd

/-- The permutation inputs of a log. -/
def fIns (ℓ : Log) : List KeccakState := (rightOf ℓ).map Prod.fst

/-- The permutation outputs of a log. -/
def fOuts (ℓ : Log) : List KeccakState := (rightOf ℓ).map Prod.snd

theorem length_leftOf_add_rightOf : ∀ ℓ : Log, (leftOf ℓ).length + (rightOf ℓ).length = ℓ.length
  | [] => rfl
  | .inl _ :: ℓ => by
    have := length_leftOf_add_rightOf ℓ
    simp only [leftOf, rightOf, List.filterMap_cons, List.length_cons] at this ⊢
    omega
  | .inr _ :: ℓ => by
    have := length_leftOf_add_rightOf ℓ
    simp only [leftOf, rightOf, List.filterMap_cons, List.length_cons] at this ⊢
    omega

theorem lookH_cons_inl (x : Bytes) (u : Digest) (ℓ : Log) (y : Bytes) :
    lookH (.inl (x, u) :: ℓ) y = if x = y then some u else lookH ℓ y := rfl

theorem lookH_cons_inr (p : KeccakState × KeccakState) (ℓ : Log) (y : Bytes) :
    lookH (.inr p :: ℓ) y = lookH ℓ y := rfl

theorem lookF_cons_inl (p : Bytes × Digest) (ℓ : Log) (s : KeccakState) :
    lookF (.inl p :: ℓ) s = lookF ℓ s := rfl

theorem lookF_cons_inr (s : KeccakState) (u : KeccakState) (ℓ : Log) (s' : KeccakState) :
    lookF (.inr (s, u) :: ℓ) s' = if s = s' then some u else lookF ℓ s' := rfl

/-- A hash lookup is the first hash entry with the input. -/
theorem lookH_eq_some_iff (ℓ : Log) (x : Bytes) (v : Digest) :
    lookH ℓ x = some v ↔
      ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i] = .inl (x, v) ∧ lookH (ℓ.take i) x = none := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    rcases e with ⟨y, u⟩ | p
    · rw [lookH_cons_inl]
      by_cases he : y = x
      · subst he
        simp only [↓reduceIte, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨0, by simp, by simp, by simp⟩
        · rintro ⟨i, hi, hei, hn⟩
          cases i with
          | zero => simp at hei; exact hei
          | succ i => simp [lookH_cons_inl] at hn
      · simp only [he, ↓reduceIte]
        rw [ih]
        constructor
        · rintro ⟨i, hi, hei, hn⟩
          exact ⟨i + 1, by simpa using hi, by simpa using hei, by
            simp [lookH_cons_inl, he, hn]⟩
        · rintro ⟨i, hi, hei, hn⟩
          cases i with
          | zero => simp at hei; exact absurd hei.1 he
          | succ i =>
            refine ⟨i, by simpa using hi, by simpa using hei, ?_⟩
            simpa [lookH_cons_inl, he] using hn
    · rw [lookH_cons_inr, ih]
      constructor
      · rintro ⟨i, hi, hei, hn⟩
        exact ⟨i + 1, by simpa using hi, by simpa using hei, by simp [lookH_cons_inr, hn]⟩
      · rintro ⟨i, hi, hei, hn⟩
        cases i with
        | zero => simp at hei
        | succ i =>
          exact ⟨i, by simpa using hi, by simpa using hei, by
            simpa [lookH_cons_inr] using hn⟩

/-- A permutation lookup is the first permutation entry with the input. -/
theorem lookF_eq_some_iff (ℓ : Log) (s v : KeccakState) :
    lookF ℓ s = some v ↔
      ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i] = .inr (s, v) ∧ lookF (ℓ.take i) s = none := by
  induction ℓ with
  | nil => simp
  | cons e ℓ ih =>
    rcases e with p | ⟨y, u⟩
    · rw [lookF_cons_inl, ih]
      constructor
      · rintro ⟨i, hi, hei, hn⟩
        exact ⟨i + 1, by simpa using hi, by simpa using hei, by simp [lookF_cons_inl, hn]⟩
      · rintro ⟨i, hi, hei, hn⟩
        cases i with
        | zero => simp at hei
        | succ i =>
          exact ⟨i, by simpa using hi, by simpa using hei, by
            simpa [lookF_cons_inl] using hn⟩
    · rw [lookF_cons_inr]
      by_cases he : y = s
      · subst he
        simp only [↓reduceIte, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨0, by simp, by simp, by simp⟩
        · rintro ⟨i, hi, hei, hn⟩
          cases i with
          | zero => simp at hei; exact hei
          | succ i => simp [lookF_cons_inr] at hn
      · simp only [he, ↓reduceIte]
        rw [ih]
        constructor
        · rintro ⟨i, hi, hei, hn⟩
          exact ⟨i + 1, by simpa using hi, by simpa using hei, by
            simp [lookF_cons_inr, he, hn]⟩
        · rintro ⟨i, hi, hei, hn⟩
          cases i with
          | zero => simp at hei; exact absurd hei.1 he
          | succ i =>
            refine ⟨i, by simpa using hi, by simpa using hei, ?_⟩
            simpa [lookF_cons_inr, he] using hn

theorem lookH_append_of_some {ℓ : Log} {x : Bytes} {v : Digest} (h : lookH ℓ x = some v)
    (ℓ' : Log) : lookH (ℓ ++ ℓ') x = some v := by
  have h' : lookL ℓ x = some v := h
  show lookL (ℓ ++ ℓ') x = some v
  rw [lookL_append, h', Option.some_or]

theorem lookF_append_of_some {ℓ : Log} {s v : KeccakState} (h : lookF ℓ s = some v)
    (ℓ' : Log) : lookF (ℓ ++ ℓ') s = some v := by
  have h' : lookR ℓ s = some v := h
  show lookR (ℓ ++ ℓ') s = some v
  rw [lookR_append, h', Option.some_or]

/-- A hash lookup in a prefix is a lookup in the log. -/
theorem lookH_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {x : Bytes} {v : Digest}
    (h : lookH ℓ x = some v) : lookH ℓ' x = some v := by
  obtain ⟨r, rfl⟩ := hp
  exact lookH_append_of_some h r

/-- A permutation lookup in a prefix is a lookup in the log. -/
theorem lookF_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {s v : KeccakState}
    (h : lookF ℓ s = some v) : lookF ℓ' s = some v := by
  obtain ⟨r, rfl⟩ := hp
  exact lookF_append_of_some h r

/-- An entry is found by a hash lookup in every prefix that contains it, if no earlier entry has
its input. -/
theorem lookH_take_of_first {ℓ : Log} {i : ℕ} (hi : i < ℓ.length) {x : Bytes} {v : Digest}
    (hei : ℓ[i] = .inl (x, v)) (hn : lookH (ℓ.take i) x = none) {m : ℕ} (hm : i < m) :
    lookH (ℓ.take m) x = some v := by
  rw [lookH_eq_some_iff]
  exact ⟨i, by simp; omega, by simpa using hei, by rwa [List.take_take, min_eq_left hm.le]⟩

theorem lookF_append_inr_self {ℓ : Log} {s : KeccakState} (h : lookF ℓ s = none) (u : KeccakState) :
    lookF (ℓ ++ [.inr (s, u)]) s = some u := by
  rw [lookF, lookR_append, lookR_inr]; simp [h]

theorem lookF_append_inr_of_ne {ℓ : Log} {s s' : KeccakState} (h : s' ≠ s) (u : KeccakState) :
    lookF (ℓ ++ [.inr (s, u)]) s' = lookF ℓ s' := by
  rw [lookF, lookR_append, lookR_inr]; simp [Ne.symm h]

theorem lookF_append_inl (ℓ : Log) (p : Bytes × Digest) (s : KeccakState) :
    lookF (ℓ ++ [.inl p]) s = lookF ℓ s := by
  rw [lookF, lookR_append, lookR_inl]; simp

theorem mem_hIns_of_getElem {ℓ : Log} {i : ℕ} (hi : i < ℓ.length) {x : Bytes} {u : Digest}
    (h : ℓ[i] = .inl (x, u)) : x ∈ hIns ℓ :=
  List.mem_map.mpr ⟨(x, u), mem_leftOf.mpr (h ▸ List.getElem_mem hi), rfl⟩

theorem mem_hOuts_of_getElem {ℓ : Log} {i : ℕ} (hi : i < ℓ.length) {x : Bytes} {u : Digest}
    (h : ℓ[i] = .inl (x, u)) : u ∈ hOuts ℓ :=
  List.mem_map.mpr ⟨(x, u), mem_leftOf.mpr (h ▸ List.getElem_mem hi), rfl⟩

theorem mem_fIns_of_getElem {ℓ : Log} {i : ℕ} (hi : i < ℓ.length) {s u : KeccakState}
    (h : ℓ[i] = .inr (s, u)) : s ∈ fIns ℓ :=
  List.mem_map.mpr ⟨(s, u), mem_rightOf.mpr (h ▸ List.getElem_mem hi), rfl⟩

theorem mem_fOuts_of_getElem {ℓ : Log} {i : ℕ} (hi : i < ℓ.length) {s u : KeccakState}
    (h : ℓ[i] = .inr (s, u)) : u ∈ fOuts ℓ :=
  List.mem_map.mpr ⟨(s, u), mem_rightOf.mpr (h ▸ List.getElem_mem hi), rfl⟩

/-! ## The seeding -/

/-- A seeding: hash steps, each input a function of the answers before it, then a permutation
step whose input is a function of all the hash answers. The seed is the permutation's answer. -/
structure Seed where
  /-- The hash steps. -/
  hs : List (List Digest → Bytes)
  /-- The permutation step's input. -/
  fin : List Digest → KeccakState

/-- The hash steps from the answers `ds` so far. -/
def Seed.hsRun {m : Type → Type} [Monad m] (H : Bytes → m Digest) :
    List (List Digest → Bytes) → List Digest → m (List Digest)
  | [], ds => pure ds
  | f :: fs, ds => do
    let d ← H (f ds)
    Seed.hsRun H fs (ds ++ [d])

/-- The seed, computed with a hash function and a permutation in any monad. -/
def Seed.run {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)
    (σ : Seed) : m KeccakState := do
  let ds ← Seed.hsRun H σ.hs []
  F (σ.fin ds)

/-- The answers `ds` answer the hash steps of the seeding under the answers `H`. -/
def Answered (H : Bytes → Option Digest) (σ : Seed) (ds : List Digest) : Prop :=
  ds.length = σ.hs.length ∧
    ∀ (i : ℕ) (hi : i < ds.length), ∃ f, σ.hs[i]? = some f ∧ H (f (ds.take i)) = some ds[i]

theorem hsRun_option {H : Bytes → Option Digest} :
    ∀ (fs : List (List Digest → Bytes)) (ds₀ ds : List Digest),
      Seed.hsRun H fs ds₀ = some ds →
        ∃ ds', ds = ds₀ ++ ds' ∧ ds'.length = fs.length ∧
          ∀ (i : ℕ) (hi : i < ds'.length), ∃ f, fs[i]? = some f ∧
            H (f (ds.take (ds₀.length + i))) = some ds'[i]
  | [], ds₀, ds, h => by
    simp only [Seed.hsRun, pure, Option.some.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, fun i hi ↦ by simp at hi⟩
  | f :: fs, ds₀, ds, h => by
    simp only [Seed.hsRun, bind, Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, h⟩ := h
    obtain ⟨ds', rfl, hl, hall⟩ := hsRun_option fs (ds₀ ++ [d]) ds h
    refine ⟨d :: ds', by simp, by simp [hl], fun i hi ↦ ?_⟩
    cases i with
    | zero =>
      refine ⟨f, rfl, ?_⟩
      simpa [List.take_append_of_le_length] using hd
    | succ i =>
      obtain ⟨g, hg, hH⟩ := hall i (by simpa using hi)
      refine ⟨g, by simpa using hg, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hH

/-- A seeding run through answers in `Option` answers its hash steps. -/
theorem answered_of_hsRun {H : Bytes → Option Digest} {σ : Seed} {ds : List Digest}
    (h : Seed.hsRun H σ.hs [] = some ds) : Answered H σ ds := by
  obtain ⟨ds', rfl, hl, hall⟩ := hsRun_option σ.hs [] ds h
  refine ⟨by simpa using hl, fun i hi ↦ ?_⟩
  obtain ⟨f, hf, hH⟩ := hall i (by simpa using hi)
  exact ⟨f, hf, by simpa using hH⟩

/-- Answers that are injective: one answer, one input. -/
def AnswersInj (H : Bytes → Option Digest) : Prop :=
  ∀ x y v, H x = some v → H y = some v → x = y

/-- **A family of seedings**, one per statement `x : X`: the seeding `seed x`, and the history
`root x` of the verifier program at which its seed puts the sponge. Every hash answer of a
seeding is referred to by a later hash step, at an offset among `offs`, or by the first four
lanes of the permutation input; the permutation inputs have zero capacity; and the permutation
input, computed through answers without collisions, names its statement. -/
structure Seeds (X : Type) where
  /-- The seeding of a statement. -/
  seed : X → Seed
  /-- The history at which the seed puts the program. -/
  root : X → List Ev
  /-- The byte offsets at which hash steps carry earlier answers. -/
  offs : List ℕ
  /-- Every hash answer is referred to later. -/
  refs : ∀ x (ds : List Digest), ds.length = (seed x).hs.length → ∀ (i : ℕ) (hi : i < ds.length),
    laneDigest ((seed x).fin ds) = ds[i] ∨
      ∃ j f, i < j ∧ (seed x).hs[j]? = some f ∧ ∃ o ∈ offs, chunkAt o (f (ds.take j)) =
        digestBytes ds[i]
  /-- The permutation inputs have zero capacity. -/
  cap0 : ∀ x ds, capOf ((seed x).fin ds) = 0
  /-- The permutation input names the statement, for answers without collisions. -/
  inj : ∀ H : Bytes → Option Digest, AnswersInj H → ∀ x x' ds ds', Answered H (seed x) ds →
    Answered H (seed x') ds' → (seed x).fin ds = (seed x').fin ds' → x = x'

/-! ## Failure -/

/-- The root two adjacent waiting scalars of tag `1`, in slots `i` and `i + 1` of a permutation
input, encode. -/
def pairRoot (t : KeccakState) (i : ℕ) : Option Digest :=
  if slotTag t i = 1 ∧ slotTag t (i + 1) = 1 then digestFromHalves (slotE t i, slotE t (i + 1))
  else none

/-- The input that produced the state a permutation input continues: the first permutation
entry of the log whose output has the input's capacity. -/
def predIn (ℓ : Log) (t : KeccakState) : Option KeccakState :=
  ((rightOf ℓ).find? fun e ↦ decide (capOf e.2 = capOf t)).map Prod.fst

/-- The root straddling a forced permutation: the last waiting scalar of the input before, and
the first of this one, both of tag `1`. -/
def straddleRoot (ℓ : Log) (t : KeccakState) : Option Digest :=
  (predIn ℓ t).bind fun t' ↦
    if slotTag t' 3 = 1 ∧ slotTag t 0 = 1 then digestFromHalves (slotE t' 3, slotE t 0) else none

/-- The permutation input `t` absorbs the root `r` in the log `ℓ`. -/
def RootOf (ℓ : Log) (t : KeccakState) (r : Digest) : Prop :=
  (∃ i < 3, pairRoot t i = some r) ∨ straddleRoot ℓ t = some r

/-- A fresh hash answer `u` at `x` appended to `ℓ` fails. -/
def BadH {X : Type} (σ : Seeds X) (ℓ : Log) (x : Bytes) (u : Digest) : Prop :=
  u ∈ hOuts ℓ ∨
    (∃ y ∈ x :: hIns ℓ, ∃ o ∈ 0 :: 32 :: σ.offs, chunkAt o y = digestBytes u) ∨
    ∃ t ∈ fIns ℓ, RootOf ℓ t u ∨ laneDigest t = u

/-- A fresh permutation answer `u` at `s` appended to `ℓ` fails. -/
def BadF (ℓ : Log) (s u : KeccakState) : Prop :=
  (∃ v ∈ fOuts ℓ, capOf v = capOf u) ∨ (∃ y ∈ s :: fIns ℓ, capOf y = capOf u) ∨ capOf u = 0

/-- A fresh entry appended to `ℓ` fails. -/
def BadEntry {X : Type} (σ : Seeds X) (ℓ : Log) : Entry → Prop
  | .inl (x, u) => BadH σ ℓ x u
  | .inr (s, u) => BadF ℓ s u

/-- Some entry of the log failed with respect to the entries before it. -/
def Fail {X : Type} (σ : Seeds X) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length), BadEntry σ (ℓ.take i) ℓ[i]

theorem not_fail_nil {X : Type} (σ : Seeds X) : ¬ Fail σ [] := fun ⟨_, hi, _⟩ ↦ by simp at hi

/-- The log with one more entry fails exactly if the log fails or the entry does. -/
theorem fail_append {X : Type} (σ : Seeds X) (ℓ : Log) (e : Entry) :
    Fail σ (ℓ ++ [e]) ↔ Fail σ ℓ ∨ BadEntry σ ℓ e := by
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

/-- Sums over a finite type commute with sums over a list. -/
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

/-- The roots an input absorbs: at most four. -/
theorem sum_rootOf_le (ℓ : Log) (t : KeccakState) : ∑ u, ind (RootOf ℓ t u) ≤ 4 := by
  have hpair : ∀ i, ∑ u, ind (pairRoot t i = some u) ≤ 1 := fun i ↦
    sum_ind_le_one fun u u' hu hu' ↦ Option.some.inj (hu.symm.trans hu')
  have hstr : ∑ u, ind (straddleRoot ℓ t = some u) ≤ 1 :=
    sum_ind_le_one fun u u' hu hu' ↦ Option.some.inj (hu.symm.trans hu')
  have hpt : ∀ u, ind (RootOf ℓ t u) ≤
      ([0, 1, 2].map fun i ↦ ind (pairRoot t i = some u)).sum + ind (straddleRoot ℓ t = some u) := by
    intro u
    refine (ind_or_le _ _).trans (add_le_add ?_ le_rfl)
    refine (ind_mono fun ⟨i, hi, h⟩ ↦ ⟨i, ?_, h⟩).trans (ind_exists_le [0, 1, 2] _)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  calc ∑ u, ind (RootOf ℓ t u)
      ≤ ∑ u, (([0, 1, 2].map fun i ↦ ind (pairRoot t i = some u)).sum +
          ind (straddleRoot ℓ t = some u)) := Finset.sum_le_sum fun u _ ↦ hpt u
    _ = ([0, 1, 2].map fun i ↦ ∑ u, ind (pairRoot t i = some u)).sum +
          ∑ u, ind (straddleRoot ℓ t = some u) := by
        rw [Finset.sum_add_distrib, sum_list_sum_comm]
    _ ≤ ([0, 1, 2] : List ℕ).length * 1 + 1 :=
        add_le_add (list_sum_le _ _ _ fun i _ ↦ hpair i) hstr
    _ = 4 := by norm_num

/-- **The count of failing hash answers**: at most `(5 + |σ.offs|) · (|ℓ| + 1)` digests fail at a
fresh input. -/
theorem sum_badH_le {X : Type} (σ : Seeds X) (ℓ : Log) (x : Bytes) :
    ∑ u, ind (BadH σ ℓ x u) ≤ ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) := by
  set O := 0 :: 32 :: σ.offs
  set L := x :: hIns ℓ
  have hpt : ∀ u, ind (BadH σ ℓ x u) ≤
      ((hOuts ℓ).map fun v ↦ ind (v = u)).sum +
        (L.map fun y ↦ (O.map fun o ↦ ind (chunkAt o y = digestBytes u)).sum).sum +
        ((fIns ℓ).map fun t ↦ ind (RootOf ℓ t u) + ind (laneDigest t = u)).sum := by
    intro u
    refine (ind_or_le _ _).trans (add_le_add ?_ ?_) |>.trans_eq (add_assoc _ _ _).symm
    · exact (ind_mono fun h ↦ ⟨u, h, rfl⟩).trans (ind_exists_le _ _)
    refine (ind_or_le _ _).trans (add_le_add ?_ ?_)
    · refine (ind_exists_le _ _).trans (List.sum_le_sum fun y _ ↦ ind_exists_le _ _)
    · exact (ind_exists_le _ _).trans (List.sum_le_sum fun t _ ↦ ind_or_le _ _)
  have h1 : ∀ v ∈ hOuts ℓ, ∑ u, ind (v = u) ≤ 1 := fun v _ ↦
    sum_ind_le_one fun u u' hu hu' ↦ hu.symm.trans hu'
  have h2 : ∀ y ∈ L, ∑ u, (O.map fun o ↦ ind (chunkAt o y = digestBytes u)).sum ≤
      (O.length : ℝ≥0∞) := by
    intro y _
    rw [sum_list_sum_comm]
    have := list_sum_le O (fun o ↦ ∑ u, ind (chunkAt o y = digestBytes u)) 1 fun o _ ↦
      sum_ind_le_one fun u u' hu hu' ↦ digestBytes_injective (hu.symm.trans hu')
    rwa [mul_one] at this
  have h3 : ∀ t ∈ fIns ℓ, ∑ u, (ind (RootOf ℓ t u) + ind (laneDigest t = u)) ≤ 5 := by
    intro t _
    rw [Finset.sum_add_distrib]
    calc _ ≤ 4 + 1 := add_le_add (sum_rootOf_le ℓ t)
          (sum_ind_le_one fun u u' hu hu' ↦ hu.symm.trans hu')
      _ = 5 := by norm_num
  have hlen := length_leftOf_add_rightOf ℓ
  calc ∑ u, ind (BadH σ ℓ x u)
      ≤ ∑ u, (((hOuts ℓ).map fun v ↦ ind (v = u)).sum +
          (L.map fun y ↦ (O.map fun o ↦ ind (chunkAt o y = digestBytes u)).sum).sum +
          ((fIns ℓ).map fun t ↦ ind (RootOf ℓ t u) + ind (laneDigest t = u)).sum) :=
        Finset.sum_le_sum fun u _ ↦ hpt u
    _ = ((hOuts ℓ).map fun v ↦ ∑ u, ind (v = u)).sum +
          (L.map fun y ↦ ∑ u, (O.map fun o ↦ ind (chunkAt o y = digestBytes u)).sum).sum +
          ((fIns ℓ).map fun t ↦ ∑ u, (ind (RootOf ℓ t u) + ind (laneDigest t = u))).sum := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_list_sum_comm, sum_list_sum_comm,
          sum_list_sum_comm]
    _ ≤ (hOuts ℓ).length * 1 + L.length * (O.length : ℝ≥0∞) + (fIns ℓ).length * 5 :=
        add_le_add (add_le_add (list_sum_le _ _ _ h1) (list_sum_le _ _ _ h2))
          (list_sum_le _ _ _ h3)
    _ ≤ _ := by
        simp only [hOuts, fIns, L, O, hIns, List.length_map, List.length_cons, mul_one]
        have : ((leftOf ℓ).length : ℝ≥0∞) + (rightOf ℓ).length = ℓ.length := by
          exact_mod_cast hlen
        push_cast
        rw [← this]
        set a : ℝ≥0∞ := ((leftOf ℓ).length : ℝ≥0∞)
        set b : ℝ≥0∞ := ((rightOf ℓ).length : ℝ≥0∞)
        set o : ℝ≥0∞ := (σ.offs.length : ℝ≥0∞)
        have e1 : a + (a + 1) * (o + 1 + 1) + b * 5 = a * (3 + o) + b * 5 + (2 + o) := by ring
        have e2 : (5 + o) * (a + b + 1) = a * (3 + o) + a * 2 + (b * 5 + b * o) + (5 + o) := by
          ring
        rw [e1, e2]
        have h25 : (2 : ℝ≥0∞) + o ≤ 5 + o := by gcongr; norm_num
        calc a * (3 + o) + b * 5 + (2 + o) ≤ a * (3 + o) + b * 5 + (5 + o) := by gcongr
          _ ≤ a * (3 + o) + a * 2 + (b * 5 + b * o) + (5 + o) := by
            gcongr
            · exact le_self_add
            · exact le_self_add

/-- **The count of failing permutation answers**: the answer's capacity avoids at most
`2|ℓ| + 2` values, each with probability at most `2^-256`. -/
theorem sum_badF_div_le (ℓ : Log) (s : KeccakState) :
    (∑ u, ind (BadF ℓ s u)) / Fintype.card KeccakState ≤ ((2 * ℓ.length + 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 256 := by
  set C : List (Fin 9 → UInt64) := (fOuts ℓ).map capOf ++ (s :: fIns ℓ).map capOf ++ [0]
  have hpt : ∀ u, ind (BadF ℓ s u) ≤ (C.map fun c ↦ ind (capOf u = c)).sum := by
    intro u
    refine le_trans (ind_mono fun h ↦ ?_) (ind_exists_le C _)
    rcases h with ⟨v, hv, h⟩ | ⟨y, hy, h⟩ | h
    · exact ⟨capOf v, List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hv)),
        h.symm⟩
    · exact ⟨capOf y, List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hy)),
        h.symm⟩
    · exact ⟨0, List.mem_append_right _ (List.mem_singleton_self 0), h⟩
  have hC : C.length ≤ 2 * ℓ.length + 2 := by
    have := length_leftOf_add_rightOf ℓ
    simp [C, fOuts, fIns]
    omega
  calc (∑ u, ind (BadF ℓ s u)) / Fintype.card KeccakState
      ≤ (∑ u, (C.map fun c ↦ ind (capOf u = c)).sum) / Fintype.card KeccakState := by
        gcongr with u; exact hpt u
    _ = (C.map fun c ↦ (∑ u, ind (capOf u = c)) / Fintype.card KeccakState).sum := by
        rw [sum_list_sum_comm, div_eq_mul_inv, ← List.sum_map_mul_right]
        simp only [div_eq_mul_inv]
    _ ≤ C.length * 2⁻¹ ^ 256 := list_sum_le _ _ _ fun c _ ↦ sum_capOf_div_le c
    _ ≤ _ := by gcongr

end Count

/-! ## Order facts without failure -/

section Order

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- Without failure, hash outputs are distinct. -/
theorem hOut_ne (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length) (hij : i < j)
    {x y : Bytes} {u v : Digest} (hei : ℓ[i] = .inl (x, u)) (hej : ℓ[j] = .inl (y, v)) :
    u ≠ v := by
  rintro rfl
  have hb := h
  refine hb ⟨j, hj, ?_⟩
  rw [hej]
  exact Or.inl (mem_hOuts_of_getElem (ℓ := ℓ.take j) (i := i) (by simp; omega)
    (by simpa using hei))

/-- Without failure, two hash entries with one output are one entry. -/
theorem index_eq_of_hOut (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    {x y : Bytes} {u : Digest} (hei : ℓ[i] = .inl (x, u)) (hej : ℓ[j] = .inl (y, u)) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd rfl (hOut_ne h hi hj hij hei hej)
  · rfl
  · exact absurd rfl (hOut_ne h hj hi hij hej hei)

/-- Without failure, the capacities of permutation outputs are distinct. -/
theorem fCap_ne (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length) (hij : i < j)
    {s t u v : KeccakState} (hei : ℓ[i] = .inr (s, u)) (hej : ℓ[j] = .inr (t, v)) :
    capOf u ≠ capOf v := by
  intro hc
  refine h ⟨j, hj, ?_⟩
  rw [hej]
  exact Or.inl ⟨u, mem_fOuts_of_getElem (ℓ := ℓ.take j) (i := i) (by simp; omega)
    (by simpa using hei), hc⟩

/-- Without failure, no permutation output has the zero capacity. -/
theorem fCap_ne_zero (h : ¬ Fail σ ℓ) {i : ℕ} (hi : i < ℓ.length) {s u : KeccakState}
    (hei : ℓ[i] = .inr (s, u)) : capOf u ≠ 0 := by
  intro hc
  refine h ⟨i, hi, ?_⟩
  rw [hei]
  exact Or.inr (Or.inr hc)

/-- Without failure, a permutation entry whose output's capacity a permutation input carries
comes before it. -/
theorem lt_of_cap (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    {s t u v : KeccakState} (hei : ℓ[i] = .inr (s, u)) (hej : ℓ[j] = .inr (t, v))
    (hc : capOf t = capOf u) : i < j := by
  by_contra hji
  refine h ⟨i, hi, ?_⟩
  rw [hei]
  refine Or.inr (Or.inl ⟨t, ?_, hc⟩)
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hji) with hlt | rfl
  · exact List.mem_cons_of_mem _ (mem_fIns_of_getElem (ℓ := ℓ.take i) (i := j) (by simp; omega)
      (by simpa using hej))
  · rw [hei] at hej
    cases hej
    exact List.mem_cons_self

/-- Without failure, a hash entry whose output is a chunk, at an offset among `0`, `32` and the
seeding offsets, of a hash input comes before it. -/
theorem lt_of_chunk (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    {x y : Bytes} {u v : Digest} (hei : ℓ[i] = .inl (x, u)) (hej : ℓ[j] = .inl (y, v)) {o : ℕ}
    (ho : o ∈ 0 :: 32 :: σ.offs) (hc : chunkAt o y = digestBytes u) : i < j := by
  by_contra hji
  refine h ⟨i, hi, ?_⟩
  rw [hei]
  refine Or.inr (Or.inl ⟨y, ?_, o, ho, hc⟩)
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hji) with hlt | rfl
  · exact List.mem_cons_of_mem _ (mem_hIns_of_getElem (ℓ := ℓ.take i) (i := j) (by simp; omega)
      (by simpa using hej))
  · rw [hei] at hej
    cases hej
    exact List.mem_cons_self

/-- Without failure, a hash entry whose output is the IV a permutation input carries comes
before it. -/
theorem lt_of_laneDigest (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    {x : Bytes} {u : Digest} {t v : KeccakState} (hei : ℓ[i] = .inl (x, u))
    (hej : ℓ[j] = .inr (t, v)) (hc : laneDigest t = u) : i < j := by
  by_contra hji
  have hne : j ≠ i := fun e ↦ by subst e; rw [hei] at hej; cases hej
  refine h ⟨i, hi, ?_⟩
  rw [hei]
  exact Or.inr (Or.inr ⟨t, mem_fIns_of_getElem (ℓ := ℓ.take i) (i := j) (by simp; omega)
    (by simpa using hej), Or.inr hc⟩)

/-- The predecessor found in a prefix is found in every longer prefix. -/
theorem predIn_take_mono {ℓ : Log} {j i : ℕ} (hji : j ≤ i) {t t' : KeccakState}
    (h : predIn (ℓ.take j) t = some t') : predIn (ℓ.take i) t = some t' := by
  obtain ⟨n, rfl⟩ : ∃ n, i = j + n := ⟨i - j, by omega⟩
  have hsplit : ℓ.take (j + n) = ℓ.take j ++ (ℓ.drop j).take n := by
    rw [List.take_add]
  unfold predIn at h ⊢
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  refine Option.map_eq_some_iff.mpr ⟨e, ?_, rfl⟩
  rw [hsplit, rightOf_append, List.find?_append, he]
  rfl

/-- Roots absorbed in a prefix are absorbed in every longer prefix. -/
theorem rootOf_take_mono {ℓ : Log} {j i : ℕ} (hji : j ≤ i) {t : KeccakState} {r : Digest}
    (h : RootOf (ℓ.take j) t r) : RootOf (ℓ.take i) t r := by
  rcases h with h | h
  · exact Or.inl h
  · right
    unfold straddleRoot at h ⊢
    rcases hp : predIn (ℓ.take j) t with _ | t'
    · rw [hp] at h; simp at h
    · rw [hp] at h; rw [predIn_take_mono hji hp]; exact h

/-- Without failure, a hash entry whose output is a root a permutation input absorbs comes
before it. -/
theorem lt_of_rootOf (h : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    {x : Bytes} {u : Digest} {t v : KeccakState} (hei : ℓ[i] = .inl (x, u))
    (hej : ℓ[j] = .inr (t, v)) (hr : RootOf (ℓ.take j) t u) : i < j := by
  by_contra hji
  have hne : j ≠ i := fun e ↦ by subst e; rw [hei] at hej; cases hej
  refine h ⟨i, hi, ?_⟩
  rw [hei]
  exact Or.inr (Or.inr ⟨t, mem_fIns_of_getElem (ℓ := ℓ.take i) (i := j) (by simp; omega)
    (by simpa using hej), Or.inl (rootOf_take_mono (by omega) hr)⟩)

end Order

end
end LeanVM.Protocol.Compile.Rom
