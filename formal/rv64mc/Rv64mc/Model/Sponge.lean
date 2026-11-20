module

public import Rv64mc.Model.Merkle

/-!
# `transcript.rs`'s `Sponge` as the Rust computes it

`Sponge` holds the Keccak state `[u64; 25]`, an array of four waiting `(E, u64)` scalars with
their count `n_pending`, and the challenge a grind drew. `SpongeRust` mirrors it field by field
(the state a `List (BitVec 64)`, the scalars' `E` the statement's), and its methods follow the
Rust: `duplex` zeroes the rate, copies each waiting scalar's four lanes `[c0, c1, 0, tag]` over
lanes `4i..4i+4`, then permutes; `absorb` asserts that no ground challenge waits (`none` is the
panic), permutes a full queue, then queues; `sample` takes the ground challenge or permutes;
`absorb_nonce` absorbs with the nonce's tag, permutes and keeps the next challenge.

`SpongeRust.toSpec` is the statement's `Sponge` a Rust sponge stands for (the waiting scalars are
the first `n_pending`), and each method is proved to be the statement's over Keccak-f[1600]
(`duplex_toSpec`, `absorb_toSpec`, `sample_toSpec`, `absorbNonce_toSpec`, `new_toSpec`), keeping
the invariant `SpongeRust.Inv` (`25` lanes, four slots, at most four waiting).
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  LeanVM.Protocol.Compile

@[expose] public section

/-! ## Lists of lanes -/

theorem getD_set' {α : Type} (l : List α) (i j : ℕ) (a d : α) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < l.length
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem getD_append_left' {α : Type} {l₁ : List α} (l₂ : List α) {j : ℕ} (d : α)
    (h : j < l₁.length) : (l₁ ++ l₂).getD j d = l₁.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} {l₁ : List α} (l₂ : List α) {j : ℕ} (d : α)
    (h : l₁.length ≤ j) : (l₁ ++ l₂).getD j d = l₂.getD (j - l₁.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (i : ℕ) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem list_ext_getD {α : Type} {l₁ l₂ : List α} (d : α) (h : l₁.length = l₂.length)
    (h' : ∀ j < l₁.length, l₁.getD j d = l₂.getD j d) : l₁ = l₂ := by
  apply List.ext_getElem h
  intro j h1 h2
  have := h' j h1
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] using this

/-- A state of the Rust's `25` lanes as the statement's. -/
def ofStateBits (l : List (BitVec 64)) : KeccakState := Vector.ofFn fun i ↦ ⟨l.getD i 0⟩

theorem lane_ofStateBits (l : List (BitVec 64)) {i : ℕ} (hi : i < 25) :
    Keccak.lane (ofStateBits l) i = ⟨l.getD i 0⟩ := by
  simp [Keccak.lane, ofStateBits, hi]

theorem stateBits_length (a : KeccakState) : (stateBits a).length = 25 := by simp [stateBits]

theorem stateBits_ofStateBits {l : List (BitVec 64)} (h : l.length = 25) :
    stateBits (ofStateBits l) = l := by
  refine list_ext_getD 0 (by rw [stateBits_length, h]) fun j hj ↦ ?_
  rw [stateBits_length] at hj
  rw [getD_stateBits _ hj, lane_ofStateBits _ hj]

theorem ofStateBits_stateBits (a : KeccakState) : ofStateBits (stateBits a) = a := by
  apply Vector.ext
  intro i hi
  rw [ofStateBits, Vector.getElem_ofFn, getD_stateBits _ hi]
  simp [Keccak.lane, hi]

/-! ## The sponge -/

/-- `DS_OBSERVE`. -/
def dsObserveR : BitVec 64 := 1#64

/-- `DS_POW_NONCE`. -/
def dsPowNonceR : BitVec 64 := 4#64

/-- `Sponge`: `state`, `pending`, `n_pending` and `ground`. -/
structure SpongeRust where
  /-- `state: [u64; STATE_LANES]`. -/
  state : List (BitVec 64)
  /-- `pending: [(E, u64); RATE_SCALARS]`. -/
  pending : List (E × BitVec 64)
  /-- `n_pending`. -/
  nPending : ℕ
  /-- `ground`. -/
  ground : Option E

/-- The shape every sponge keeps: `25` lanes, four slots, at most four waiting. -/
def SpongeRust.Inv (r : SpongeRust) : Prop :=
  r.state.length = 25 ∧ r.pending.length = 4 ∧ r.nPending ≤ 4

/-- The statement's sponge a Rust sponge stands for. -/
def SpongeRust.toSpec (r : SpongeRust) : Sponge :=
  ⟨ofStateBits r.state, (r.pending.take r.nPending).map fun p ↦ (p.1, p.2.toNat), r.ground⟩

/-- `input[..16].fill(0)`. -/
def fillRate (s : List (BitVec 64)) : List (BitVec 64) :=
  (List.range 16).foldl (fun s i ↦ s.set i 0#64) s

/-- `input[4 * i..4 * i + 4].copy_from_slice(&w)`. -/
def writeLanes (s : List (BitVec 64)) (i : ℕ) (w : List (BitVec 64)) : List (BitVec 64) :=
  (List.range 4).foldl (fun s k ↦ s.set (4 * i + k) (w.getD k 0#64)) s

/-- A waiting scalar's four lanes, `[value.c0, value.c1, 0, tag]`. -/
def pendingWords (p : E × BitVec 64) : List (BitVec 64) := [(limbs p.1).1, (limbs p.1).2, 0#64, p.2]

/-- `Sponge::duplex`'s input: the state, its rate zeroed, the waiting scalars' lanes over it. -/
def duplexLanes (r : SpongeRust) : List (BitVec 64) :=
  ((r.pending.take r.nPending).zipIdx).foldl (fun s pi ↦ writeLanes s pi.2 (pendingWords pi.1))
    (fillRate r.state)

/-- `Sponge::duplex`: permute the input, and empty the queue. -/
def SpongeRust.duplex (r : SpongeRust) : SpongeRust :=
  { r with state := keccakFRust (duplexLanes r), nPending := 0 }

/-- `pending[n_pending] = p; n_pending += 1`. -/
def SpongeRust.push (r : SpongeRust) (p : E × BitVec 64) : SpongeRust :=
  { r with pending := r.pending.set r.nPending p, nPending := r.nPending + 1 }

/-- `Sponge::absorb(value, tag)`: `assert!(self.ground.is_none())`, a full queue permuted,
then `pending[n_pending] = (value, tag)`. -/
def SpongeRust.absorb (r : SpongeRust) (value : E) (tag : BitVec 64) : Option SpongeRust :=
  if r.ground.isSome then none
  else
    let r := if r.nPending = 4 then r.duplex else r
    some (r.push (value, tag))

/-- `Sponge::observe(value)`. -/
def SpongeRust.observe (r : SpongeRust) (value : E) : Option SpongeRust := r.absorb value dsObserveR

/-- The challenge in a state: `E::new(state[0], state[1])`. -/
def challengeRust (state : List (BitVec 64)) : E := ofLimbsW (state.getD 0 0, state.getD 1 0)

/-- `Sponge::sample`: `self.ground.take()`, else a permutation and `E::new(state[0], state[1])`. -/
def SpongeRust.sample (r : SpongeRust) : E × SpongeRust :=
  match r.ground with
  | some c => (c, { r with ground := none })
  | none => let r := r.duplex; (challengeRust r.state, r)

/-- `Sponge::absorb_nonce(nonce)`: absorb with `DS_POW_NONCE`, permute, keep the challenge,
return lane `2`. -/
def SpongeRust.absorbNonce (r : SpongeRust) (nonce : E) : Option (BitVec 64 × SpongeRust) := do
  let r ← r.absorb nonce dsPowNonceR
  let r := r.duplex
  let r := { r with ground := some (challengeRust r.state) }
  pure (r.state.getD 2 0, r)

/-- `Sponge::new(fiat_shamir_iv, public_input)`: the IV's words in lanes `0..4`, the public
input's in `4..8`, permuted. -/
def SpongeRust.new (iv publicInput : List (BitVec 8)) : SpongeRust :=
  let state := List.replicate 25 0#64
  let state := (List.range 4).foldl (fun s i ↦ s.set i ((digestWordsRust iv).getD i 0)) state
  let state :=
    (List.range 4).foldl (fun s i ↦ s.set (4 + i) ((digestWordsRust publicInput).getD i 0)) state
  ⟨keccakFRust state, List.replicate 4 (0, 0#64), 0, none⟩

/-! ## The lanes of a duplex -/

theorem length_foldl_of {α β : Type} (step : List α → β → List α)
    (h : ∀ s k, (step s k).length = s.length) (L : List β) (s : List α) :
    (L.foldl step s).length = s.length := by
  induction L generalizing s with
  | nil => rfl
  | cons a L ih => rw [List.foldl_cons, ih, h]

theorem getD_fillRate (s : List (BitVec 64)) (j : ℕ) :
    (fillRate s).getD j 0 = if j < 16 ∧ j < s.length then 0 else s.getD j 0 := by
  suffices ∀ n, ((List.range n).foldl (fun s i ↦ s.set i 0#64) s).getD j 0 =
      if j < n ∧ j < s.length then 0 else s.getD j 0 from this 16
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set', ih,
      length_foldl_of _ (fun _ _ ↦ List.length_set ..)]
    by_cases h1 : n = j
    · subst h1; by_cases h2 : n < s.length <;> simp [h2]
    · by_cases h3 : j < n <;> simp [h1, h3, show (j < n + 1) = (j < n) by
        apply propext; omega]

theorem length_fillRate (s : List (BitVec 64)) : (fillRate s).length = s.length :=
  length_foldl_of _ (fun _ _ ↦ List.length_set ..) _ _

theorem length_writeLanes (s : List (BitVec 64)) (i : ℕ) (w : List (BitVec 64)) :
    (writeLanes s i w).length = s.length :=
  length_foldl_of _ (fun _ _ ↦ List.length_set ..) _ _

theorem getD_writeLanes (s : List (BitVec 64)) (i : ℕ) (w : List (BitVec 64)) (j : ℕ) :
    (writeLanes s i w).getD j 0 =
      if 4 * i ≤ j ∧ j < 4 * i + 4 ∧ j < s.length then w.getD (j - 4 * i) 0 else s.getD j 0 := by
  suffices ∀ n ≤ 4, ((List.range n).foldl (fun s k ↦ s.set (4 * i + k) (w.getD k 0#64)) s).getD
      j 0 = if 4 * i ≤ j ∧ j < 4 * i + n ∧ j < s.length then w.getD (j - 4 * i) 0 else
      s.getD j 0 from this 4 le_rfl
  intro n hn
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set',
      ih (by omega), length_foldl_of _ (fun _ _ ↦ List.length_set ..)]
    by_cases h1 : 4 * i + n = j
    · subst h1
      by_cases h2 : 4 * i + n < s.length <;> simp [h2]
    · by_cases h3 : 4 * i ≤ j ∧ j < 4 * i + n ∧ j < s.length
      · simp [h1, h3, show j < 4 * i + (n + 1) by omega]
      · have h4 : ¬ (4 * i ≤ j ∧ j < 4 * i + (n + 1) ∧ j < s.length) := by omega
        simp [h1, h3, h4]

/-- The writes of the waiting scalars `ps`, the `k`-th at slot `n + k`. -/
theorem getD_writes (ps : List (E × BitVec 64)) (n : ℕ) (s : List (BitVec 64))
    (hs : s.length = 25) (hn : 4 * (n + ps.length) ≤ 16) (j : ℕ) :
    ((ps.zipIdx n).foldl (fun s pi ↦ writeLanes s pi.2 (pendingWords pi.1)) s).getD j 0 =
      if 4 * n ≤ j ∧ j < 4 * (n + ps.length) then
        (pendingWords (ps.getD ((j - 4 * n) / 4) (0, 0#64))).getD (j % 4) 0
      else s.getD j 0 := by
  induction ps generalizing n s with
  | nil => simp
  | cons p ps ih =>
    simp only [List.length_cons] at hn
    rw [List.zipIdx_cons, List.foldl_cons, ih (n + 1) _ (by rw [length_writeLanes, hs])
      (by omega), getD_writeLanes, hs]
    simp only [List.length_cons]
    by_cases h1 : 4 * (n + 1) ≤ j ∧ j < 4 * (n + 1 + ps.length)
    · rw [ite_eq_left h1, ite_eq_left ⟨by omega, by omega⟩]
      rw [show (j - 4 * n) / 4 = (j - 4 * (n + 1)) / 4 + 1 by omega, List.getD_cons_succ]
    · rw [ite_eq_right h1]
      by_cases h2 : 4 * n ≤ j ∧ j < 4 * n + 4
      · rw [ite_eq_left ⟨h2.1, h2.2, by omega⟩, ite_eq_left ⟨h2.1, by omega⟩,
          show (j - 4 * n) / 4 = 0 by omega, List.getD_cons_zero]
        congr 1
        omega
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem getD_pendingLanes (ps : List (E × ℕ)) (j : ℕ) :
    (pendingLanes ps).getD j 0 =
      if j < 4 * ps.length then
        [((ps.getD (j / 4) (0, 0)).1.limb 0).lane, ((ps.getD (j / 4) (0, 0)).1.limb 1).lane, 0,
          (ps.getD (j / 4) (0, 0)).2.toUInt64].getD (j % 4) 0
      else 0 := by
  induction ps generalizing j with
  | nil => simp [pendingLanes]
  | cons p ps ih =>
    rw [pendingLanes, List.flatMap_cons, ← pendingLanes]
    simp only [List.length_cons]
    by_cases h : j < 4
    · rw [getD_append_left' _ _ (by simpa using h), ite_eq_left (by omega),
        show j / 4 = 0 by omega, show j % 4 = j by omega, List.getD_cons_zero]
    · rw [getD_append_right' _ _ (by simp; omega), ih]
      simp only [show [((p.1.limb 0).lane), ((p.1.limb 1).lane), 0,
        p.2.toUInt64].length = 4 from rfl]
      by_cases h' : j - 4 < 4 * ps.length
      · rw [ite_eq_left h', ite_eq_left (by omega), show j / 4 = (j - 4) / 4 + 1 by omega,
          List.getD_cons_succ, show (j - 4) % 4 = j % 4 by omega]
      · rw [ite_eq_right h', ite_eq_right (by omega)]

theorem length_writes (ps : List (E × BitVec 64)) (n : ℕ) (s : List (BitVec 64)) :
    ((ps.zipIdx n).foldl (fun s pi ↦ writeLanes s pi.2 (pendingWords pi.1)) s).length =
      s.length := by
  induction ps generalizing n s with
  | nil => rfl
  | cons p ps ih => rw [List.zipIdx_cons, List.foldl_cons, ih, length_writeLanes]

theorem lane_ofFn (f : Fin 25 → UInt64) {j : ℕ} (hj : j < 25) :
    Keccak.lane (Vector.ofFn f) j = f ⟨j, hj⟩ := by
  simp [Keccak.lane, hj]

theorem length_duplexLanes (r : SpongeRust) : (duplexLanes r).length = r.state.length := by
  rw [duplexLanes, length_writes, length_fillRate]

/-- **The lanes `Sponge::duplex` permutes are the statement's `duplexInput`.** -/
theorem duplexLanes_eq (r : SpongeRust) (h : r.Inv) :
    duplexLanes r = stateBits (duplexInput r.toSpec) := by
  obtain ⟨hs, hp, hn⟩ := h
  have htake : (r.pending.take r.nPending).length = r.nPending := by simp [hp]; omega
  refine list_ext_getD 0 (by rw [length_duplexLanes, hs, stateBits_length]) fun j hj ↦ ?_
  rw [length_duplexLanes, hs] at hj
  rw [duplexLanes, getD_writes _ 0 _ (by rw [length_fillRate, hs]) (by omega), getD_stateBits _ hj,
    duplexInput, lane_ofFn _ hj, getD_fillRate, hs, htake]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero]
  by_cases h1 : j < 4 * r.nPending
  · rw [ite_eq_left h1, ite_eq_left (show j < 16 by omega), getD_pendingLanes, SpongeRust.toSpec]
    simp only [List.length_map, htake, ite_eq_left h1]
    rw [show ((0 : E), (0 : ℕ)) = (fun p : E × BitVec 64 ↦ (p.1, p.2.toNat)) (0, 0#64) from rfl,
      getD_map']
    generalize (r.pending.take r.nPending).getD (j / 4) (0, 0#64) = p
    rcases (show j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 by omega) with h | h | h | h <;>
      simp [h, pendingWords, limbs, K.lane]
  · rw [ite_eq_right h1]
    by_cases h2 : j < 16
    · rw [ite_eq_left ⟨h2, hj⟩, ite_eq_left h2, getD_pendingLanes, SpongeRust.toSpec]
      simp only [List.length_map, htake, ite_eq_right h1]
      rfl
    · rw [ite_eq_right (fun h ↦ h2 h.1), ite_eq_right h2, SpongeRust.toSpec, lane_ofStateBits _ hj]


/-! ## The methods are the statement's

The proofs never unfold Keccak-f: `keccakFRust` is irreducible here, and its lanes are rewritten
by `keccakFRust_eq`. -/

attribute [local irreducible] keccakFRust

theorem take_succ_set {α : Type} (l : List α) (n : ℕ) (p : α) (h : n < l.length) :
    (l.set n p).take (n + 1) = l.take n ++ [p] := by
  rw [List.take_add_one, List.getElem?_set_self h, List.take_set,
    List.set_eq_of_length_le (by simp)]
  rfl

@[simp] theorem duplex_pending (r : SpongeRust) : r.duplex.pending = r.pending := rfl
@[simp] theorem duplex_nPending (r : SpongeRust) : r.duplex.nPending = 0 := rfl
@[simp] theorem duplex_ground (r : SpongeRust) : r.duplex.ground = r.ground := rfl
@[simp] theorem push_state (r : SpongeRust) (p : E × BitVec 64) : (r.push p).state = r.state := rfl
@[simp] theorem push_pending (r : SpongeRust) (p : E × BitVec 64) :
    (r.push p).pending = r.pending.set r.nPending p := rfl
@[simp] theorem push_nPending (r : SpongeRust) (p : E × BitVec 64) :
    (r.push p).nPending = r.nPending + 1 := rfl
@[simp] theorem push_ground (r : SpongeRust) (p : E × BitVec 64) : (r.push p).ground = r.ground :=
  rfl

/-- `duplex` over Keccak-f[1600]. -/
theorem duplex_id (s : Sponge) :
    (duplex (m := Id) keccakF1600 s : Sponge) = ⟨keccakF1600 (duplexInput s), [], s.ground⟩ := rfl

theorem duplex_state (r : SpongeRust) (h : r.Inv) :
    r.duplex.state = stateBits (keccakF1600 (duplexInput r.toSpec)) := by
  rw [SpongeRust.duplex]
  dsimp only
  rw [duplexLanes_eq r h, keccakFRust_eq]

theorem duplex_inv (r : SpongeRust) (h : r.Inv) : r.duplex.Inv :=
  ⟨by rw [duplex_state r h, stateBits_length], by rw [duplex_pending]; exact h.2.1,
    by rw [duplex_nPending]; omega⟩

/-- **`Sponge::duplex` is `duplex`.** -/
theorem duplex_toSpec (r : SpongeRust) (h : r.Inv) :
    r.duplex.toSpec = (duplex (m := Id) keccakF1600 r.toSpec : Sponge) := by
  rw [duplex_id, SpongeRust.toSpec, SpongeRust.toSpec, duplex_state r h, ofStateBits_stateBits,
    duplex_nPending, duplex_ground, List.take_zero, List.map_nil]
  rfl

theorem toSpec_pending_length (r : SpongeRust) (h : r.Inv) :
    r.toSpec.pending.length = r.nPending := by
  have := h.2.2
  simp [SpongeRust.toSpec, h.2.1]
  omega

theorem push_toSpec (r : SpongeRust) (h : r.Inv) (h4 : r.nPending < 4) (v : E) (t : BitVec 64) :
    (r.push (v, t)).toSpec = { r.toSpec with pending := r.toSpec.pending ++ [(v, t.toNat)] } := by
  simp only [SpongeRust.toSpec, push_state, push_pending, push_nPending, push_ground]
  rw [take_succ_set _ _ _ (by rw [h.2.1]; exact h4), List.map_append]
  rfl

theorem push_inv (r : SpongeRust) (h : r.Inv) (h4 : r.nPending < 4) (p : E × BitVec 64) :
    (r.push p).Inv :=
  ⟨by rw [push_state]; exact h.1, by rw [push_pending, List.length_set]; exact h.2.1,
    by rw [push_nPending]; omega⟩

/-- **`Sponge::absorb` is `absorb`**, when no ground challenge waits; it panics otherwise. -/
theorem absorb_toSpec (r : SpongeRust) (h : r.Inv) (hg : r.ground = none) (v : E)
    (t : BitVec 64) :
    ∃ r', r.absorb v t = some r' ∧ r'.Inv ∧
      r'.toSpec = (absorb (m := Id) keccakF1600 r.toSpec v t.toNat : Sponge) := by
  have hl := toSpec_pending_length r h
  by_cases h4 : r.nPending = 4
  · have hd := duplex_inv r h
    have hd4 : r.duplex.nPending < 4 := by rw [duplex_nPending]; omega
    refine ⟨r.duplex.push (v, t), ?_, push_inv _ hd hd4 _, ?_⟩
    · simp [SpongeRust.absorb, hg, h4]
    · have hlen : r.toSpec.pending.length = rateScalars := by rw [hl, h4]; rfl
      rw [push_toSpec _ hd hd4, duplex_toSpec r h]
      simp only [absorb, hlen, ↓reduceIte]
      rfl
  · have h4' : r.nPending < 4 := by have := h.2.2; omega
    refine ⟨r.push (v, t), ?_, push_inv _ h h4' _, ?_⟩
    · simp [SpongeRust.absorb, hg, h4]
    · have hlen : ¬ r.toSpec.pending.length = rateScalars := by
        rw [hl]; exact fun e ↦ h4 (by rw [e]; rfl)
      rw [push_toSpec _ h h4']
      simp only [absorb, hlen, ↓reduceIte]
      rfl

theorem absorb_ground (r : SpongeRust) (hg : r.ground.isSome) (v : E) (t : BitVec 64) :
    r.absorb v t = none := by
  simp [SpongeRust.absorb, hg]

theorem challengeRust_stateBits (a : KeccakState) : challengeRust (stateBits a) = challengeOf a := by
  rw [challengeRust, getD_stateBits _ (by norm_num), getD_stateBits _ (by norm_num)]
  rfl

/-- **`Sponge::sample` is `squeeze`.** -/
theorem sample_toSpec (r : SpongeRust) (h : r.Inv) :
    (r.sample.1, r.sample.2.toSpec) = (squeeze (m := Id) keccakF1600 r.toSpec : E × Sponge) ∧
      r.sample.2.Inv := by
  unfold SpongeRust.sample
  cases hg : r.ground with
  | some c =>
    refine ⟨?_, h⟩
    simp only [squeeze, SpongeRust.toSpec, hg]
    rfl
  | none =>
    refine ⟨?_, duplex_inv r h⟩
    simp only [squeeze, show r.toSpec.ground = none by simp [SpongeRust.toSpec, hg]]
    rw [duplex_toSpec r h, duplex_state r h, challengeRust_stateBits, duplex_id]
    rfl

/-- **`Sponge::absorb_nonce` is `absorbNonce`**, when no ground challenge waits; the proof of
work is the same lane. -/
theorem absorbNonce_toSpec (r : SpongeRust) (h : r.Inv) (hg : r.ground = none) (n : E) :
    ∃ pow r', r.absorbNonce n = some (pow, r') ∧ r'.Inv ∧
      (UInt64.ofBitVec pow, r'.toSpec) =
        (absorbNonce (m := Id) keccakF1600 r.toSpec n : UInt64 × Sponge) := by
  obtain ⟨r1, h1, hi1, hs1⟩ := absorb_toSpec r h hg n dsPowNonceR
  have hd := duplex_inv r1 hi1
  refine ⟨r1.duplex.state.getD 2 0, { r1.duplex with ground := some (challengeRust r1.duplex.state) },
    ?_, ⟨hd.1, hd.2.1, hd.2.2⟩, ?_⟩
  · simp only [SpongeRust.absorbNonce, h1]
    rfl
  · have e : (absorbNonce (m := Id) keccakF1600 r.toSpec n : UInt64 × Sponge) =
        (Keccak.lane (duplex (m := Id) keccakF1600 r1.toSpec : Sponge).state 2,
          { (duplex (m := Id) keccakF1600 r1.toSpec : Sponge) with
            ground := some (challengeOf (duplex (m := Id) keccakF1600 r1.toSpec : Sponge).state) }) := by
      rw [hs1]
      rfl
    rw [e, ← duplex_toSpec r1 hi1]
    simp only [SpongeRust.toSpec, duplex_state r1 hi1, ofStateBits_stateBits, duplex_pending,
      duplex_nPending, challengeRust_stateBits, getD_stateBits _ (show 2 < 25 by norm_num)]

theorem getD_foldl_set_range (o n : ℕ) (f : ℕ → BitVec 64) (s : List (BitVec 64)) (j : ℕ) :
    ((List.range n).foldl (fun s i ↦ s.set (o + i) (f i)) s).getD j 0 =
      if o ≤ j ∧ j < o + n ∧ j < s.length then f (j - o) else s.getD j 0 := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set', ih,
      length_foldl_of _ (fun _ _ ↦ List.length_set ..)]
    by_cases h1 : o + n = j
    · subst h1
      by_cases h2 : o + n < s.length <;> simp [h2]
    · by_cases h3 : o ≤ j ∧ j < o + n ∧ j < s.length
      · simp [h1, h3, show j < o + (n + 1) by omega]
      · have h4 : ¬ (o ≤ j ∧ j < o + (n + 1) ∧ j < s.length) := by omega
        simp [h1, h3, h4]

theorem getD_words (d : Digest) {j : ℕ} (hj : j < 4) :
    (digestWordsRust (digestBits d)).getD j 0 = d[j].toBitVec := by
  rw [digestBits, digestWordsRust_digestBytes]
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_replicate' {α : Type} (n : ℕ) (a d : α) (i : ℕ) :
    (List.replicate n a).getD i d = if i < n then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- The lanes `Sponge::new` permutes. -/
def newLanes (iv publicInput : List (BitVec 8)) : List (BitVec 64) :=
  (List.range 4).foldl (fun s i ↦ s.set (4 + i) ((digestWordsRust publicInput).getD i 0))
    ((List.range 4).foldl (fun s i ↦ s.set i ((digestWordsRust iv).getD i 0))
      (List.replicate 25 0#64))

theorem new_state (iv publicInput : List (BitVec 8)) :
    (SpongeRust.new iv publicInput).state = keccakFRust (newLanes iv publicInput) := rfl

theorem newLanes_eq (iv publicInput : Digest) :
    newLanes (digestBits iv) (digestBits publicInput) = stateBits (seedInput iv publicInput) := by
  have hlen : (newLanes (digestBits iv) (digestBits publicInput)).length = 25 := by
    rw [newLanes, length_foldl_of _ (fun _ _ ↦ List.length_set ..),
      length_foldl_of _ (fun _ _ ↦ List.length_set ..), List.length_replicate]
  have h1 := getD_foldl_set_range 0 4 (fun i ↦ (digestWordsRust (digestBits iv)).getD i 0)
    (List.replicate 25 0#64)
  simp only [Nat.zero_add] at h1
  refine list_ext_getD 0 (by rw [hlen, stateBits_length]) fun j hj ↦ ?_
  rw [hlen] at hj
  rw [newLanes, getD_foldl_set_range, h1, getD_stateBits _ hj, seedInput, lane_ofFn _ hj,
    length_foldl_of _ (fun _ _ ↦ List.length_set ..), List.length_replicate, getD_replicate']
  by_cases ha : j < 4
  · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, by omega⟩]
    simp only [ha, ↓reduceDIte, Nat.sub_zero]
    exact getD_words iv ha
  · by_cases hb : j < 8
    · rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
      simp only [ha, hb, ↓reduceDIte]
      exact getD_words publicInput (by omega)
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hj]
      simp only [ha, hb, ↓reduceDIte]
      rfl

/-- **`Sponge::new` is the statement's initial sponge**: the permutation of `seedInput`. -/
theorem new_toSpec (iv publicInput : Digest) :
    (SpongeRust.new (digestBits iv) (digestBits publicInput)).toSpec =
      ⟨keccakF1600 (seedInput iv publicInput), [], none⟩ ∧
      (SpongeRust.new (digestBits iv) (digestBits publicInput)).Inv := by
  have hs : (SpongeRust.new (digestBits iv) (digestBits publicInput)).state =
      stateBits (keccakF1600 (seedInput iv publicInput)) := by
    rw [new_state, newLanes_eq, keccakFRust_eq]
  refine ⟨?_, ⟨by rw [hs, stateBits_length], rfl, Nat.zero_le _⟩⟩
  rw [SpongeRust.toSpec, hs, ofStateBits_stateBits]
  rfl

end

end Rv64mc.Model
