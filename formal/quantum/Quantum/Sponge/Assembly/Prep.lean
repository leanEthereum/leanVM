module

public import Quantum.Sponge.Hash
public import Quantum.Sponge.Bound
public import Quantum.Sponge.PermTail

@[expose] public section

/-!
# Pieces of the sponge's collision and preimage bounds

The parts of the end-to-end collision and preimage bounds of the sponge in the QRPM (Corollaries
6.13 and 6.14 of Alagic, Carolan, Majenz and Tokat, ePrint 2025/731) that do not involve the
quantum reads.

* `spongeEvalM`: the classical evaluation of the sponge through reads of `k`, `k'` and `h`, three
  per block, in any monad. With reads answered by total functions and logged
  (`run_spongeEvalM_log`), it returns `spongeHash φ m` and logs `spongeReads π h k k' m`.
* `agreesRounds_of_heldBy`: a database holding every logged read holds the rounds of `m` and the
  final `h` point, so it holds a collision of two messages with equal outputs
  (`collision_of_heldBy`), or a path to the output of a message (`reachesOutput_of_heldBy`).
* `average_le`: averaging over a uniform `π` costs the fraction of bad permutations.
* `collisionRateBound_le`, `preimageRateBound_le`: closed forms of the per-port fractions.
-/

namespace Quantum.Sponge

open Quantum Finset
open scoped ENNReal

/-! ## Collisions and preimages of the sponge as database paths -/

section Bridge

variable {X Z Y : Type} [AddCommGroup X] [AddCommGroup Z] (π : Equiv.Perm (X × Z)) (h : Z → X)
  (k k' : X → Z) {D : Dbs X Z} {out : X → Y}

/-- A database holding the rounds of a nonempty `m` and its final `h` point holds the tail of `m`
reaching the output of its hash. -/
theorem reaches_of_agrees {m : List X} (hm : m ≠ []) (hD : AgreesRounds π h k k' D m)
    (hh : D.h (absorb (spongePerm (h, k, k') π) m).2 =
      some (h (absorb (spongePerm (h, k, k') π) m).2)) :
    Reaches π D out (absorbTail (spongePerm (h, k, k') π) m)
      (out (spongeHash (spongePerm (h, k, k') π) m)) := by
  obtain ⟨t0, zp, xp, a, xi, zi, b, w, ht, htail, ha, hπ, hb, hw, hhash⟩ :=
    isHeadPath_of_agrees π h k k' hm hD hh
  exact ⟨zi + b, xi, w, ⟨t0, zp, xp, a, zi, b, ht, htail, ha, hπ, hb, rfl⟩, hw, by rw [hhash]⟩

/-- **A sponge collision is a database collision.** A database holding the rounds and final `h`
points of two distinct nonempty messages with equal outputs holds a collision. -/
theorem collision_of_agrees {m m' : List X} (hm : m ≠ []) (hm' : m' ≠ []) (hne : m ≠ m')
    (hD : AgreesRounds π h k k' D m)
    (hh : D.h (absorb (spongePerm (h, k, k') π) m).2 =
      some (h (absorb (spongePerm (h, k, k') π) m).2))
    (hD' : AgreesRounds π h k k' D m')
    (hh' : D.h (absorb (spongePerm (h, k, k') π) m').2 =
      some (h (absorb (spongePerm (h, k, k') π) m').2))
    (hout : out (spongeHash (spongePerm (h, k, k') π) m) =
      out (spongeHash (spongePerm (h, k, k') π) m')) :
    Collision π D out :=
  ⟨_, _, _, fun ht ↦ hne (absorbTail_injective _ ht), reaches_of_agrees π h k k' hm hD hh,
    hout ▸ reaches_of_agrees π h k k' hm' hD' hh'⟩

/-- **A sponge preimage is a database path.** A database holding the rounds and final `h` point
of a nonempty message whose output is `y0` holds a path to `y0`. -/
theorem reachesOutput_of_agrees {m : List X} {y0 : Y} (hm : m ≠ [])
    (hD : AgreesRounds π h k k' D m)
    (hh : D.h (absorb (spongePerm (h, k, k') π) m).2 =
      some (h (absorb (spongePerm (h, k, k') π) m).2))
    (hout : out (spongeHash (spongePerm (h, k, k') π) m) = y0) :
    ReachesOutput π D out y0 :=
  ⟨_, by rw [← hout]; exact reaches_of_agrees π h k k' hm hD hh⟩

end Bridge

/-! ## Evaluating the sponge through reads -/

section Eval

/-- A classical read of one of the three functions together with its answer: `h` at `z : Z`,
`k` or `k'` at `x : X`. -/
inductive SpongeRead (X Z : Type) where
  /-- `h z = a`. -/
  | h (z : Z) (a : X)
  /-- `k x = a`. -/
  | k (x : X) (a : Z)
  /-- `k' x = a`. -/
  | k' (x : X) (a : Z)
  deriving DecidableEq

variable {X Z : Type}

/-- The port a read queries. -/
def SpongeRead.port : SpongeRead X Z → SpongePort
  | .h _ _ => .h
  | .k _ _ => .k
  | .k' _ _ => .k'

/-- The databases `D` hold the read's answer at its point. -/
def SpongeRead.HeldBy (D : Dbs X Z) : SpongeRead X Z → Prop
  | .h z a => D.h z = some a
  | .k x a => D.k x = some a
  | .k' x a => D.k' x = some a

variable [AddCommGroup X] [AddCommGroup Z] (π : Equiv.Perm (X × Z))

/-- One round of the evaluation from state `s` on block `b`: read `k` at the block entering `π`,
`k'` at the intermediate rate, and `h` at the new capacity. -/
def evalRoundM {M : Type → Type} [Monad M] (rh : Z → M X) (rk rk' : X → M Z) (s : X × Z) (b : X) :
    M (X × Z) := do
  let xp := s.1 + b
  let a ← rk xp
  let p := π (xp, s.2 + a)
  let c ← rk' p.1
  let w ← rh (p.2 + c)
  pure (p.1 + w, p.2 + c)

/-- The sponge's evaluation of `msg` through the reads `rh`, `rk`, `rk'` of `h`, `k`, `k'`, three
per block. -/
def spongeEvalM {M : Type → Type} [Monad M] (rh : Z → M X) (rk rk' : X → M Z) (msg : List X) :
    M X :=
  (fun s ↦ s.1) <$> msg.foldlM (evalRoundM π rh rk rk') (0, 0)

/-- Read `h` at `z`, answered by `h` and logged. -/
def readH (h : Z → X) (z : Z) : StateM (List (SpongeRead X Z)) X :=
  modifyGet fun L ↦ (h z, L ++ [.h z (h z)])

/-- Read `k` at `x`, answered by `k` and logged. -/
def readK (k : X → Z) (x : X) : StateM (List (SpongeRead X Z)) Z :=
  modifyGet fun L ↦ (k x, L ++ [.k x (k x)])

/-- Read `k'` at `x`, answered by `k'` and logged. -/
def readK' (k' : X → Z) (x : X) : StateM (List (SpongeRead X Z)) Z :=
  modifyGet fun L ↦ (k' x, L ++ [.k' x (k' x)])

variable (h : Z → X) (k k' : X → Z)

/-- The reads of one round from state `s` on block `b`, answered by `h`, `k`, `k'`. -/
def roundReads (s : X × Z) (b : X) : List (SpongeRead X Z) :=
  [.k (s.1 + b) (k (s.1 + b)),
    .k' (π (s.1 + b, s.2 + k (s.1 + b))).1 (k' (π (s.1 + b, s.2 + k (s.1 + b))).1),
    .h ((π (s.1 + b, s.2 + k (s.1 + b))).2 + k' (π (s.1 + b, s.2 + k (s.1 + b))).1)
      (h ((π (s.1 + b, s.2 + k (s.1 + b))).2 + k' (π (s.1 + b, s.2 + k (s.1 + b))).1))]

/-- The step of the logged evaluation: absorb the block and append the round's reads. -/
def logStep (p : (X × Z) × List (SpongeRead X Z)) (b : X) : (X × Z) × List (SpongeRead X Z) :=
  (absorbStep (spongePerm (h, k, k') π) p.1 b, p.2 ++ roundReads π h k k' p.1 b)

/-- The reads of evaluating `msg` with answers `h`, `k`, `k'`: the `k`, `k'` and `h` points of
every round, in order. -/
def spongeReads (msg : List X) : List (SpongeRead X Z) :=
  (msg.foldl (logStep π h k k') ((0, 0), [])).2

theorem run_evalRoundM_log (s : X × Z) (b : X) (L : List (SpongeRead X Z)) :
    (evalRoundM π (readH h) (readK k) (readK' k') s b).run L = logStep π h k k' (s, L) b := by
  refine Prod.ext rfl ?_
  show ((L ++ [_]) ++ [_]) ++ [_] = L ++ [_, _, _]
  simp

theorem run_foldlM_log (msg : List X) (s : X × Z) (L : List (SpongeRead X Z)) :
    (msg.foldlM (evalRoundM π (readH h) (readK k) (readK' k')) s).run L =
      msg.foldl (logStep π h k k') (s, L) := by
  induction msg generalizing s L with
  | nil => rfl
  | cons b msg ih =>
    rw [List.foldlM_cons, StateT.run_bind, run_evalRoundM_log, List.foldl_cons]
    exact ih _ _

theorem fst_foldl_logStep (msg : List X) (p : (X × Z) × List (SpongeRead X Z)) :
    (msg.foldl (logStep π h k k') p).1 = msg.foldl (absorbStep (spongePerm (h, k, k') π)) p.1 := by
  induction msg generalizing p with
  | nil => rfl
  | cons b msg ih => exact ih _

/-- **The logged evaluation.** Answered by `h`, `k`, `k'`, the evaluation of `msg` returns the
sponge's hash under `φ = spongePerm (h, k, k') π` and logs `spongeReads π h k k' msg`. -/
theorem run_spongeEvalM_log (msg : List X) :
    (spongeEvalM π (readH h) (readK k) (readK' k') msg).run [] =
      (spongeHash (spongePerm (h, k, k') π) msg, spongeReads π h k k' msg) := by
  rw [spongeEvalM, StateT.run_map, run_foldlM_log]
  refine Prod.ext ?_ rfl
  change (msg.foldl (logStep π h k k') ((0, 0), [])).1.1 = _
  rw [fst_foldl_logStep]
  rfl

theorem spongeReads_nil : spongeReads π h k k' ([] : List X) = [] :=
  rfl

theorem spongeReads_append_singleton (msg : List X) (b : X) :
    spongeReads π h k k' (msg ++ [b]) =
      spongeReads π h k k' msg ++ roundReads π h k k' (absorb (spongePerm (h, k, k') π) msg) b := by
  simp only [spongeReads, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [logStep, fst_foldl_logStep]
  rfl

/-- Each block makes one read of each port. -/
theorem countP_port_spongeReads (msg : List X) (i : SpongePort) :
    (spongeReads π h k k' msg).countP (fun e ↦ e.port = i) = msg.length := by
  induction msg using List.reverseRecOn with
  | nil => rfl
  | append_singleton msg b ih =>
    rw [spongeReads_append_singleton, List.countP_append, ih]
    cases i <;> simp [roundReads, SpongeRead.port]

theorem length_spongeReads (msg : List X) :
    (spongeReads π h k k' msg).length = 3 * msg.length := by
  induction msg using List.reverseRecOn with
  | nil => rfl
  | append_singleton msg b ih =>
    rw [spongeReads_append_singleton, List.length_append, ih]
    simp [roundReads]
    ring

/-- A database holding every read of `msg` holds its rounds and its final `h` point. -/
theorem agreesRounds_of_heldBy {D : Dbs X Z} {msg : List X}
    (hD : ∀ e ∈ spongeReads π h k k' msg, e.HeldBy D) :
    AgreesRounds π h k k' D msg ∧
      (msg ≠ [] → D.h (absorb (spongePerm (h, k, k') π) msg).2 =
        some (h (absorb (spongePerm (h, k, k') π) msg).2)) := by
  induction msg using List.reverseRecOn with
  | nil => exact ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero _), fun h ↦ absurd rfl h⟩
  | append_singleton msg b ih =>
    rw [spongeReads_append_singleton] at hD
    have hr : ∀ e ∈ roundReads π h k k' (absorb (spongePerm (h, k, k') π) msg) b, e.HeldBy D :=
      fun e he ↦ hD e (List.mem_append_right _ he)
    simp only [roundReads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, SpongeRead.HeldBy] at hr
    obtain ⟨hk, hk', hh⟩ := hr
    have hm := (ih fun e he ↦ hD e (List.mem_append_left _ he)).1
    refine ⟨fun j hj ↦ ?_, fun _ ↦ ?_⟩
    · rcases Nat.lt_or_ge j msg.length with hj' | hj'
      · have := hm j hj'
        simp only [List.take_append_of_le_length hj'.le, List.getElem_append_left hj']
        exact this
      · have hjm : j = msg.length := by simp at hj; omega
        subst hjm
        simp only [List.take_left', List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
        exact ⟨hk, hk'⟩
    · rw [absorb_append_singleton]
      exact hh

/-- Two distinct nonempty messages with equal outputs, all of whose reads a database holds, give
a collision in the database. -/
theorem collision_of_heldBy {Y : Type} {out : X → Y} {D : Dbs X Z} {m m' : List X} (hm : m ≠ [])
    (hm' : m' ≠ []) (hne : m ≠ m') (hD : ∀ e ∈ spongeReads π h k k' m, e.HeldBy D)
    (hD' : ∀ e ∈ spongeReads π h k k' m', e.HeldBy D)
    (hout : out (spongeHash (spongePerm (h, k, k') π) m) =
      out (spongeHash (spongePerm (h, k, k') π) m')) :
    D ∈ CollisionBad π out :=
  Or.inr <| collision_of_agrees π h k k' hm hm' hne (agreesRounds_of_heldBy π h k k' hD).1
    ((agreesRounds_of_heldBy π h k k' hD).2 hm) (agreesRounds_of_heldBy π h k k' hD').1
    ((agreesRounds_of_heldBy π h k k' hD').2 hm') hout

/-- A nonempty message with output `y0`, all of whose reads a database holds, gives a path to
`y0` in the database. -/
theorem reachesOutput_of_heldBy {Y : Type} {out : X → Y} {D : Dbs X Z} {m : List X} {y0 : Y}
    (hm : m ≠ []) (hD : ∀ e ∈ spongeReads π h k k' m, e.HeldBy D)
    (hout : out (spongeHash (spongePerm (h, k, k') π) m) = y0) :
    D ∈ PreimageBad π out y0 :=
  Or.inr <| reachesOutput_of_agrees π h k k' hm (agreesRounds_of_heldBy π h k k' hD).1
    ((agreesRounds_of_heldBy π h k k' hD).2 hm) hout

end Eval

section Fill

variable {X Z : Type} [Zero X] [Zero Z]

/-- Total functions extending the databases `D`, `0` outside their points. Reads held by `D` are
answered by `D.fill`. -/
def Dbs.fill (D : Dbs X Z) : (Z → X) × (X → Z) × (X → Z) :=
  (fun z ↦ (D.h z).getD 0, fun x ↦ (D.k x).getD 0, fun x ↦ (D.k' x).getD 0)

theorem Dbs.fill_h {D : Dbs X Z} {z : Z} {a : X} (h : D.h z = some a) : D.fill.1 z = a := by
  simp [Dbs.fill, h]

theorem Dbs.fill_k {D : Dbs X Z} {x : X} {a : Z} (h : D.k x = some a) : D.fill.2.1 x = a := by
  simp [Dbs.fill, h]

theorem Dbs.fill_k' {D : Dbs X Z} {x : X} {a : Z} (h : D.k' x = some a) : D.fill.2.2 x = a := by
  simp [Dbs.fill, h]

end Fill

/-! ## Averaging over the permutation -/

section Average

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- **Averaging over `π`.** A quantity at most `1`, and at most `B` for good permutations,
averages over a uniform `π` to at most the fraction of bad permutations plus `B`. -/
theorem average_le {G : ℕ} {B : ℝ≥0∞} (p : Equiv.Perm (X × Z) → ℝ≥0∞) (hp : ∀ π, p π ≤ 1)
    (hB : ∀ π, PermGood π G → p π ≤ B) :
    (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π, p π ≤
      (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G) : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) + B := by
  set N := (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)
  have hN0 : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑ π, p π ≤
      (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G) : ℝ≥0∞) + N * B := by
    rw [← sum_filter_add_sum_filter_not univ fun π ↦ ¬PermGood π G]
    gcongr
    · calc ∑ π ∈ univ.filter fun π ↦ ¬PermGood π G, p π
          ≤ ∑ _π ∈ univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G, (1 : ℝ≥0∞) :=
            sum_le_sum fun π _ ↦ hp π
        _ = _ := by simp
    · calc ∑ π ∈ univ.filter fun π ↦ ¬¬PermGood π G, p π
          ≤ ∑ _π ∈ univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬¬PermGood π G, B :=
            sum_le_sum fun π hπ ↦ hB π (not_not.mp (mem_filter.mp hπ).2)
        _ ≤ ∑ _π : Equiv.Perm (X × Z), B := sum_le_sum_of_subset (filter_subset _ _)
        _ = N * B := by simp [N]
  calc N⁻¹ * ∑ π, p π
      ≤ N⁻¹ * ((#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G) : ℝ≥0∞) + N * B) := by
        gcongr
    _ = _ := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul, ENNReal.div_eq_inv_mul]

/-- `average_le` with `PermGood π (3 s)` and the bound of `prob_not_permGood_le`. -/
theorem average_le_of_permGood {s : ℕ} (hs : 2 * s < Fintype.card X * Fintype.card Z) {B : ℝ≥0∞}
    (p : Equiv.Perm (X × Z) → ℝ≥0∞) (hp : ∀ π, p π ≤ 1)
    (hB : ∀ π, PermGood π (3 * s) → p π ≤ B) :
    (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π, p π ≤
      ENNReal.ofReal ((Fintype.card X : ℝ) ^ 2 * (Fintype.card Z).choose s *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s +
        (Fintype.card X : ℝ) ^ 2 * Fintype.card Z * (Fintype.card Z).choose s *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) + B := by
  refine (average_le p hp hB).trans ?_
  gcongr
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Fintype.card _),
    ← ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  exact ENNReal.ofReal_le_ofReal (prob_not_permGood_le hs)

end Average

/-! ## Closed forms of the per-port fractions -/

section Rates

variable {X Z : Type} [Fintype X] [Fintype Z]

/-- Both `|Z|` counts of `collisionRateBound` and `preimageRateBound` are at most
`(T + 2)³ G + 2 T + 1`. -/
theorem rateCounts_le (T G : ℕ) :
    (T + 1) * ((T + 1) * T + 2 * T) * G ≤ (T + 2) ^ 3 * G + 2 * T + 1 ∧
      (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T ≤ (T + 2) ^ 3 * G + 2 * T + 1 := by
  have h1 : (T + 1) * ((T + 1) * T + 2 * T) ≤ (T + 2) ^ 3 := by nlinarith
  have h2 : T * ((T + 1) * T + T + 1) + T * T ≤ (T + 2) ^ 3 := by nlinarith
  constructor
  · calc (T + 1) * ((T + 1) * T + 2 * T) * G ≤ (T + 2) ^ 3 * G := Nat.mul_le_mul_right G h1
      _ ≤ _ := by omega
  · have := Nat.mul_le_mul_right G h2
    nlinarith

private theorem max_div_le {a b c : ℕ} (hab : a ≤ c) (hbc : b ≤ c) :
    max ((a : ℕ) / Fintype.card Z : ℝ≥0∞) ((b : ℕ) / Fintype.card Z : ℝ≥0∞) ≤
      (c : ℝ≥0∞) / Fintype.card Z :=
  max_le (by gcongr) (by gcongr)

/-- `collisionRateBound T G F ≤ max (T F / |X|) (((T + 2)³ G + 2 T + 1) / |Z|)`. -/
theorem collisionRateBound_le [DecidableEq X] [DecidableEq Z] (T G F : ℕ) :
    collisionRateBound (X := X) (Z := Z) T G F ≤
      max ((T * F : ℕ) / Fintype.card X : ℝ≥0∞)
        (((T + 2) ^ 3 * G + 2 * T + 1 : ℕ) / Fintype.card Z : ℝ≥0∞) :=
  max_le_max le_rfl (max_div_le (rateCounts_le T G).1 (rateCounts_le T G).2)

/-- `preimageRateBound T G F ≤ max (F / |X|) (((T + 2)³ G + 2 T + 1) / |Z|)`. -/
theorem preimageRateBound_le [DecidableEq X] [DecidableEq Z] (T G F : ℕ) :
    preimageRateBound (X := X) (Z := Z) T G F ≤
      max ((F : ℕ) / Fintype.card X : ℝ≥0∞)
        (((T + 2) ^ 3 * G + 2 * T + 1 : ℕ) / Fintype.card Z : ℝ≥0∞) :=
  max_le_max le_rfl (max_div_le (rateCounts_le T G).1 (rateCounts_le T G).2)

/-- The collision weight of `T` calls in closed form:
`6 T² ε ≤ 6 T² (T F / |X| + ((T + 2)³ G + 2 T + 1) / |Z|)`. -/
theorem six_mul_collisionRateBound_le [DecidableEq X] [DecidableEq Z] (T G F : ℕ) :
    6 * (T : ℝ≥0∞) ^ 2 * collisionRateBound (X := X) (Z := Z) T G F ≤
      6 * (T : ℝ≥0∞) ^ 2 * ((T * F : ℕ) / Fintype.card X +
        ((T + 2) ^ 3 * G + 2 * T + 1 : ℕ) / Fintype.card Z) := by
  gcongr
  exact (collisionRateBound_le T G F).trans (max_le le_self_add le_add_self)

/-- The preimage weight of `T` calls in closed form:
`6 T² ε ≤ 6 T² (F / |X| + ((T + 2)³ G + 2 T + 1) / |Z|)`. -/
theorem six_mul_preimageRateBound_le [DecidableEq X] [DecidableEq Z] (T G F : ℕ) :
    6 * (T : ℝ≥0∞) ^ 2 * preimageRateBound (X := X) (Z := Z) T G F ≤
      6 * (T : ℝ≥0∞) ^ 2 * ((F : ℕ) / Fintype.card X +
        ((T + 2) ^ 3 * G + 2 * T + 1 : ℕ) / Fintype.card Z) := by
  gcongr
  exact (preimageRateBound_le T G F).trans (max_le le_self_add le_add_self)

end Rates

end Quantum.Sponge

end
