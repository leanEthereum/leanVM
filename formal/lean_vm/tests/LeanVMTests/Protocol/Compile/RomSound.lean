import LeanVM.Protocol.Compile.Rom.Sound
import LeanVM.Protocol.Compile.Cost
import LeanVM.Protocol.WithHash

/-!
# Random-oracle theorem tests

Statement locks for the random-oracle theorem of the compiled verifier and its parts: the
uniformity of the squeezed challenge, the proof-of-work fraction, the counts of failing answers,
the potential's step inequalities and final inequality, and `romSound` itself.

Then the theorem end to end on a tiny verifier program: read one scalar `x`, sample one
challenge `c`, accept iff `c = x`. Its doom certificate (`toyCert`) is "the history is empty or
is one scalar": a group escapes it only if the challenge hits the scalar, with probability
`1/|E|`. The seeding (a family of one statement, `toySeeds`) hashes fixed bytes, then permutes
the digest into the sponge's first state; the compiled verifier makes three queries on every
proof (`toy_queryBound`): the hash, the seed's permutation and the squeeze, the scalar waiting in
the sponge. Every accepted proof has a doomed boundary prefix (the empty history), so `romSound`
bounds the acceptance probability of every adversary with `Q_A` queries by
`(Q_A + 3) · (2^-128 + 5 (Q_A + 3) / 2^256)` (`toy_accept_le`), instantiated also at a concrete
adversary. Negative checks: the trivial doom predicate is not a certificate (the verdict refutes
doom: `Cert.final` is load-bearing); a 70-bit proof of work passes on a zero lane, which is
why the discount is `2^-min(b, 64)` and not `2^-b`; extraction from no answers gives zero
rows.
-/

namespace LeanVMTests.Protocol.Compile.RomSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Rom LeanVM.Protocol.Compile.Rom LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## Statement locks -/

example (f : E → ℝ≥0∞) :
    (∑ u : KeccakState, f (challengeOf u)) / Fintype.card KeccakState = (∑ c : E, f c) / Fintype.card E :=
  sum_challengeOf_div f

example (b : ℕ) :
    (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = true)) / Fintype.card KeccakState ≤
      2⁻¹ ^ min b 64 :=
  sum_powOk_div_le b

example : Fintype.card Digest = 2 ^ 256 := card_digest

example : Fintype.card KeccakState = 2 ^ 1600 := card_kstate

example {X : Type} (σ : Seeds X) (ℓ : Log) (x : Bytes) :
    ∑ u, ind (BadH σ ℓ x u) ≤ ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) :=
  sum_badH_le σ ℓ x

example (ℓ : Log) (s : KeccakState) :
    (∑ u, ind (BadF ℓ s u)) / Fintype.card KeccakState ≤
      ((2 * ℓ.length + 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 256 :=
  sum_badF_div_le ℓ s

example {X : Type} {P : VerifierProgram Bool} (D : List Ev → Prop) (σ : Seeds X) (ℓ : Log) (x :
    Bytes) :
    (∑ u, pot D σ P (ℓ ++ [.inl (x, u)])) / Fintype.card Digest ≤
      pot D σ P ℓ + ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) / 2 ^ 256 :=
  step_ineqH D ℓ x

example {X : Type} {P : VerifierProgram Bool} (C : Cert P) (σ : Seeds X) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) (ℓ : Log) (t : KeccakState)
    (ht : lookF ℓ t = none) :
    (∑ u, pot C.D σ P (ℓ ++ [.inr (t, u)])) / Fintype.card KeccakState ≤
      pot C.D σ P ℓ + (εmax + ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) / 2 ^ 256) :=
  step_ineqF C hε ℓ t ht

example {X : Type} {P : VerifierProgram Bool} (C : Cert P) (σ : Seeds X) : pot C.D σ P [] = 0 :=
  pot_nil C.D σ P

example {X : Type} {P : VerifierProgram Bool} (C : Cert P) {σ : Seeds X} {ℓ : Log} (hf : ¬ Fail σ ℓ)
    (hε1 : ∀ h, grindBits h = 0 → C.ε h < 1) {x : X} {π : Proof} (hroot : RootOk P (σ.root x))
    (hv : verify (lookH ℓ) (lookF ℓ) (σ.seed x) (nodeAt P (σ.root x)) π = some true)
    (hbad : ∃ h₀, h₀ <+: extractedFrom (lookH ℓ) (lookF ℓ) (σ.seed x) (nodeAt P (σ.root x))
      (σ.root x) π ∧ (σ.root x).length ≤ h₀.length ∧ Boundary h₀ ∧ C.D h₀) :
    1 ≤ pot C.D σ P ℓ :=
  final_ineq C hf hε1 hroot hv hbad

example {X : Type} (P : VerifierProgram Bool) (C : Cert P) (σ : Seeds X)
    (hroot : ∀ x, RootOk P (σ.root x)) (εmax : ℝ≥0∞)
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax)
    (A : OracleComp KeccakCalls (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV) :
    Pr{let z ← romExperiment A (verifierFam σ P)}[z.1.2 = true ∧ Doomed C σ z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εmax + ((5 + σ.offs.length) * (QA + QV) : ℕ) / 2 ^ 256) :=
  romSound P C σ hroot εmax hε A QA hA QV hV

/-! ## A tiny program and its certificate -/

/-- Read a scalar `x`, sample a challenge `c`, accept iff `c = x`. -/
def toyProg : VerifierProgram Bool := .read fun x ↦ .sample fun c ↦ .ret (decide (c = x))

/-- Doom: the history is empty or is one scalar (the challenge is still to come). -/
def toyD (h : List Ev) : Prop := h = [] ∨ ∃ x, h = [Ev.read x]

theorem toy_after_nil : toyProg.after [] = some toyProg := by simp [VerifierProgram.after]

theorem toy_after_read (x : E) :
    toyProg.after [Ev.read x] = some (.sample fun c ↦ .ret (decide (c = x))) := by
  simp [toyProg, VerifierProgram.after]

theorem toy_after_of_toyD {h : List Ev} {p : VerifierProgram Bool} (hD : toyD h)
    (ha : toyProg.after h = some p) :
    p = toyProg ∨ ∃ x, p = .sample fun c ↦ .ret (decide (c = x)) := by
  rcases hD with rfl | ⟨x, rfl⟩
  · rw [toy_after_nil] at ha
    exact Or.inl (Option.some.inj ha).symm
  · rw [toy_after_read] at ha
    exact Or.inr ⟨x, (Option.some.inj ha).symm⟩

theorem toy_esc (x : E) :
    esc toyD [Ev.read x] (.sample fun c ↦ .ret (decide (c = x))) =
      (Fintype.card E : ℝ≥0∞)⁻¹ := by
  rw [esc_sample]
  have hpt : ∀ c : E, esc toyD ([Ev.read x] ++ [Ev.sample c]) (.ret (decide (c = x))) =
      if c = x then 1 else 0 := by
    intro c
    have hD : ¬ toyD [Ev.read x, Ev.sample c] := by
      rintro (h | ⟨y, h⟩) <;> simp at h
    by_cases hc : c = x
    · subst hc
      simp [esc, hD]
    · simp [hc, esc]
  simp only [hpt, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]

/-- The doom certificate of the tiny program: a group escapes only if the challenge hits the
scalar. -/
noncomputable def toyCert : Cert toyProg where
  D := toyD
  ε := fun _ ↦ (Fintype.card E : ℝ≥0∞)⁻¹
  read := by
    intro h k x _ ha hD
    rcases hD with rfl | ⟨y, rfl⟩
    · exact Or.inr ⟨x, rfl⟩
    · rw [toy_after_read] at ha; cases ha
  grind := by
    intro h b k _ ha hD
    rcases toy_after_of_toyD hD ha with h1 | ⟨x, h1⟩ <;> cases h1
  commit := by
    intro h ht w k word _ ha _ hD
    rcases toy_after_of_toyD hD ha with h1 | ⟨x, h1⟩ <;> cases h1
  group := by
    intro h p _ _ ha hp hD
    rcases hD with rfl | ⟨x, rfl⟩
    · rw [toy_after_nil] at ha
      cases ha
      rcases hp with ⟨k, hk⟩ | ⟨i, ps, k, hk⟩ <;> cases hk
    · rw [toy_after_read] at ha
      cases ha
      exact le_of_eq (toy_esc x)
  final := by
    intro h _ ha hD
    rcases toy_after_of_toyD hD ha with h1 | ⟨x, h1⟩ <;> cases h1

/-- The trivial doom predicate is not a certificate: the accepting verdict refutes doom. -/
theorem not_cert_of_always_doomed : ¬ ∃ C : Cert toyProg, ∀ h, C.D h := by
  rintro ⟨C, hC⟩
  have hr1 : toyProg.Reachable [Ev.read 0] := by
    simpa using VerifierProgram.Reachable.read (P := toyProg) 0 VerifierProgram.Reachable.nil
        toy_after_nil
  have hr2 : toyProg.Reachable [Ev.read 0, Ev.sample 0] := by
    simpa using VerifierProgram.Reachable.sample (P := toyProg) 0 hr1 (toy_after_read 0)
  have ha : toyProg.after [Ev.read 0, Ev.sample 0] = some (.ret true) := by
    simp [toyProg, VerifierProgram.after]
  exact C.final hr2 ha (hC _)

/-! ## The compiled toy verifier -/

/-- The seeding: one hash of fixed bytes, then the permutation of the digest. -/
def toySeed : Seed := ⟨[fun _ ↦ [0x6c, 0x65, 0x61, 0x6e]], fun ds ↦ seedInput (ds.getD 0 default) default⟩

/-- The seedings of one statement, rooted at the empty history. -/
def toySeeds : Seeds Unit where
  seed _ := toySeed
  root _ := []
  offs := []
  refs _ ds hl i hi := by
    left
    have h1 : ds.length = 1 := hl
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [toySeed, laneDigest_seedInput]
    rw [List.getD_eq_getElem _ _ (by omega)]
  cap0 _ ds := capOf_seedInput _ _
  inj _ _ x x' _ _ _ _ _ := rfl

theorem toy_rootOk : RootOk toyProg [] :=
  ⟨VerifierProgram.Reachable.nil, trivial, rfl, rfl, by simp [VerifierProgram.after]⟩

theorem nodeAt_toy : nodeAt toyProg [] = toyProg := rfl

/-- The toy program's cost: a read and a sample, `1 + 4` quarters. -/
theorem toy_cost : toyProg.CostLE 0 5 := ⟨by norm_num, fun _ ↦ ⟨le_rfl, fun _ ↦ trivial⟩⟩

/-- The compiled toy verifier makes at most three queries on every proof. -/
theorem toy_queryBound (z : Unit × Proof) :
    IsTotalQueryBound (verifierFam toySeeds toyProg z) 3 :=
  isTotalQueryBound_verifierComp toy_cost toySeed z.2

theorem toy_eps (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * toyCert.ε h ≤ (Fintype.card E : ℝ≥0∞)⁻¹ := by
  show (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (Fintype.card E : ℝ≥0∞)⁻¹ ≤ _
  calc (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (Fintype.card E : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card E : ℝ≥0∞)⁻¹ := by
        gcongr
        exact pow_le_one₀ bot_le (ENNReal.inv_le_one.mpr (by norm_num))
    _ = _ := one_mul _

/-- Every proof of the toy verifier is doomed: the empty history is a doomed boundary. -/
theorem toy_doomed (z : Unit × Proof) (c : KeccakCalls.QueryCache) : Doomed toyCert toySeeds z c :=
  ⟨[], List.nil_prefix, le_rfl, trivial, Or.inl rfl⟩

/-- **The random-oracle theorem on the toy program.** Every adversary with at most `QA` queries
makes the compiled toy verifier accept with probability at most
`(QA + 3) · (2^-128 + 5 (QA + 3) / 2^256)`. -/
theorem toy_accept_le (A : OracleComp KeccakCalls (Unit × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam toySeeds toyProg)}[z.1.2 = true] ≤
      (QA + 3 : ℕ) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + failBound toySeeds (QA + 3)) := by
  have h := romSound toyProg toyCert toySeeds (fun _ ↦ toy_rootOk) _ toy_eps A QA hA 3
    toy_queryBound
  simp only [toy_doomed, and_true, card_E, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- A concrete adversary: one fixed proof, no queries. -/
def toyAdv : OracleComp KeccakCalls (Unit × Proof) := pure ((), ⟨[0], []⟩)

/-- The theorem at the concrete adversary. -/
example : Pr{let z ← romExperiment toyAdv (verifierFam toySeeds toyProg)}[z.1.2 = true] ≤
    (0 + 3 : ℕ) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + failBound toySeeds (0 + 3)) :=
  toy_accept_le _ 0 trivial

/-! ## Negative checks -/

/-- A 70-bit proof of work passes on a zero lane: the predicate tests one 64-bit lane, so for
`b > 64` its success fraction is `2^-64`, and the discount is `2^-min(b, 64)`. -/
example : powOk 70 0 = true := by decide

/-- Extraction from no answers gives the zero row of the width. -/
example (r : Digest) (ht w p : ℕ) : extract (lookH []) r ht w p = List.replicate w 0 := by
  have : ¬ ∃ o : Opening, openOneWithHash (m := Option) (lookH []) r ht w p o = some true := by
    rintro ⟨o, ho⟩
    obtain ⟨-, -, ld, hld, -⟩ := (openOne_eq_some_true_iff _ _ _ _ _ _).mp ho
    simp at hld
  simp [extract, pickLeaf, this]

end LeanVMTests.Protocol.Compile.RomSound
