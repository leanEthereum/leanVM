module

public import Common.QueryCost
public import Statement.HashSignatures

@[expose] public section

/-!
# Worst-case permutation calls of the hash-based combinators

Bounds on every path (`QueryCostAtMost`) of the shared combinators of `Statement/HashSignatures.lean`
(`sequenceFin`, `walkChain`, `foldPath`, `buildTree`) from bounds on their steps, and the cost of a
Keccak-256 hash over `π` in permutation calls: `⌊n / 136⌋ + 1` for `n` bytes. The schemes' key
generation, signer and verifier are bounded with them (`Common.XmssCost`, `Common.SphincsCost`).
-/

open OracleComp OracleSpec

namespace Common

section Combinators

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℕ}

theorem sequenceFin_cost {α : Type} (b : ℕ) :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α), (∀ i, QueryCostAtMost (c i) w b) →
      QueryCostAtMost (HashSig.OverPermutation.sequenceFin c) w (n * b)
  | 0, c, _ => by
    simp only [HashSig.OverPermutation.sequenceFin]
    exact isWeightBound_pure _ _ _
  | n + 1, c, h => by
    simp only [HashSig.OverPermutation.sequenceFin]
    refine ((h 0).bind fun _ ↦ (sequenceFin_cost b (fun i : Fin n ↦ c i.succ)
      (fun i ↦ h i.succ)).bind fun _ ↦ isWeightBound_pure _ w 0).mono ?_
    rw [Nat.succ_mul]
    omega

theorem walkChain_cost {S : ℕ} (step : Fin S → HashSig.Digest → OracleComp spec HashSig.Digest)
    (b : ℕ) (h : ∀ t v, QueryCostAtMost (step t v) w b) :
    ∀ start steps v, QueryCostAtMost (HashSig.OverPermutation.walkChain step start steps v) w (steps * b)
  | _, 0, v => by
    simp only [HashSig.OverPermutation.walkChain]
    exact isWeightBound_pure _ _ _
  | start, steps + 1, v => by
    simp only [HashSig.OverPermutation.walkChain]
    refine ((walkChain_cost step b h start steps v).bind fun prev ↦ ?_).mono
      (Q := steps * b + b) (by rw [Nat.succ_mul])
    split
    · exact h _ _
    · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

theorem foldPath_cost (node : ℕ → ℕ → HashSig.HashInput → OracleComp spec HashSig.Digest)
    (b : ℕ) (h : ∀ l j left right, QueryCostAtMost (node l j (HashSig.OverPermutation.nodePayload left right)) w b)
    (leafIndex : ℕ) (sibling : ℕ → HashSig.Digest) :
    ∀ levels v, QueryCostAtMost (HashSig.OverPermutation.foldPath node leafIndex sibling levels v) w (levels * b)
  | 0, v => by
    simp only [HashSig.OverPermutation.foldPath]
    exact isWeightBound_pure _ _ _
  | l + 1, v => by
    simp only [HashSig.OverPermutation.foldPath]
    refine ((foldPath_cost node b h leafIndex sibling l v).bind fun _ ↦ ?_).mono
      (by rw [Nat.succ_mul])
    split
    · exact h _ _ _ _
    · exact h _ _ _ _

theorem buildTree_cost (leaf : ℕ → OracleComp spec HashSig.Digest)
    (node : ℕ → ℕ → HashSig.HashInput → OracleComp spec HashSig.Digest) (a b : ℕ)
    (hl : ∀ i, QueryCostAtMost (leaf i) w a)
    (hn : ∀ l j left right, QueryCostAtMost (node l j (HashSig.OverPermutation.nodePayload left right)) w b) :
    ∀ l j, QueryCostAtMost (HashSig.OverPermutation.buildTree leaf node l j) w (2 ^ l * a + (2 ^ l - 1) * b)
  | 0, j => by
    simp only [HashSig.OverPermutation.buildTree]
    simpa using hl j
  | l + 1, j => by
    simp only [HashSig.OverPermutation.buildTree]
    refine ((buildTree_cost leaf node a b hl hn l (2 * j)).bind fun _ ↦
      (buildTree_cost leaf node a b hl hn l (2 * j + 1)).bind fun _ ↦ hn l j _ _).mono ?_
    have hp : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    rw [pow_succ]
    have e1 : (2 ^ l * 2 - 1) * b = (2 ^ l - 1) * b + (2 ^ l - 1) * b + b := by
      rw [← Nat.add_mul, ← Nat.succ_mul]
      congr 1
      omega
    rw [e1]
    ring_nf
    omega

/-- Weight bounds add along a bind whose continuation is bounded on the support. -/
theorem QueryCostAtMost.bind_of_support {α β : Type} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {a b : ℕ} (ha : QueryCostAtMost oa w a)
    (hb : ∀ x ∈ support oa, QueryCostAtMost (ob x) w b) : QueryCostAtMost (oa >>= ob) w (a + b) := by
  induction oa using OracleComp.inductionOn generalizing a with
  | pure x =>
    simpa using (hb x (by simp)).mono (Nat.le_add_left b a)
  | query_bind t k ih =>
    rw [bind_assoc, isWeightBound_query_bind_iff]
    rw [isWeightBound_query_bind_iff] at ha
    refine ⟨ha.1.trans (Nat.le_add_right _ _), fun u ↦ ?_⟩
    refine (ih u (ha.2 u) fun x hx ↦ hb x ?_).mono (by omega)
    simp only [mem_support_bind_iff]
    exact ⟨u, by simp, hx⟩

/-- `mapM` makes the calls of its steps. -/
theorem mapM_cost {α β : Type} (f : α → OracleComp spec β) (b : ℕ) (h : ∀ x, QueryCostAtMost (f x) w b) :
    ∀ l : List α, QueryCostAtMost (l.mapM f) w (l.length * b)
  | [] => by
    rw [List.mapM_nil]
    exact isWeightBound_pure _ _ _
  | x :: l => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (h x).bind fun _ ↦ ((mapM_cost f b h l).bind fun _ ↦ isWeightBound_pure _ w 0).mono le_rfl

end Combinators

section Hash

open LeanVM.Protocol

/-- The statement's Keccak state, `25` lanes. -/
local notation "LState" => LeanVM.Semantics.KeccakState

/-- Absorbing `n + 1` blocks over `π`, then `g`: within `Q' + (n + 1)` permutation calls when `g`
is within `Q'` from every state. -/
theorem isWeightBound_absorbWith {β : Type} {g : LState → OracleComp RandomPermutationOracles β} {Q' : ℕ}
    (hg : ∀ s, QueryCostAtMost (g s) permutationCallCost Q') :
    ∀ (n : ℕ) (s : LState) (d : List UInt8),
      QueryCostAtMost (KeccakHash.absorbWith queryPermutation n s d >>= g) permutationCallCost (Q' + (n + 1))
  | 0, s, d => by
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= g) permutationCallCost (Q' + 1)
    rw [isWeightBound_query_bind_iff]
    exact ⟨by simp [permutationCallCost], fun u ↦ by simpa [permutationCallCost] using hg u⟩
  | n + 1, s, d => by
    simp only [KeccakHash.absorbWith, bind_assoc]
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= fun s' ↦
      KeccakHash.absorbWith queryPermutation n s' _ >>= g) permutationCallCost (Q' + (n + 1 + 1))
    rw [isWeightBound_query_bind_iff]
    refine ⟨by simp only [permutationCallCost]; omega, fun u ↦ ?_⟩
    have h := isWeightBound_absorbWith hg n u (d.drop KeccakHash.rate)
    simpa [permutationCallCost, show Q' + (n + 1 + 1) - 1 = Q' + (n + 1) by omega] using h

/-- Absorbing `n + 1` blocks over `π`, then `g`, within `Q` permutation calls: `n + 1 ≤ Q`, and
`g` is within the rest from every state (the last call of `π` can answer any). -/
theorem isWeightBound_absorbWith_inv {β : Type} {g : LState → OracleComp RandomPermutationOracles β} :
    ∀ (n : ℕ) (s : LState) (d : List UInt8) (Q : ℕ),
      QueryCostAtMost (KeccakHash.absorbWith queryPermutation n s d >>= g) permutationCallCost Q →
        n + 1 ≤ Q ∧ ∀ s', QueryCostAtMost (g s') permutationCallCost (Q - (n + 1))
  | 0, s, d, Q, h => by
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= g) permutationCallCost Q at h
    rw [isWeightBound_query_bind_iff] at h
    exact ⟨by simpa [permutationCallCost] using h.1, fun s' ↦ by simpa [permutationCallCost] using h.2 s'⟩
  | n + 1, s, d, Q, h => by
    simp only [KeccakHash.absorbWith, bind_assoc] at h
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= fun s' ↦
      KeccakHash.absorbWith queryPermutation n s' _ >>= g) permutationCallCost Q at h
    rw [isWeightBound_query_bind_iff] at h
    obtain ⟨h1, h2⟩ := isWeightBound_absorbWith_inv n s (d.drop KeccakHash.rate) _ (h.2 s)
    refine ⟨by simp [permutationCallCost] at h1; omega, fun s' ↦ ?_⟩
    have := h2 s'
    simpa [permutationCallCost, show Q - 1 - (n + 1) = Q - (n + 1 + 1) by omega] using this

/-- **Keccak-256 over `π` of `n` bytes makes `⌊n / 136⌋ + 1` permutation calls.** -/
theorem keccak256With_cost (d : List UInt8) :
    QueryCostAtMost (KeccakHash.keccak256With queryPermutation d) permutationCallCost
      (d.length / 136 + 1) := by
  have h := isWeightBound_absorbWith (g := fun state ↦
      (pure #v[LeanVM.Semantics.Keccak.lane state 0, LeanVM.Semantics.Keccak.lane state 1,
        LeanVM.Semantics.Keccak.lane state 2, LeanVM.Semantics.Keccak.lane state 3] :
        OracleComp RandomPermutationOracles _))
    (fun _ ↦ isWeightBound_pure _ _ 0) (d.length / KeccakHash.rate) (Vector.replicate 25 0) d
  simpa [KeccakHash.keccak256With, KeccakHash.rate] using h

/-- **The hash `H` of `n` bytes makes `⌊n / 136⌋ + 1` permutation calls.** -/
theorem keccakHash_cost (d : HashSig.HashInput) :
    QueryCostAtMost (HashSig.OverPermutation.keccakHash queryPermutation d) permutationCallCost
      (d.length / 136 + 1) :=
  isWeightBound_map _ (keccak256With_cost d)

/-- The hash of at most `136 · k + 135` bytes makes at most `k + 1` permutation calls. -/
theorem keccakHash_cost_le (d : HashSig.HashInput) {k : ℕ} (h : d.length < 136 * (k + 1)) :
    QueryCostAtMost (HashSig.OverPermutation.keccakHash queryPermutation d) permutationCallCost
      (k + 1) :=
  (keccakHash_cost d).mono (by
    have : d.length / 136 < k + 1 := Nat.div_lt_of_lt_mul (by omega)
    omega)

end Hash

end Common
